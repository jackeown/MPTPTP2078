%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 802 expanded)
%              Number of leaves         :    6 ( 138 expanded)
%              Depth                    :   40
%              Number of atoms          :  445 (4795 expanded)
%              Number of equality atoms :   51 ( 563 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f307,plain,(
    $false ),
    inference(subsumption_resolution,[],[f306,f261])).

fof(f261,plain,(
    ~ r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f151,f260])).

fof(f260,plain,(
    sK1 = k11_lattice3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f259,f149])).

fof(f149,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | sK1 = k11_lattice3(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f66,f144])).

fof(f144,plain,(
    k12_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK1,sK2) ),
    inference(resolution,[],[f74,f22])).

fof(f22,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <~> r3_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <~> r3_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k12_lattice3(X0,X1,X2) = X1
                <=> r3_orders_2(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_0)).

fof(f74,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k11_lattice3(sK0,sK1,X1) = k12_lattice3(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f73,f25])).

fof(f25,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X1] :
      ( ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k11_lattice3(sK0,sK1,X1) = k12_lattice3(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f72,f27])).

fof(f27,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X1] :
      ( ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k11_lattice3(sK0,sK1,X1) = k12_lattice3(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f68,f26])).

fof(f26,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X1] :
      ( ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k11_lattice3(sK0,sK1,X1) = k12_lattice3(sK0,sK1,X1) ) ),
    inference(resolution,[],[f39,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f66,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | sK1 = k12_lattice3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f65,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f50,f27])).

fof(f50,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_struct_0(sK0) ),
    inference(resolution,[],[f28,f26])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f65,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | sK1 = k12_lattice3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f64,f22])).

fof(f64,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | sK1 = k12_lattice3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f63,f23])).

fof(f63,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | sK1 = k12_lattice3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f62,f27])).

fof(f62,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | sK1 = k12_lattice3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f61,f24])).

fof(f24,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | sK1 = k12_lattice3(sK0,sK1,sK2) ),
    inference(resolution,[],[f38,f20])).

fof(f20,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | sK1 = k12_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
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

fof(f259,plain,
    ( sK1 = k11_lattice3(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f258,f25])).

fof(f258,plain,
    ( sK1 = k11_lattice3(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f257,f60])).

fof(f60,plain,(
    r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f59,f51])).

fof(f59,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f58,f27])).

fof(f58,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f54,f24])).

fof(f54,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK1) ),
    inference(resolution,[],[f36,f23])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r1_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f257,plain,
    ( sK1 = k11_lattice3(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f256,f22])).

fof(f256,plain,
    ( sK1 = k11_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f255,f23])).

fof(f255,plain,
    ( sK1 = k11_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f254,f27])).

fof(f254,plain,
    ( sK1 = k11_lattice3(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f253,f26])).

fof(f253,plain,
    ( sK1 = k11_lattice3(sK0,sK1,sK2)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ v5_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f248])).

fof(f248,plain,
    ( sK1 = k11_lattice3(sK0,sK1,sK2)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ v5_orders_2(sK0)
    | sK1 = k11_lattice3(sK0,sK1,sK2) ),
    inference(resolution,[],[f187,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f32,f28])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(f187,plain,
    ( r1_orders_2(sK0,sK3(sK0,sK1,sK2,sK1),sK1)
    | sK1 = k11_lattice3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f185,f22])).

fof(f185,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(sK0,sK1,sK2,sK1),sK1)
    | sK1 = k11_lattice3(sK0,sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(sK0,sK1,sK2,sK1),sK1)
    | sK1 = k11_lattice3(sK0,sK1,sK2)
    | sK1 = k11_lattice3(sK0,sK1,sK2) ),
    inference(resolution,[],[f114,f149])).

fof(f114,plain,(
    ! [X1] :
      ( ~ r1_orders_2(sK0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,sK3(sK0,sK1,X1,sK1),sK1)
      | sK1 = k11_lattice3(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f113,f25])).

fof(f113,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ r1_orders_2(sK0,sK1,X1)
      | r1_orders_2(sK0,sK3(sK0,sK1,X1,sK1),sK1)
      | sK1 = k11_lattice3(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f112,f23])).

fof(f112,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ r1_orders_2(sK0,sK1,X1)
      | r1_orders_2(sK0,sK3(sK0,sK1,X1,sK1),sK1)
      | sK1 = k11_lattice3(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f111,f27])).

fof(f111,plain,(
    ! [X1] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ r1_orders_2(sK0,sK1,X1)
      | r1_orders_2(sK0,sK3(sK0,sK1,X1,sK1),sK1)
      | sK1 = k11_lattice3(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f105,f26])).

fof(f105,plain,(
    ! [X1] :
      ( ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ r1_orders_2(sK0,sK1,X1)
      | r1_orders_2(sK0,sK3(sK0,sK1,X1,sK1),sK1)
      | sK1 = k11_lattice3(sK0,sK1,X1) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X1] :
      ( ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ r1_orders_2(sK0,sK1,X1)
      | r1_orders_2(sK0,sK3(sK0,sK1,X1,sK1),sK1)
      | sK1 = k11_lattice3(sK0,sK1,X1) ) ),
    inference(resolution,[],[f60,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,X1)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X3,X2)
      | r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f30,f28])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f151,plain,
    ( ~ r3_orders_2(sK0,sK1,sK2)
    | sK1 != k11_lattice3(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f21,f144])).

fof(f21,plain,
    ( ~ r3_orders_2(sK0,sK1,sK2)
    | sK1 != k12_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f306,plain,(
    r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f305,f51])).

fof(f305,plain,
    ( v2_struct_0(sK0)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f304,f22])).

fof(f304,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f303,f23])).

fof(f303,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f302,f27])).

fof(f302,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f286,f24])).

fof(f286,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f279,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f279,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f278,f25])).

fof(f278,plain,
    ( ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f277,f22])).

fof(f277,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f276,f27])).

fof(f276,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f275,f26])).

fof(f275,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f272,f23])).

fof(f272,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f271])).

fof(f271,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(superposition,[],[f43,f260])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) ) ),
    inference(subsumption_resolution,[],[f40,f28])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:44:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (23768)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.42  % (23768)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f307,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(subsumption_resolution,[],[f306,f261])).
% 0.20/0.42  fof(f261,plain,(
% 0.20/0.42    ~r3_orders_2(sK0,sK1,sK2)),
% 0.20/0.42    inference(subsumption_resolution,[],[f151,f260])).
% 0.20/0.42  fof(f260,plain,(
% 0.20/0.42    sK1 = k11_lattice3(sK0,sK1,sK2)),
% 0.20/0.42    inference(subsumption_resolution,[],[f259,f149])).
% 0.20/0.42  fof(f149,plain,(
% 0.20/0.42    r1_orders_2(sK0,sK1,sK2) | sK1 = k11_lattice3(sK0,sK1,sK2)),
% 0.20/0.42    inference(backward_demodulation,[],[f66,f144])).
% 0.20/0.42  fof(f144,plain,(
% 0.20/0.42    k12_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK1,sK2)),
% 0.20/0.42    inference(resolution,[],[f74,f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (? [X2] : ((k12_lattice3(X0,X1,X2) = X1 <~> r3_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 0.20/0.42    inference(flattening,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (? [X2] : ((k12_lattice3(X0,X1,X2) = X1 <~> r3_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,negated_conjecture,(
% 0.20/0.42    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 0.20/0.42    inference(negated_conjecture,[],[f6])).
% 0.20/0.42  fof(f6,conjecture,(
% 0.20/0.42    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_0)).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k11_lattice3(sK0,sK1,X1) = k12_lattice3(sK0,sK1,X1)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f73,f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    v5_orders_2(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    ( ! [X1] : (~v5_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k11_lattice3(sK0,sK1,X1) = k12_lattice3(sK0,sK1,X1)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f72,f27])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    l1_orders_2(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f72,plain,(
% 0.20/0.42    ( ! [X1] : (~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k11_lattice3(sK0,sK1,X1) = k12_lattice3(sK0,sK1,X1)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f68,f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    v2_lattice3(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    ( ! [X1] : (~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k11_lattice3(sK0,sK1,X1) = k12_lattice3(sK0,sK1,X1)) )),
% 0.20/0.42    inference(resolution,[],[f39,f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.42    inference(flattening,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    r1_orders_2(sK0,sK1,sK2) | sK1 = k12_lattice3(sK0,sK1,sK2)),
% 0.20/0.42    inference(subsumption_resolution,[],[f65,f51])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    ~v2_struct_0(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f50,f27])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    ~l1_orders_2(sK0) | ~v2_struct_0(sK0)),
% 0.20/0.42    inference(resolution,[],[f28,f26])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X0] : (~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v2_struct_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 0.20/0.42    inference(flattening,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    r1_orders_2(sK0,sK1,sK2) | v2_struct_0(sK0) | sK1 = k12_lattice3(sK0,sK1,sK2)),
% 0.20/0.42    inference(subsumption_resolution,[],[f64,f22])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK2) | v2_struct_0(sK0) | sK1 = k12_lattice3(sK0,sK1,sK2)),
% 0.20/0.42    inference(subsumption_resolution,[],[f63,f23])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK2) | v2_struct_0(sK0) | sK1 = k12_lattice3(sK0,sK1,sK2)),
% 0.20/0.42    inference(subsumption_resolution,[],[f62,f27])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK2) | v2_struct_0(sK0) | sK1 = k12_lattice3(sK0,sK1,sK2)),
% 0.20/0.42    inference(subsumption_resolution,[],[f61,f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    v3_orders_2(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK2) | v2_struct_0(sK0) | sK1 = k12_lattice3(sK0,sK1,sK2)),
% 0.20/0.42    inference(resolution,[],[f38,f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    r3_orders_2(sK0,sK1,sK2) | sK1 = k12_lattice3(sK0,sK1,sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.42    inference(flattening,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.20/0.42  fof(f259,plain,(
% 0.20/0.42    sK1 = k11_lattice3(sK0,sK1,sK2) | ~r1_orders_2(sK0,sK1,sK2)),
% 0.20/0.42    inference(subsumption_resolution,[],[f258,f25])).
% 0.20/0.42  fof(f258,plain,(
% 0.20/0.42    sK1 = k11_lattice3(sK0,sK1,sK2) | ~r1_orders_2(sK0,sK1,sK2) | ~v5_orders_2(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f257,f60])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    r1_orders_2(sK0,sK1,sK1)),
% 0.20/0.42    inference(subsumption_resolution,[],[f59,f51])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    v2_struct_0(sK0) | r1_orders_2(sK0,sK1,sK1)),
% 0.20/0.42    inference(subsumption_resolution,[],[f58,f27])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    ~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_orders_2(sK0,sK1,sK1)),
% 0.20/0.42    inference(subsumption_resolution,[],[f54,f24])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_orders_2(sK0,sK1,sK1)),
% 0.20/0.42    inference(resolution,[],[f36,f23])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_orders_2(X0,X1,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.42    inference(flattening,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).
% 0.20/0.42  fof(f257,plain,(
% 0.20/0.42    sK1 = k11_lattice3(sK0,sK1,sK2) | ~r1_orders_2(sK0,sK1,sK1) | ~r1_orders_2(sK0,sK1,sK2) | ~v5_orders_2(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f256,f22])).
% 0.20/0.42  fof(f256,plain,(
% 0.20/0.42    sK1 = k11_lattice3(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK1) | ~r1_orders_2(sK0,sK1,sK2) | ~v5_orders_2(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f255,f23])).
% 0.20/0.42  fof(f255,plain,(
% 0.20/0.42    sK1 = k11_lattice3(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK1) | ~r1_orders_2(sK0,sK1,sK2) | ~v5_orders_2(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f254,f27])).
% 0.20/0.42  fof(f254,plain,(
% 0.20/0.42    sK1 = k11_lattice3(sK0,sK1,sK2) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK1) | ~r1_orders_2(sK0,sK1,sK2) | ~v5_orders_2(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f253,f26])).
% 0.20/0.42  fof(f253,plain,(
% 0.20/0.42    sK1 = k11_lattice3(sK0,sK1,sK2) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK1) | ~r1_orders_2(sK0,sK1,sK2) | ~v5_orders_2(sK0)),
% 0.20/0.42    inference(duplicate_literal_removal,[],[f248])).
% 0.20/0.42  fof(f248,plain,(
% 0.20/0.42    sK1 = k11_lattice3(sK0,sK1,sK2) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK1) | ~r1_orders_2(sK0,sK1,sK2) | ~v5_orders_2(sK0) | sK1 = k11_lattice3(sK0,sK1,sK2)),
% 0.20/0.42    inference(resolution,[],[f187,f46])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | ~v5_orders_2(X0) | k11_lattice3(X0,X1,X2) = X3) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f32,f28])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) | k11_lattice3(X0,X1,X2) = X3) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.42    inference(flattening,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).
% 0.20/0.42  fof(f187,plain,(
% 0.20/0.42    r1_orders_2(sK0,sK3(sK0,sK1,sK2,sK1),sK1) | sK1 = k11_lattice3(sK0,sK1,sK2)),
% 0.20/0.42    inference(subsumption_resolution,[],[f185,f22])).
% 0.20/0.42  fof(f185,plain,(
% 0.20/0.42    ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(sK0,sK1,sK2,sK1),sK1) | sK1 = k11_lattice3(sK0,sK1,sK2)),
% 0.20/0.42    inference(duplicate_literal_removal,[],[f184])).
% 0.20/0.42  fof(f184,plain,(
% 0.20/0.42    ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(sK0,sK1,sK2,sK1),sK1) | sK1 = k11_lattice3(sK0,sK1,sK2) | sK1 = k11_lattice3(sK0,sK1,sK2)),
% 0.20/0.42    inference(resolution,[],[f114,f149])).
% 0.20/0.42  fof(f114,plain,(
% 0.20/0.42    ( ! [X1] : (~r1_orders_2(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(sK0,sK1,X1,sK1),sK1) | sK1 = k11_lattice3(sK0,sK1,X1)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f113,f25])).
% 0.20/0.43  fof(f113,plain,(
% 0.20/0.43    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r1_orders_2(sK0,sK1,X1) | r1_orders_2(sK0,sK3(sK0,sK1,X1,sK1),sK1) | sK1 = k11_lattice3(sK0,sK1,X1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f112,f23])).
% 0.20/0.43  fof(f112,plain,(
% 0.20/0.43    ( ! [X1] : (~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r1_orders_2(sK0,sK1,X1) | r1_orders_2(sK0,sK3(sK0,sK1,X1,sK1),sK1) | sK1 = k11_lattice3(sK0,sK1,X1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f111,f27])).
% 0.20/0.43  fof(f111,plain,(
% 0.20/0.43    ( ! [X1] : (~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r1_orders_2(sK0,sK1,X1) | r1_orders_2(sK0,sK3(sK0,sK1,X1,sK1),sK1) | sK1 = k11_lattice3(sK0,sK1,X1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f105,f26])).
% 0.20/0.43  fof(f105,plain,(
% 0.20/0.43    ( ! [X1] : (~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r1_orders_2(sK0,sK1,X1) | r1_orders_2(sK0,sK3(sK0,sK1,X1,sK1),sK1) | sK1 = k11_lattice3(sK0,sK1,X1)) )),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f100])).
% 0.20/0.43  fof(f100,plain,(
% 0.20/0.43    ( ! [X1] : (~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r1_orders_2(sK0,sK1,X1) | r1_orders_2(sK0,sK3(sK0,sK1,X1,sK1),sK1) | sK1 = k11_lattice3(sK0,sK1,X1)) )),
% 0.20/0.43    inference(resolution,[],[f60,f48])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,X3,X1) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) | k11_lattice3(X0,X1,X2) = X3) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f30,f28])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) | k11_lattice3(X0,X1,X2) = X3) )),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f151,plain,(
% 0.20/0.43    ~r3_orders_2(sK0,sK1,sK2) | sK1 != k11_lattice3(sK0,sK1,sK2)),
% 0.20/0.43    inference(backward_demodulation,[],[f21,f144])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ~r3_orders_2(sK0,sK1,sK2) | sK1 != k12_lattice3(sK0,sK1,sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f306,plain,(
% 0.20/0.43    r3_orders_2(sK0,sK1,sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f305,f51])).
% 0.20/0.43  fof(f305,plain,(
% 0.20/0.43    v2_struct_0(sK0) | r3_orders_2(sK0,sK1,sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f304,f22])).
% 0.20/0.43  fof(f304,plain,(
% 0.20/0.43    ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_orders_2(sK0,sK1,sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f303,f23])).
% 0.20/0.43  fof(f303,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_orders_2(sK0,sK1,sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f302,f27])).
% 0.20/0.43  fof(f302,plain,(
% 0.20/0.43    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_orders_2(sK0,sK1,sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f286,f24])).
% 0.20/0.43  fof(f286,plain,(
% 0.20/0.43    ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_orders_2(sK0,sK1,sK2)),
% 0.20/0.43    inference(resolution,[],[f279,f37])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_orders_2(X0,X1,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f279,plain,(
% 0.20/0.43    r1_orders_2(sK0,sK1,sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f278,f25])).
% 0.20/0.43  fof(f278,plain,(
% 0.20/0.43    ~v5_orders_2(sK0) | r1_orders_2(sK0,sK1,sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f277,f22])).
% 0.20/0.43  fof(f277,plain,(
% 0.20/0.43    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | r1_orders_2(sK0,sK1,sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f276,f27])).
% 0.20/0.43  fof(f276,plain,(
% 0.20/0.43    ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | r1_orders_2(sK0,sK1,sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f275,f26])).
% 0.20/0.43  fof(f275,plain,(
% 0.20/0.43    ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | r1_orders_2(sK0,sK1,sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f272,f23])).
% 0.20/0.43  fof(f272,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | r1_orders_2(sK0,sK1,sK2)),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f271])).
% 0.20/0.43  fof(f271,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | r1_orders_2(sK0,sK1,sK2)),
% 0.20/0.43    inference(superposition,[],[f43,f260])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f40,f28])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)) )),
% 0.20/0.43    inference(equality_resolution,[],[f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X3,X2) | k11_lattice3(X0,X1,X2) != X3) )),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (23768)------------------------------
% 0.20/0.43  % (23768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (23768)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (23768)Memory used [KB]: 1791
% 0.20/0.43  % (23768)Time elapsed: 0.011 s
% 0.20/0.43  % (23768)------------------------------
% 0.20/0.43  % (23768)------------------------------
% 0.20/0.43  % (23750)Success in time 0.067 s
%------------------------------------------------------------------------------
