%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 255 expanded)
%              Number of leaves         :    8 (  46 expanded)
%              Depth                    :   27
%              Number of atoms          :  318 (1586 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(subsumption_resolution,[],[f161,f32])).

fof(f32,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_7)).

fof(f161,plain,(
    ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f160,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f160,plain,(
    ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f156,f32])).

fof(f156,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f155,f44])).

fof(f155,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f154,f122])).

fof(f122,plain,(
    ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(resolution,[],[f121,f24])).

fof(f24,plain,
    ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
    | ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f121,plain,(
    r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f120,f32])).

fof(f120,plain,
    ( r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f119,f28])).

fof(f28,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f119,plain,
    ( r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f118,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f53,f32])).

fof(f53,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_struct_0(sK0) ),
    inference(resolution,[],[f29,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f29,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f118,plain,
    ( r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f117,f31])).

fof(f31,plain,(
    v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f117,plain,(
    ! [X0] :
      ( ~ v3_lattice3(X0)
      | r1_orders_2(X0,k2_yellow_0(X0,sK2),k2_yellow_0(X0,sK1))
      | v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f116,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_0)).

fof(f116,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(X0,sK1)
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,k2_yellow_0(X0,sK2),k2_yellow_0(X0,sK1))
      | v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_lattice3(X0) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(X0,sK1)
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,k2_yellow_0(X0,sK2),k2_yellow_0(X0,sK1))
      | v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f78,f43])).

fof(f78,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(X0,sK2)
      | ~ r2_yellow_0(X0,sK1)
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,k2_yellow_0(X0,sK2),k2_yellow_0(X0,sK1)) ) ),
    inference(resolution,[],[f25,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_tarski(X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ r2_yellow_0(X0,X2)
      | r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow_0)).

fof(f25,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f154,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f153,f32])).

fof(f153,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f152,f26])).

fof(f26,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f152,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f145,f54])).

fof(f145,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(resolution,[],[f144,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f144,plain,(
    r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f140,f32])).

fof(f140,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f139,f44])).

fof(f139,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f135,f32])).

fof(f135,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f114,f44])).

fof(f114,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f113,f59])).

fof(f59,plain,(
    ! [X0] : r1_yellow_0(sK0,X0) ),
    inference(subsumption_resolution,[],[f58,f32])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | r1_yellow_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f57,f28])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | r1_yellow_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f55,f54])).

fof(f55,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | r1_yellow_0(sK0,X0) ) ),
    inference(resolution,[],[f31,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f113,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,sK1)
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f104,f32])).

fof(f104,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,sK1)
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(resolution,[],[f100,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X2,X3)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f100,plain,(
    r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f99,f32])).

fof(f99,plain,
    ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f96,f59])).

fof(f96,plain,(
    ! [X3] :
      ( ~ r1_yellow_0(X3,sK2)
      | r2_lattice3(X3,sK1,k1_yellow_0(X3,sK2))
      | ~ l1_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f95,f44])).

fof(f95,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k1_yellow_0(X3,sK2),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_lattice3(X3,sK1,k1_yellow_0(X3,sK2))
      | ~ r1_yellow_0(X3,sK2) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k1_yellow_0(X3,sK2),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_lattice3(X3,sK1,k1_yellow_0(X3,sK2))
      | ~ l1_orders_2(X3)
      | ~ m1_subset_1(k1_yellow_0(X3,sK2),u1_struct_0(X3))
      | ~ r1_yellow_0(X3,sK2) ) ),
    inference(resolution,[],[f79,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f79,plain,(
    ! [X2,X1] :
      ( ~ r2_lattice3(X1,sK2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | r2_lattice3(X1,sK1,X2) ) ),
    inference(resolution,[],[f25,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X3)
      | r2_lattice3(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r2_lattice3(X0,X2,X3)
                 => r2_lattice3(X0,X1,X3) )
                & ( r1_lattice3(X0,X2,X3)
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.46  % (381)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (373)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (381)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (377)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f165,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f161,f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    l1_orders_2(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0))),
% 0.22/0.47    inference(flattening,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & (l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,negated_conjecture,(
% 0.22/0.47    ~! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 0.22/0.47    inference(negated_conjecture,[],[f8])).
% 0.22/0.47  fof(f8,conjecture,(
% 0.22/0.47    ! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_7)).
% 0.22/0.47  fof(f161,plain,(
% 0.22/0.47    ~l1_orders_2(sK0)),
% 0.22/0.47    inference(resolution,[],[f160,f44])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~l1_orders_2(X0) | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 0.22/0.47  fof(f160,plain,(
% 0.22/0.47    ~m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.47    inference(subsumption_resolution,[],[f156,f32])).
% 0.22/0.47  fof(f156,plain,(
% 0.22/0.47    ~m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.22/0.47    inference(resolution,[],[f155,f44])).
% 0.22/0.47  fof(f155,plain,(
% 0.22/0.47    ~m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.47    inference(subsumption_resolution,[],[f154,f122])).
% 0.22/0.47  fof(f122,plain,(
% 0.22/0.47    ~r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.22/0.47    inference(resolution,[],[f121,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ~r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) | ~r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f121,plain,(
% 0.22/0.47    r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))),
% 0.22/0.47    inference(subsumption_resolution,[],[f120,f32])).
% 0.22/0.47  fof(f120,plain,(
% 0.22/0.47    r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) | ~l1_orders_2(sK0)),
% 0.22/0.47    inference(subsumption_resolution,[],[f119,f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    v5_orders_2(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f119,plain,(
% 0.22/0.47    r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0)),
% 0.22/0.47    inference(subsumption_resolution,[],[f118,f54])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ~v2_struct_0(sK0)),
% 0.22/0.47    inference(subsumption_resolution,[],[f53,f32])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ~l1_orders_2(sK0) | ~v2_struct_0(sK0)),
% 0.22/0.47    inference(resolution,[],[f29,f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0] : (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v2_struct_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.22/0.47    inference(flattening,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    v1_lattice3(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f118,plain,(
% 0.22/0.47    r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) | v2_struct_0(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0)),
% 0.22/0.47    inference(resolution,[],[f117,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    v3_lattice3(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f117,plain,(
% 0.22/0.47    ( ! [X0] : (~v3_lattice3(X0) | r1_orders_2(X0,k2_yellow_0(X0,sK2),k2_yellow_0(X0,sK1)) | v2_struct_0(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f116,f43])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v2_struct_0(X0) | ~v5_orders_2(X0) | ~v3_lattice3(X0) | ~l1_orders_2(X0) | r2_yellow_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)) | (~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_0)).
% 0.22/0.47  fof(f116,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_yellow_0(X0,sK1) | ~l1_orders_2(X0) | r1_orders_2(X0,k2_yellow_0(X0,sK2),k2_yellow_0(X0,sK1)) | v2_struct_0(X0) | ~v5_orders_2(X0) | ~v3_lattice3(X0)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f115])).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_yellow_0(X0,sK1) | ~l1_orders_2(X0) | r1_orders_2(X0,k2_yellow_0(X0,sK2),k2_yellow_0(X0,sK1)) | v2_struct_0(X0) | ~v5_orders_2(X0) | ~v3_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.47    inference(resolution,[],[f78,f43])).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_yellow_0(X0,sK2) | ~r2_yellow_0(X0,sK1) | ~l1_orders_2(X0) | r1_orders_2(X0,k2_yellow_0(X0,sK2),k2_yellow_0(X0,sK1))) )),
% 0.22/0.47    inference(resolution,[],[f25,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_tarski(X1,X2) | ~r2_yellow_0(X0,X1) | ~r2_yellow_0(X0,X2) | r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r2_yellow_0(X0,X2) | ~r2_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 0.22/0.47    inference(flattening,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | (~r2_yellow_0(X0,X2) | ~r2_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r2_yellow_0(X0,X2) & r2_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow_0)).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    r1_tarski(sK1,sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f154,plain,(
% 0.22/0.47    ~m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) | r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.22/0.47    inference(subsumption_resolution,[],[f153,f32])).
% 0.22/0.47  fof(f153,plain,(
% 0.22/0.47    ~l1_orders_2(sK0) | ~m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) | r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.22/0.47    inference(subsumption_resolution,[],[f152,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    v3_orders_2(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f152,plain,(
% 0.22/0.47    ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) | r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.22/0.47    inference(subsumption_resolution,[],[f145,f54])).
% 0.22/0.47  fof(f145,plain,(
% 0.22/0.47    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) | r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.22/0.47    inference(resolution,[],[f144,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | r3_orders_2(X0,X1,X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.22/0.47  fof(f144,plain,(
% 0.22/0.47    r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.22/0.47    inference(subsumption_resolution,[],[f140,f32])).
% 0.22/0.47  fof(f140,plain,(
% 0.22/0.47    r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) | ~l1_orders_2(sK0)),
% 0.22/0.47    inference(resolution,[],[f139,f44])).
% 0.22/0.47  fof(f139,plain,(
% 0.22/0.47    ~m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.22/0.47    inference(subsumption_resolution,[],[f135,f32])).
% 0.22/0.47  fof(f135,plain,(
% 0.22/0.47    ~m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) | ~l1_orders_2(sK0)),
% 0.22/0.47    inference(resolution,[],[f114,f44])).
% 0.22/0.47  fof(f114,plain,(
% 0.22/0.47    ~m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.22/0.47    inference(subsumption_resolution,[],[f113,f59])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    ( ! [X0] : (r1_yellow_0(sK0,X0)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f58,f32])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    ( ! [X0] : (~l1_orders_2(sK0) | r1_yellow_0(sK0,X0)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f57,f28])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    ( ! [X0] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | r1_yellow_0(sK0,X0)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f55,f54])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ( ! [X0] : (v2_struct_0(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | r1_yellow_0(sK0,X0)) )),
% 0.22/0.47    inference(resolution,[],[f31,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v2_struct_0(X0) | ~v5_orders_2(X0) | ~v3_lattice3(X0) | ~l1_orders_2(X0) | r1_yellow_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    ~m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) | ~r1_yellow_0(sK0,sK1) | ~m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.22/0.47    inference(subsumption_resolution,[],[f104,f32])).
% 0.22/0.47  fof(f104,plain,(
% 0.22/0.47    ~l1_orders_2(sK0) | ~m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) | ~r1_yellow_0(sK0,sK1) | ~m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.22/0.47    inference(resolution,[],[f100,f48])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ( ! [X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,k1_yellow_0(X0,X1),X3)) )),
% 0.22/0.47    inference(equality_resolution,[],[f39])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,X2,X3) | k1_yellow_0(X0,X1) != X2) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.47    inference(flattening,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 0.22/0.47  fof(f100,plain,(
% 0.22/0.47    r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2))),
% 0.22/0.47    inference(subsumption_resolution,[],[f99,f32])).
% 0.22/0.47  fof(f99,plain,(
% 0.22/0.47    r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2)) | ~l1_orders_2(sK0)),
% 0.22/0.47    inference(resolution,[],[f96,f59])).
% 0.22/0.47  fof(f96,plain,(
% 0.22/0.47    ( ! [X3] : (~r1_yellow_0(X3,sK2) | r2_lattice3(X3,sK1,k1_yellow_0(X3,sK2)) | ~l1_orders_2(X3)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f95,f44])).
% 0.22/0.47  fof(f95,plain,(
% 0.22/0.47    ( ! [X3] : (~m1_subset_1(k1_yellow_0(X3,sK2),u1_struct_0(X3)) | ~l1_orders_2(X3) | r2_lattice3(X3,sK1,k1_yellow_0(X3,sK2)) | ~r1_yellow_0(X3,sK2)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f92])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    ( ! [X3] : (~m1_subset_1(k1_yellow_0(X3,sK2),u1_struct_0(X3)) | ~l1_orders_2(X3) | r2_lattice3(X3,sK1,k1_yellow_0(X3,sK2)) | ~l1_orders_2(X3) | ~m1_subset_1(k1_yellow_0(X3,sK2),u1_struct_0(X3)) | ~r1_yellow_0(X3,sK2)) )),
% 0.22/0.47    inference(resolution,[],[f79,f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))) )),
% 0.22/0.47    inference(equality_resolution,[],[f40])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) != X2) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    ( ! [X2,X1] : (~r2_lattice3(X1,sK2,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | r2_lattice3(X1,sK1,X2)) )),
% 0.22/0.47    inference(resolution,[],[f25,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (381)------------------------------
% 0.22/0.47  % (381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (381)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (381)Memory used [KB]: 1663
% 0.22/0.47  % (381)Time elapsed: 0.008 s
% 0.22/0.47  % (381)------------------------------
% 0.22/0.47  % (381)------------------------------
% 0.22/0.47  % (367)Success in time 0.113 s
%------------------------------------------------------------------------------
