%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:42 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  110 (1262 expanded)
%              Number of leaves         :   14 ( 250 expanded)
%              Depth                    :   18
%              Number of atoms          :  478 (6224 expanded)
%              Number of equality atoms :   61 ( 765 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1136,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1135,f396])).

fof(f396,plain,(
    k2_lattices(sK0,k6_lattices(sK0),sK1) = k2_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1) ),
    inference(forward_demodulation,[],[f342,f193])).

fof(f193,plain,(
    sK1 = k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f46,f88,f49,f44,f90,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

fof(f90,plain,(
    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f46,f84,f59])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(f84,plain,(
    l2_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f49,f51])).

fof(f51,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f44,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).

fof(f49,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f88,plain,(
    v8_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f49,f47,f46,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f47,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f342,plain,(
    k2_lattices(sK0,k6_lattices(sK0),sK1) = k2_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f89,f49,f44,f97,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

fof(f97,plain,(
    m1_subset_1(k2_lattices(sK0,k6_lattices(sK0),sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f46,f83,f44,f90,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattices)).

fof(f83,plain,(
    l1_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f49,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f89,plain,(
    v9_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f49,f47,f46,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1135,plain,(
    k2_lattices(sK0,k6_lattices(sK0),sK1) != k2_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f89,f88,f49,f46,f44,f97,f1063,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) != X1
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

fof(f1063,plain,(
    ~ r1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f85,f46,f84,f44,f650,f97,f1052,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X2,X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).

fof(f1052,plain,(
    r1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1)) ),
    inference(forward_demodulation,[],[f1039,f744])).

fof(f744,plain,(
    sK1 = k2_lattices(sK0,sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f89,f88,f49,f46,f44,f44,f738,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f738,plain,(
    r1_lattices(sK0,sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f46,f88,f86,f89,f49,f177,f44,f44,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f177,plain,(
    r3_lattices(sK0,sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f86,f88,f89,f49,f46,f44,f44,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_lattices(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r3_lattices(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

fof(f86,plain,(
    v6_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f49,f47,f46,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1039,plain,(
    r1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k2_lattices(sK0,k6_lattices(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f89,f46,f49,f88,f87,f44,f651,f90,f44,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v9_lattices(X0)
      | ~ v7_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattices(X0,X1,X2)
                   => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_lattices)).

fof(f651,plain,(
    r1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f46,f89,f88,f49,f44,f90,f552,f64])).

fof(f552,plain,(
    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f551,f91])).

fof(f91,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f48,f84,f46,f44,f81])).

fof(f81,plain,(
    ! [X2,X0] :
      ( ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k6_lattices(X0) = k1_lattices(X0,X2,k6_lattices(X0)) ) ),
    inference(subsumption_resolution,[],[f79,f59])).

fof(f79,plain,(
    ! [X2,X0] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k6_lattices(X0) = k1_lattices(X0,X2,k6_lattices(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X2,X1) = X1
      | k6_lattices(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v14_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k6_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattices)).

fof(f48,plain,(
    v14_lattices(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f551,plain,(
    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f303,f469])).

fof(f469,plain,(
    k6_lattices(sK0) = k2_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f468,f105])).

fof(f105,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,k6_lattices(sK0),k2_lattices(sK0,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f84,f48,f46,f95,f82])).

fof(f82,plain,(
    ! [X2,X0] :
      ( ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k6_lattices(X0) = k1_lattices(X0,k6_lattices(X0),X2) ) ),
    inference(subsumption_resolution,[],[f80,f59])).

fof(f80,plain,(
    ! [X2,X0] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k6_lattices(X0) = k1_lattices(X0,k6_lattices(X0),X2) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = X1
      | k6_lattices(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f46,f83,f44,f44,f74])).

fof(f468,plain,(
    k6_lattices(sK0) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,k6_lattices(sK0),k2_lattices(sK0,sK1,sK1))) ),
    inference(forward_demodulation,[],[f314,f411])).

fof(f411,plain,(
    k2_lattices(sK0,sK1,sK1) = k2_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1) ),
    inference(forward_demodulation,[],[f315,f185])).

fof(f185,plain,(
    sK1 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f46,f88,f49,f44,f44,f68])).

fof(f315,plain,(
    k2_lattices(sK0,sK1,sK1) = k2_lattices(sK0,k2_lattices(sK0,sK1,sK1),k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f89,f49,f44,f95,f72])).

fof(f314,plain,(
    k6_lattices(sK0) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,k6_lattices(sK0),k2_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1))) ),
    inference(unit_resulting_resolution,[],[f46,f89,f49,f102,f90,f72])).

fof(f102,plain,(
    m1_subset_1(k2_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f46,f83,f44,f95,f74])).

fof(f303,plain,(
    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)))) ),
    inference(unit_resulting_resolution,[],[f46,f89,f49,f98,f44,f72])).

fof(f98,plain,(
    m1_subset_1(k2_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f46,f83,f90,f90,f74])).

fof(f87,plain,(
    v7_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f49,f47,f46,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f650,plain,(
    sK1 != k2_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(superposition,[],[f45,f610])).

fof(f610,plain,(
    k4_lattices(sK0,k6_lattices(sK0),sK1) = k2_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f83,f46,f86,f44,f90,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f45,plain,(
    sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,(
    v4_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f49,f47,f46,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:46:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (27877)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (27860)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (27880)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (27856)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (27861)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (27862)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (27864)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (27868)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (27867)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (27881)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.26/0.53  % (27872)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.26/0.53  % (27862)Refutation not found, incomplete strategy% (27862)------------------------------
% 1.26/0.53  % (27862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (27862)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (27862)Memory used [KB]: 10618
% 1.26/0.53  % (27862)Time elapsed: 0.076 s
% 1.26/0.53  % (27862)------------------------------
% 1.26/0.53  % (27862)------------------------------
% 1.26/0.53  % (27866)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.26/0.53  % (27870)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.26/0.53  % (27876)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.26/0.53  % (27863)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.26/0.53  % (27871)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.26/0.53  % (27878)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.26/0.53  % (27858)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.26/0.54  % (27859)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.42/0.55  % (27875)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.42/0.55  % (27879)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.42/0.57  % (27882)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.42/0.58  % (27873)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.42/0.58  % (27865)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.42/0.59  % (27863)Refutation found. Thanks to Tanya!
% 1.42/0.59  % SZS status Theorem for theBenchmark
% 1.42/0.59  % SZS output start Proof for theBenchmark
% 1.42/0.59  fof(f1136,plain,(
% 1.42/0.59    $false),
% 1.42/0.59    inference(subsumption_resolution,[],[f1135,f396])).
% 1.42/0.59  fof(f396,plain,(
% 1.42/0.59    k2_lattices(sK0,k6_lattices(sK0),sK1) = k2_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1)),
% 1.42/0.59    inference(forward_demodulation,[],[f342,f193])).
% 1.42/0.59  fof(f193,plain,(
% 1.42/0.59    sK1 = k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1)),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f46,f88,f49,f44,f90,f68])).
% 1.42/0.59  fof(f68,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (~v8_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | v2_struct_0(X0)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f33])).
% 1.42/0.59  fof(f33,plain,(
% 1.42/0.59    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.59    inference(flattening,[],[f32])).
% 1.42/0.59  fof(f32,plain,(
% 1.42/0.59    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.59    inference(ennf_transformation,[],[f3])).
% 1.42/0.59  fof(f3,axiom,(
% 1.42/0.59    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 1.42/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).
% 1.42/0.59  fof(f90,plain,(
% 1.42/0.59    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f46,f84,f59])).
% 1.42/0.59  fof(f59,plain,(
% 1.42/0.59    ( ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f27])).
% 1.42/0.59  fof(f27,plain,(
% 1.42/0.59    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.59    inference(flattening,[],[f26])).
% 1.42/0.59  fof(f26,plain,(
% 1.42/0.59    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.59    inference(ennf_transformation,[],[f6])).
% 1.42/0.59  fof(f6,axiom,(
% 1.42/0.59    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 1.42/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).
% 1.42/0.59  fof(f84,plain,(
% 1.42/0.59    l2_lattices(sK0)),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f49,f51])).
% 1.42/0.59  fof(f51,plain,(
% 1.42/0.59    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f19])).
% 1.42/0.59  fof(f19,plain,(
% 1.42/0.59    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.42/0.59    inference(ennf_transformation,[],[f7])).
% 1.42/0.59  fof(f7,axiom,(
% 1.42/0.59    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.42/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 1.42/0.59  fof(f44,plain,(
% 1.42/0.59    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.42/0.59    inference(cnf_transformation,[],[f18])).
% 1.42/0.59  fof(f18,plain,(
% 1.42/0.59    ? [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.42/0.59    inference(flattening,[],[f17])).
% 1.42/0.59  fof(f17,plain,(
% 1.42/0.59    ? [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.42/0.59    inference(ennf_transformation,[],[f15])).
% 1.42/0.59  fof(f15,negated_conjecture,(
% 1.42/0.59    ~! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 1.42/0.59    inference(negated_conjecture,[],[f14])).
% 1.42/0.59  fof(f14,conjecture,(
% 1.42/0.59    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 1.42/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).
% 1.42/0.59  fof(f49,plain,(
% 1.42/0.59    l3_lattices(sK0)),
% 1.42/0.59    inference(cnf_transformation,[],[f18])).
% 1.42/0.59  fof(f88,plain,(
% 1.42/0.59    v8_lattices(sK0)),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f49,f47,f46,f55])).
% 1.42/0.59  fof(f55,plain,(
% 1.42/0.59    ( ! [X0] : (v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f21])).
% 1.42/0.59  fof(f21,plain,(
% 1.42/0.59    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.42/0.59    inference(flattening,[],[f20])).
% 1.42/0.59  fof(f20,plain,(
% 1.42/0.59    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.42/0.59    inference(ennf_transformation,[],[f16])).
% 1.42/0.59  fof(f16,plain,(
% 1.42/0.59    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.42/0.59    inference(pure_predicate_removal,[],[f1])).
% 1.42/0.59  fof(f1,axiom,(
% 1.42/0.59    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.42/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 1.42/0.59  fof(f47,plain,(
% 1.42/0.59    v10_lattices(sK0)),
% 1.42/0.59    inference(cnf_transformation,[],[f18])).
% 1.42/0.59  fof(f46,plain,(
% 1.42/0.59    ~v2_struct_0(sK0)),
% 1.42/0.59    inference(cnf_transformation,[],[f18])).
% 1.42/0.59  fof(f342,plain,(
% 1.42/0.59    k2_lattices(sK0,k6_lattices(sK0),sK1) = k2_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1))),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f46,f89,f49,f44,f97,f72])).
% 1.42/0.59  fof(f72,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | v2_struct_0(X0)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f35])).
% 1.42/0.59  fof(f35,plain,(
% 1.42/0.59    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.59    inference(flattening,[],[f34])).
% 1.42/0.59  fof(f34,plain,(
% 1.42/0.59    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.59    inference(ennf_transformation,[],[f4])).
% 1.42/0.59  fof(f4,axiom,(
% 1.42/0.59    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 1.42/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).
% 1.42/0.59  fof(f97,plain,(
% 1.42/0.59    m1_subset_1(k2_lattices(sK0,k6_lattices(sK0),sK1),u1_struct_0(sK0))),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f46,f83,f44,f90,f74])).
% 1.42/0.59  fof(f74,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f37])).
% 1.42/0.59  fof(f37,plain,(
% 1.42/0.59    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.59    inference(flattening,[],[f36])).
% 1.42/0.59  fof(f36,plain,(
% 1.42/0.59    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.59    inference(ennf_transformation,[],[f5])).
% 1.42/0.59  fof(f5,axiom,(
% 1.42/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 1.42/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattices)).
% 1.42/0.59  fof(f83,plain,(
% 1.42/0.59    l1_lattices(sK0)),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f49,f50])).
% 1.42/0.59  fof(f50,plain,(
% 1.42/0.59    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f19])).
% 1.42/0.59  fof(f89,plain,(
% 1.42/0.59    v9_lattices(sK0)),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f49,f47,f46,f56])).
% 1.42/0.59  fof(f56,plain,(
% 1.42/0.59    ( ! [X0] : (v9_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f21])).
% 1.42/0.59  fof(f1135,plain,(
% 1.42/0.59    k2_lattices(sK0,k6_lattices(sK0),sK1) != k2_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1)),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f89,f88,f49,f46,f44,f97,f1063,f64])).
% 1.42/0.59  fof(f64,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) != X1 | r1_lattices(X0,X1,X2)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f31])).
% 1.42/0.59  fof(f31,plain,(
% 1.42/0.59    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.59    inference(flattening,[],[f30])).
% 1.42/0.59  fof(f30,plain,(
% 1.42/0.59    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.59    inference(ennf_transformation,[],[f11])).
% 1.42/0.59  fof(f11,axiom,(
% 1.42/0.59    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.42/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 1.42/0.59  fof(f1063,plain,(
% 1.42/0.59    ~r1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1)),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f85,f46,f84,f44,f650,f97,f1052,f57])).
% 1.42/0.59  fof(f57,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_lattices(X0,X1,X2) | ~r1_lattices(X0,X2,X1) | X1 = X2) )),
% 1.42/0.59    inference(cnf_transformation,[],[f23])).
% 1.42/0.59  fof(f23,plain,(
% 1.42/0.59    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.59    inference(flattening,[],[f22])).
% 1.42/0.59  fof(f22,plain,(
% 1.42/0.59    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.59    inference(ennf_transformation,[],[f12])).
% 1.42/0.59  fof(f12,axiom,(
% 1.42/0.59    ! [X0] : ((l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_lattices(X0,X2,X1) & r1_lattices(X0,X1,X2)) => X1 = X2))))),
% 1.42/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).
% 1.42/0.59  fof(f1052,plain,(
% 1.42/0.59    r1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1))),
% 1.42/0.59    inference(forward_demodulation,[],[f1039,f744])).
% 1.42/0.59  fof(f744,plain,(
% 1.42/0.59    sK1 = k2_lattices(sK0,sK1,sK1)),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f89,f88,f49,f46,f44,f44,f738,f65])).
% 1.42/0.59  fof(f65,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f31])).
% 1.42/0.59  fof(f738,plain,(
% 1.42/0.59    r1_lattices(sK0,sK1,sK1)),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f46,f88,f86,f89,f49,f177,f44,f44,f78])).
% 1.42/0.59  fof(f78,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f43])).
% 1.42/0.59  fof(f43,plain,(
% 1.42/0.59    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.59    inference(flattening,[],[f42])).
% 1.42/0.59  fof(f42,plain,(
% 1.42/0.59    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.59    inference(ennf_transformation,[],[f9])).
% 1.42/0.59  fof(f9,axiom,(
% 1.42/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.42/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 1.42/0.59  fof(f177,plain,(
% 1.42/0.59    r3_lattices(sK0,sK1,sK1)),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f86,f88,f89,f49,f46,f44,f44,f76])).
% 1.42/0.59  fof(f76,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_lattices(X0,X1,X1)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f41])).
% 1.42/0.59  fof(f41,plain,(
% 1.42/0.59    ! [X0,X1,X2] : (r3_lattices(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.59    inference(flattening,[],[f40])).
% 1.42/0.59  fof(f40,plain,(
% 1.42/0.59    ! [X0,X1,X2] : (r3_lattices(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.59    inference(ennf_transformation,[],[f10])).
% 1.42/0.59  fof(f10,axiom,(
% 1.42/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => r3_lattices(X0,X1,X1))),
% 1.42/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_lattices)).
% 1.42/0.59  fof(f86,plain,(
% 1.42/0.59    v6_lattices(sK0)),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f49,f47,f46,f53])).
% 1.42/0.59  fof(f53,plain,(
% 1.42/0.59    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f21])).
% 1.42/0.59  fof(f1039,plain,(
% 1.42/0.59    r1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k2_lattices(sK0,k6_lattices(sK0),sK1))),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f89,f46,f49,f88,f87,f44,f651,f90,f44,f58])).
% 1.42/0.59  fof(f58,plain,(
% 1.42/0.59    ( ! [X2,X0,X3,X1] : (~v9_lattices(X0) | ~v7_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_lattices(X0,X1,X2) | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))) )),
% 1.42/0.59    inference(cnf_transformation,[],[f25])).
% 1.42/0.59  fof(f25,plain,(
% 1.42/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v7_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.59    inference(flattening,[],[f24])).
% 1.42/0.59  fof(f24,plain,(
% 1.42/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | ~r1_lattices(X0,X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v7_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.59    inference(ennf_transformation,[],[f13])).
% 1.42/0.59  fof(f13,axiom,(
% 1.42/0.59    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 1.42/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_lattices)).
% 1.42/0.59  fof(f651,plain,(
% 1.42/0.59    r1_lattices(sK0,sK1,k6_lattices(sK0))),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f46,f89,f88,f49,f44,f90,f552,f64])).
% 1.42/0.59  fof(f552,plain,(
% 1.42/0.59    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))),
% 1.42/0.59    inference(forward_demodulation,[],[f551,f91])).
% 1.42/0.59  fof(f91,plain,(
% 1.42/0.59    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f48,f84,f46,f44,f81])).
% 1.42/0.59  fof(f81,plain,(
% 1.42/0.59    ( ! [X2,X0] : (~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k6_lattices(X0) = k1_lattices(X0,X2,k6_lattices(X0))) )),
% 1.42/0.59    inference(subsumption_resolution,[],[f79,f59])).
% 1.42/0.59  fof(f79,plain,(
% 1.42/0.59    ( ! [X2,X0] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~v14_lattices(X0) | ~m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k6_lattices(X0) = k1_lattices(X0,X2,k6_lattices(X0))) )),
% 1.42/0.59    inference(equality_resolution,[],[f62])).
% 1.42/0.59  fof(f62,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~v14_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X2,X1) = X1 | k6_lattices(X0) != X1) )),
% 1.42/0.59    inference(cnf_transformation,[],[f29])).
% 1.42/0.59  fof(f29,plain,(
% 1.42/0.59    ! [X0] : (! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.59    inference(flattening,[],[f28])).
% 1.42/0.59  fof(f28,plain,(
% 1.42/0.59    ! [X0] : ((! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.59    inference(ennf_transformation,[],[f2])).
% 1.42/0.59  fof(f2,axiom,(
% 1.42/0.59    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => (v14_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k6_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1))))))),
% 1.42/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattices)).
% 1.42/0.59  fof(f48,plain,(
% 1.42/0.59    v14_lattices(sK0)),
% 1.42/0.59    inference(cnf_transformation,[],[f18])).
% 1.42/0.59  fof(f551,plain,(
% 1.42/0.59    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k6_lattices(sK0)))),
% 1.42/0.59    inference(forward_demodulation,[],[f303,f469])).
% 1.42/0.59  fof(f469,plain,(
% 1.42/0.59    k6_lattices(sK0) = k2_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))),
% 1.42/0.59    inference(forward_demodulation,[],[f468,f105])).
% 1.42/0.59  fof(f105,plain,(
% 1.42/0.59    k6_lattices(sK0) = k1_lattices(sK0,k6_lattices(sK0),k2_lattices(sK0,sK1,sK1))),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f84,f48,f46,f95,f82])).
% 1.42/0.59  fof(f82,plain,(
% 1.42/0.59    ( ! [X2,X0] : (~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k6_lattices(X0) = k1_lattices(X0,k6_lattices(X0),X2)) )),
% 1.42/0.59    inference(subsumption_resolution,[],[f80,f59])).
% 1.42/0.59  fof(f80,plain,(
% 1.42/0.59    ( ! [X2,X0] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~v14_lattices(X0) | ~m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k6_lattices(X0) = k1_lattices(X0,k6_lattices(X0),X2)) )),
% 1.42/0.59    inference(equality_resolution,[],[f61])).
% 1.42/0.59  fof(f61,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~v14_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = X1 | k6_lattices(X0) != X1) )),
% 1.42/0.59    inference(cnf_transformation,[],[f29])).
% 1.42/0.59  fof(f95,plain,(
% 1.42/0.59    m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0))),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f46,f83,f44,f44,f74])).
% 1.42/0.59  fof(f468,plain,(
% 1.42/0.59    k6_lattices(sK0) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,k6_lattices(sK0),k2_lattices(sK0,sK1,sK1)))),
% 1.42/0.59    inference(forward_demodulation,[],[f314,f411])).
% 1.42/0.59  fof(f411,plain,(
% 1.42/0.59    k2_lattices(sK0,sK1,sK1) = k2_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1)),
% 1.42/0.59    inference(forward_demodulation,[],[f315,f185])).
% 1.42/0.59  fof(f185,plain,(
% 1.42/0.59    sK1 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1)),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f46,f88,f49,f44,f44,f68])).
% 1.42/0.59  fof(f315,plain,(
% 1.42/0.59    k2_lattices(sK0,sK1,sK1) = k2_lattices(sK0,k2_lattices(sK0,sK1,sK1),k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1))),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f46,f89,f49,f44,f95,f72])).
% 1.42/0.59  fof(f314,plain,(
% 1.42/0.59    k6_lattices(sK0) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,k6_lattices(sK0),k2_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1)))),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f46,f89,f49,f102,f90,f72])).
% 1.42/0.59  fof(f102,plain,(
% 1.42/0.59    m1_subset_1(k2_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1),u1_struct_0(sK0))),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f46,f83,f44,f95,f74])).
% 1.42/0.59  fof(f303,plain,(
% 1.42/0.59    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))))),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f46,f89,f49,f98,f44,f72])).
% 1.42/0.59  fof(f98,plain,(
% 1.42/0.59    m1_subset_1(k2_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)),u1_struct_0(sK0))),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f46,f83,f90,f90,f74])).
% 1.42/0.59  fof(f87,plain,(
% 1.42/0.59    v7_lattices(sK0)),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f49,f47,f46,f54])).
% 1.42/0.59  fof(f54,plain,(
% 1.42/0.59    ( ! [X0] : (v7_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f21])).
% 1.42/0.59  fof(f650,plain,(
% 1.42/0.59    sK1 != k2_lattices(sK0,k6_lattices(sK0),sK1)),
% 1.42/0.59    inference(superposition,[],[f45,f610])).
% 1.42/0.59  fof(f610,plain,(
% 1.42/0.59    k4_lattices(sK0,k6_lattices(sK0),sK1) = k2_lattices(sK0,k6_lattices(sK0),sK1)),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f83,f46,f86,f44,f90,f75])).
% 1.42/0.59  fof(f75,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f39])).
% 1.42/0.59  fof(f39,plain,(
% 1.42/0.59    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.59    inference(flattening,[],[f38])).
% 1.42/0.59  fof(f38,plain,(
% 1.42/0.59    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.59    inference(ennf_transformation,[],[f8])).
% 1.42/0.59  fof(f8,axiom,(
% 1.42/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2))),
% 1.42/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 1.42/0.59  fof(f45,plain,(
% 1.42/0.59    sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1)),
% 1.42/0.59    inference(cnf_transformation,[],[f18])).
% 1.42/0.59  fof(f85,plain,(
% 1.42/0.59    v4_lattices(sK0)),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f49,f47,f46,f52])).
% 1.42/0.59  fof(f52,plain,(
% 1.42/0.59    ( ! [X0] : (v4_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f21])).
% 1.42/0.59  % SZS output end Proof for theBenchmark
% 1.42/0.59  % (27863)------------------------------
% 1.42/0.59  % (27863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.59  % (27863)Termination reason: Refutation
% 1.42/0.59  
% 1.42/0.59  % (27863)Memory used [KB]: 2174
% 1.42/0.59  % (27863)Time elapsed: 0.127 s
% 1.42/0.59  % (27863)------------------------------
% 1.42/0.59  % (27863)------------------------------
% 1.42/0.59  % (27855)Success in time 0.226 s
%------------------------------------------------------------------------------
