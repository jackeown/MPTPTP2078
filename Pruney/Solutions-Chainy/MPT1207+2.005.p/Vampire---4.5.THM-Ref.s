%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 280 expanded)
%              Number of leaves         :    8 (  49 expanded)
%              Depth                    :   23
%              Number of atoms          :  331 (1318 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(subsumption_resolution,[],[f106,f28])).

fof(f28,plain,(
    ~ r3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r3_lattices(X0,k5_lattices(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r3_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattices)).

fof(f106,plain,(
    r3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f105,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f105,plain,
    ( v2_struct_0(sK0)
    | r3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f104,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f104,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f103,f74])).

fof(f74,plain,(
    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f73,f29])).

fof(f73,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f58,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f58,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f32,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f32,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f103,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f102,f32])).

fof(f102,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f101,f57])).

fof(f57,plain,(
    v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f56,f32])).

fof(f56,plain,
    ( ~ l3_lattices(sK0)
    | v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f49,f29])).

fof(f49,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v9_lattices(sK0) ),
    inference(resolution,[],[f30,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
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

fof(f30,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f101,plain,
    ( ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f100,f55])).

fof(f55,plain,(
    v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f54,f32])).

fof(f54,plain,
    ( ~ l3_lattices(sK0)
    | v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f48,f29])).

fof(f48,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v8_lattices(sK0) ),
    inference(resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f100,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f99,f53])).

fof(f53,plain,(
    v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f52,f32])).

fof(f52,plain,
    ( ~ l3_lattices(sK0)
    | v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f47,f29])).

fof(f47,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v6_lattices(sK0) ),
    inference(resolution,[],[f30,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f99,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(resolution,[],[f96,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f96,plain,(
    r1_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f94,f92])).

fof(f92,plain,(
    sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(forward_demodulation,[],[f90,f71])).

fof(f71,plain,(
    sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f70,f29])).

fof(f70,plain,
    ( v2_struct_0(sK0)
    | sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f69,f32])).

fof(f69,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f68,f31])).

fof(f31,plain,(
    v13_lattices(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f68,plain,
    ( ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f62,f30])).

fof(f62,plain,
    ( ~ v10_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(resolution,[],[f27,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_lattices)).

fof(f90,plain,(
    k3_lattices(sK0,k5_lattices(sK0),sK1) = k1_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(resolution,[],[f83,f27])).

fof(f83,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,k5_lattices(sK0),X0) = k3_lattices(sK0,k5_lattices(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f82,f29])).

fof(f82,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,k5_lattices(sK0),X0) = k3_lattices(sK0,k5_lattices(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f81,f59])).

fof(f59,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f32,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,(
    ! [X0] :
      ( ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,k5_lattices(sK0),X0) = k3_lattices(sK0,k5_lattices(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f78,f51])).

fof(f51,plain,(
    v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f50,f32])).

fof(f50,plain,
    ( ~ l3_lattices(sK0)
    | v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f46,f29])).

fof(f46,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v4_lattices(sK0) ),
    inference(resolution,[],[f30,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v4_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v4_lattices(sK0)
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,k5_lattices(sK0),X0) = k3_lattices(sK0,k5_lattices(sK0),X0) ) ),
    inference(resolution,[],[f74,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f94,plain,
    ( sK1 != k1_lattices(sK0,k5_lattices(sK0),sK1)
    | r1_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(resolution,[],[f85,f27])).

fof(f85,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_lattices(sK0,k5_lattices(sK0),X1) != X1
      | r1_lattices(sK0,k5_lattices(sK0),X1) ) ),
    inference(subsumption_resolution,[],[f84,f29])).

fof(f84,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_lattices(sK0,k5_lattices(sK0),X1) != X1
      | r1_lattices(sK0,k5_lattices(sK0),X1) ) ),
    inference(subsumption_resolution,[],[f79,f59])).

fof(f79,plain,(
    ! [X1] :
      ( ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_lattices(sK0,k5_lattices(sK0),X1) != X1
      | r1_lattices(sK0,k5_lattices(sK0),X1) ) ),
    inference(resolution,[],[f74,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) != X2
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:20:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (16914)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (16914)Refutation not found, incomplete strategy% (16914)------------------------------
% 0.20/0.47  % (16914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (16914)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (16914)Memory used [KB]: 6140
% 0.20/0.47  % (16914)Time elapsed: 0.057 s
% 0.20/0.47  % (16914)------------------------------
% 0.20/0.47  % (16914)------------------------------
% 0.20/0.47  % (16922)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.49  % (16912)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (16910)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (16910)Refutation not found, incomplete strategy% (16910)------------------------------
% 0.20/0.50  % (16910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16910)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16910)Memory used [KB]: 10618
% 0.20/0.50  % (16910)Time elapsed: 0.082 s
% 0.20/0.50  % (16910)------------------------------
% 0.20/0.50  % (16910)------------------------------
% 0.20/0.51  % (16927)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.51  % (16915)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.51  % (16927)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f106,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ~r3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (~r3_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (~r3_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r3_lattices(X0,k5_lattices(X0),X1)))),
% 0.20/0.51    inference(negated_conjecture,[],[f8])).
% 0.20/0.51  fof(f8,conjecture,(
% 0.20/0.51    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r3_lattices(X0,k5_lattices(X0),X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattices)).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    r3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f105,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ~v2_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    v2_struct_0(sK0) | r3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f104,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f103,f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f73,f29])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    v2_struct_0(sK0) | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 0.20/0.51    inference(resolution,[],[f58,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_lattices(X0) | v2_struct_0(X0) | m1_subset_1(k5_lattices(X0),u1_struct_0(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    l1_lattices(sK0)),
% 0.20/0.51    inference(resolution,[],[f32,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0] : (~l3_lattices(X0) | l1_lattices(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    l3_lattices(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f102,f32])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f101,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    v9_lattices(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f56,f32])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ~l3_lattices(sK0) | v9_lattices(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f49,f29])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    v2_struct_0(sK0) | ~l3_lattices(sK0) | v9_lattices(sK0)),
% 0.20/0.51    inference(resolution,[],[f30,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v9_lattices(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.20/0.51    inference(flattening,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    v10_lattices(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f100,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    v8_lattices(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f54,f32])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ~l3_lattices(sK0) | v8_lattices(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f48,f29])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    v2_struct_0(sK0) | ~l3_lattices(sK0) | v8_lattices(sK0)),
% 0.20/0.51    inference(resolution,[],[f30,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v8_lattices(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f99,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    v6_lattices(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f52,f32])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ~l3_lattices(sK0) | v6_lattices(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f47,f29])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    v2_struct_0(sK0) | ~l3_lattices(sK0) | v6_lattices(sK0)),
% 0.20/0.51    inference(resolution,[],[f30,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v6_lattices(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(resolution,[],[f96,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_lattices(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    r1_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f94,f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(forward_demodulation,[],[f90,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f70,f29])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    v2_struct_0(sK0) | sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f69,f32])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ~l3_lattices(sK0) | v2_struct_0(sK0) | sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f68,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    v13_lattices(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ~v13_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f62,f30])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ~v10_lattices(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(resolution,[],[f27,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v10_lattices(X0) | ~v13_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | k3_lattices(X0,k5_lattices(X0),X1) = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k5_lattices(X0),X1) = X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_lattices)).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    k3_lattices(sK0,k5_lattices(sK0),sK1) = k1_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(resolution,[],[f83,f27])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k5_lattices(sK0),X0) = k3_lattices(sK0,k5_lattices(sK0),X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f82,f29])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k5_lattices(sK0),X0) = k3_lattices(sK0,k5_lattices(sK0),X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f81,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    l2_lattices(sK0)),
% 0.20/0.51    inference(resolution,[],[f32,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0] : (~l3_lattices(X0) | l2_lattices(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ( ! [X0] : (~l2_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k5_lattices(sK0),X0) = k3_lattices(sK0,k5_lattices(sK0),X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f78,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    v4_lattices(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f50,f32])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ~l3_lattices(sK0) | v4_lattices(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f46,f29])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    v2_struct_0(sK0) | ~l3_lattices(sK0) | v4_lattices(sK0)),
% 0.20/0.51    inference(resolution,[],[f30,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v4_lattices(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X0] : (~v4_lattices(sK0) | ~l2_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k5_lattices(sK0),X0) = k3_lattices(sK0,k5_lattices(sK0),X0)) )),
% 0.20/0.51    inference(resolution,[],[f74,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v4_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    sK1 != k1_lattices(sK0,k5_lattices(sK0),sK1) | r1_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    inference(resolution,[],[f85,f27])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,k5_lattices(sK0),X1) != X1 | r1_lattices(sK0,k5_lattices(sK0),X1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f84,f29])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X1] : (v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,k5_lattices(sK0),X1) != X1 | r1_lattices(sK0,k5_lattices(sK0),X1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f79,f59])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ( ! [X1] : (~l2_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,k5_lattices(sK0),X1) != X1 | r1_lattices(sK0,k5_lattices(sK0),X1)) )),
% 0.20/0.51    inference(resolution,[],[f74,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) != X2 | r1_lattices(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (16927)------------------------------
% 0.20/0.51  % (16927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16927)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (16927)Memory used [KB]: 6140
% 0.20/0.51  % (16927)Time elapsed: 0.098 s
% 0.20/0.51  % (16927)------------------------------
% 0.20/0.51  % (16927)------------------------------
% 0.20/0.51  % (16915)Refutation not found, incomplete strategy% (16915)------------------------------
% 0.20/0.51  % (16915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16915)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (16915)Memory used [KB]: 10618
% 0.20/0.51  % (16915)Time elapsed: 0.091 s
% 0.20/0.51  % (16915)------------------------------
% 0.20/0.51  % (16915)------------------------------
% 0.20/0.51  % (16906)Success in time 0.145 s
%------------------------------------------------------------------------------
