%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1192+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 300 expanded)
%              Number of leaves         :    7 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  253 (1485 expanded)
%              Number of equality atoms :   50 ( 202 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(subsumption_resolution,[],[f227,f23])).

fof(f23,plain,(
    sK1 != k1_lattices(sK0,sK1,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_lattices(X0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_lattices(X0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k1_lattices(X0,X1,X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).

fof(f227,plain,(
    sK1 = k1_lattices(sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f216,f226])).

fof(f226,plain,(
    sK1 = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) ),
    inference(backward_demodulation,[],[f179,f219])).

fof(f219,plain,(
    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) ),
    inference(resolution,[],[f100,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f100,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X6)) ) ),
    inference(subsumption_resolution,[],[f99,f27])).

fof(f27,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f99,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X6))
      | ~ v9_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f98,f28])).

fof(f28,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f98,plain,(
    ! [X6] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X6))
      | ~ v9_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f79,f24])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f79,plain,(
    ! [X6] :
      ( v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X6))
      | ~ v9_lattices(sK0) ) ),
    inference(resolution,[],[f22,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
      | ~ v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

fof(f179,plain,(
    k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) ),
    inference(resolution,[],[f88,f116])).

fof(f116,plain,(
    m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f105,f22])).

fof(f105,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,u1_struct_0(sK0))
      | m1_subset_1(k1_lattices(sK0,sK1,X8),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f104,f72])).

fof(f72,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f28,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f104,plain,(
    ! [X8] :
      ( ~ l2_lattices(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | m1_subset_1(k1_lattices(sK0,sK1,X8),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f81,f24])).

fof(f81,plain,(
    ! [X8] :
      ( v2_struct_0(sK0)
      | ~ l2_lattices(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | m1_subset_1(k1_lattices(sK0,sK1,X8),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f22,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattices)).

fof(f88,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X2) = k2_lattices(sK0,sK1,X2) ) ),
    inference(subsumption_resolution,[],[f87,f71])).

fof(f71,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f28,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,(
    ! [X2] :
      ( ~ l1_lattices(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X2) = k2_lattices(sK0,sK1,X2) ) ),
    inference(subsumption_resolution,[],[f86,f25])).

fof(f25,plain,(
    v6_lattices(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f86,plain,(
    ! [X2] :
      ( ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X2) = k2_lattices(sK0,sK1,X2) ) ),
    inference(subsumption_resolution,[],[f75,f24])).

fof(f75,plain,(
    ! [X2] :
      ( v2_struct_0(sK0)
      | ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X2) = k2_lattices(sK0,sK1,X2) ) ),
    inference(resolution,[],[f22,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f216,plain,(
    sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)),sK1) ),
    inference(forward_demodulation,[],[f209,f194])).

fof(f194,plain,(
    k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) = k2_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) ),
    inference(forward_demodulation,[],[f188,f170])).

fof(f170,plain,(
    k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) = k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) ),
    inference(resolution,[],[f85,f116])).

fof(f85,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f84,f71])).

fof(f84,plain,(
    ! [X0] :
      ( ~ l1_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f83,f25])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f73,f24])).

fof(f73,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1) ) ),
    inference(resolution,[],[f22,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f188,plain,(
    k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) = k2_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) ),
    inference(resolution,[],[f91,f116])).

fof(f91,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k4_lattices(sK0,X3,sK1) = k2_lattices(sK0,X3,sK1) ) ),
    inference(subsumption_resolution,[],[f90,f71])).

fof(f90,plain,(
    ! [X3] :
      ( ~ l1_lattices(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k4_lattices(sK0,X3,sK1) = k2_lattices(sK0,X3,sK1) ) ),
    inference(subsumption_resolution,[],[f89,f25])).

fof(f89,plain,(
    ! [X3] :
      ( ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k4_lattices(sK0,X3,sK1) = k2_lattices(sK0,X3,sK1) ) ),
    inference(subsumption_resolution,[],[f76,f24])).

fof(f76,plain,(
    ! [X3] :
      ( v2_struct_0(sK0)
      | ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k4_lattices(sK0,X3,sK1) = k2_lattices(sK0,X3,sK1) ) ),
    inference(resolution,[],[f22,f30])).

fof(f209,plain,(
    sK1 = k1_lattices(sK0,k2_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1),sK1) ),
    inference(resolution,[],[f97,f116])).

fof(f97,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | sK1 = k1_lattices(sK0,k2_lattices(sK0,X5,sK1),sK1) ) ),
    inference(subsumption_resolution,[],[f96,f26])).

fof(f26,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f96,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | sK1 = k1_lattices(sK0,k2_lattices(sK0,X5,sK1),sK1)
      | ~ v8_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f95,f28])).

fof(f95,plain,(
    ! [X5] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | sK1 = k1_lattices(sK0,k2_lattices(sK0,X5,sK1),sK1)
      | ~ v8_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f78,f24])).

fof(f78,plain,(
    ! [X5] :
      ( v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | sK1 = k1_lattices(sK0,k2_lattices(sK0,X5,sK1),sK1)
      | ~ v8_lattices(sK0) ) ),
    inference(resolution,[],[f22,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
      | ~ v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

%------------------------------------------------------------------------------
