%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:43 EST 2020

% Result     : Theorem 2.42s
% Output     : Refutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :  162 (2184 expanded)
%              Number of leaves         :   19 ( 427 expanded)
%              Depth                    :   22
%              Number of atoms          :  567 (10348 expanded)
%              Number of equality atoms :  122 (1373 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2039,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2038,f76])).

fof(f76,plain,(
    sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_lattices)).

fof(f2038,plain,(
    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    inference(backward_demodulation,[],[f364,f2037])).

fof(f2037,plain,(
    sK1 = k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f2036,f887])).

fof(f887,plain,(
    sK1 = k1_lattices(sK0,sK1,k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f871,f633])).

fof(f633,plain,(
    sK1 = k3_lattices(sK0,sK1,k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f621,f190])).

fof(f190,plain,(
    sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f139,f78,f80,f77,f75,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_lattices)).

fof(f75,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f77,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f139,plain,(
    v13_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f80,f77,f137,f83])).

fof(f83,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | v2_struct_0(X0)
      | ~ v15_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v14_lattices(X0)
          & v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_lattices)).

fof(f137,plain,(
    v15_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f80,f77,f79,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v15_lattices(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_lattices)).

fof(f79,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f621,plain,(
    k3_lattices(sK0,k5_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k5_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f135,f77,f140,f145,f75,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
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
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f145,plain,(
    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f77,f134,f93])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f134,plain,(
    l1_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f80,f81])).

fof(f81,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f140,plain,(
    v4_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f80,f78,f77,f87])).

fof(f87,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f27,plain,(
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
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f135,plain,(
    l2_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f80,f82])).

fof(f82,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f871,plain,(
    k1_lattices(sK0,sK1,k5_lattices(sK0)) = k3_lattices(sK0,sK1,k5_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f135,f77,f140,f145,f75,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f2036,plain,(
    k1_lattices(sK0,sK1,k5_lattices(sK0)) = k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f2035,f880])).

fof(f880,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(forward_demodulation,[],[f877,f631])).

fof(f631,plain,(
    k6_lattices(sK0) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(forward_demodulation,[],[f629,f248])).

fof(f248,plain,(
    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f79,f78,f80,f77,f75,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattices)).

fof(f629,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f135,f77,f140,f149,f75,f122])).

fof(f149,plain,(
    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f77,f80,f75,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f877,plain,(
    k1_lattices(sK0,sK1,k7_lattices(sK0,sK1)) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f135,f77,f140,f149,f75,f123])).

fof(f2035,plain,(
    k1_lattices(sK0,sK1,k5_lattices(sK0)) = k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))) ),
    inference(forward_demodulation,[],[f2034,f1800])).

fof(f1800,plain,(
    sK1 = k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) ),
    inference(backward_demodulation,[],[f1142,f1797])).

fof(f1797,plain,(
    sK1 = k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) ),
    inference(backward_demodulation,[],[f1117,f1796])).

fof(f1796,plain,(
    sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1795,f911])).

fof(f911,plain,(
    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f855,f641])).

fof(f641,plain,(
    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f601,f188])).

fof(f188,plain,(
    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,k7_lattices(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f139,f78,f80,f77,f152,f103])).

fof(f152,plain,(
    m1_subset_1(k7_lattices(sK0,k7_lattices(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f77,f80,f149,f121])).

fof(f601,plain,(
    k3_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,k7_lattices(sK0,sK1))) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f135,f77,f140,f145,f152,f122])).

fof(f855,plain,(
    k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f135,f77,f140,f145,f152,f123])).

fof(f1795,plain,(
    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0))) ),
    inference(forward_demodulation,[],[f1794,f1781])).

fof(f1781,plain,(
    sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f1780,f360])).

fof(f360,plain,(
    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f350,f158])).

fof(f158,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f135,f77,f138,f75,f130])).

fof(f130,plain,(
    ! [X2,X0] :
      ( ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | ~ v14_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k6_lattices(X0) = k1_lattices(X0,X2,k6_lattices(X0)) ) ),
    inference(subsumption_resolution,[],[f126,f92])).

fof(f92,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(f126,plain,(
    ! [X2,X0] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k6_lattices(X0) = k1_lattices(X0,X2,k6_lattices(X0)) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X2,X1) = X1
      | k6_lattices(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattices)).

fof(f138,plain,(
    v14_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f80,f77,f137,f84])).

fof(f84,plain,(
    ! [X0] :
      ( v14_lattices(X0)
      | v2_struct_0(X0)
      | ~ v15_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f350,plain,(
    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k6_lattices(sK0))) ),
    inference(unit_resulting_resolution,[],[f77,f143,f80,f144,f75,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f144,plain,(
    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f77,f135,f92])).

fof(f143,plain,(
    v9_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f80,f78,f77,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1780,plain,(
    k2_lattices(sK0,sK1,k6_lattices(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f1779,f902])).

fof(f902,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) ),
    inference(forward_demodulation,[],[f861,f247])).

fof(f247,plain,(
    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f79,f78,f80,f77,f149,f105])).

fof(f861,plain,(
    k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) = k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f135,f77,f140,f149,f152,f123])).

fof(f1779,plain,(
    k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))) = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f1778,f1117])).

fof(f1778,plain,(
    k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))) = k1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f1717,f1121])).

fof(f1121,plain,(
    k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1118,f1032])).

fof(f1032,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1030,f258])).

fof(f258,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f79,f78,f80,f77,f75,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattices)).

fof(f1030,plain,(
    k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f134,f77,f141,f149,f75,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
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
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f141,plain,(
    v6_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f80,f78,f77,f88])).

fof(f88,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1118,plain,(
    k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f134,f77,f141,f149,f75,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f1717,plain,(
    k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))) = k1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),k2_lattices(sK0,sK1,k7_lattices(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f77,f136,f80,f149,f152,f75,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v11_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattices)).

fof(f136,plain,(
    v11_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f80,f79,f77,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ v17_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1794,plain,(
    k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f1793,f1117])).

fof(f1793,plain,(
    k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0))) = k1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f1713,f176])).

fof(f176,plain,(
    k5_lattices(sK0) = k2_lattices(sK0,sK1,k5_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f134,f77,f139,f75,f132])).

fof(f132,plain,(
    ! [X2,X0] :
      ( ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0)) ) ),
    inference(subsumption_resolution,[],[f128,f93])).

fof(f128,plain,(
    ! [X2,X0] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0)) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X2,X1) = X1
      | k5_lattices(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(f1713,plain,(
    k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0))) = k1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),k2_lattices(sK0,sK1,k5_lattices(sK0))) ),
    inference(unit_resulting_resolution,[],[f77,f136,f80,f145,f152,f75,f107])).

fof(f1117,plain,(
    k2_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f134,f77,f141,f152,f75,f125])).

fof(f1142,plain,(
    k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1103,f1029])).

fof(f1029,plain,(
    k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f134,f77,f141,f152,f75,f124])).

fof(f1103,plain,(
    k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f134,f77,f141,f75,f152,f125])).

fof(f2034,plain,(
    k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))) = k1_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1),k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f1657,f1144])).

fof(f1144,plain,(
    k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1102,f257])).

fof(f257,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f79,f78,f80,f77,f149,f106])).

fof(f1102,plain,(
    k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) = k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f134,f77,f141,f149,f152,f125])).

fof(f1657,plain,(
    k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))) = k1_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1),k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f77,f136,f80,f149,f75,f152,f107])).

fof(f364,plain,(
    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f330,f161])).

fof(f161,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f77,f135,f138,f152,f130])).

fof(f330,plain,(
    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k6_lattices(sK0))) ),
    inference(unit_resulting_resolution,[],[f77,f143,f80,f144,f152,f114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:22:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (31089)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.49  % (31081)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (31075)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (31073)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.54  % (31074)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (31088)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (31091)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (31082)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (31080)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.55  % (31083)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.55  % (31076)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.55  % (31090)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.56  % (31075)Refutation not found, incomplete strategy% (31075)------------------------------
% 0.21/0.56  % (31075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (31075)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (31075)Memory used [KB]: 10618
% 0.21/0.56  % (31075)Time elapsed: 0.121 s
% 0.21/0.56  % (31075)------------------------------
% 0.21/0.56  % (31075)------------------------------
% 0.21/0.56  % (31092)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.57  % (31084)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.73/0.60  % (31070)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.73/0.60  % (31069)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.73/0.61  % (31072)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.73/0.61  % (31085)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.73/0.61  % (31093)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.73/0.62  % (31087)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.73/0.62  % (31077)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.73/0.62  % (31079)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.73/0.63  % (31086)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.73/0.64  % (31094)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.73/0.64  % (31078)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.73/0.65  % (31071)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 2.42/0.68  % (31076)Refutation found. Thanks to Tanya!
% 2.42/0.68  % SZS status Theorem for theBenchmark
% 2.42/0.68  % SZS output start Proof for theBenchmark
% 2.42/0.68  fof(f2039,plain,(
% 2.42/0.68    $false),
% 2.42/0.68    inference(subsumption_resolution,[],[f2038,f76])).
% 2.42/0.68  fof(f76,plain,(
% 2.42/0.68    sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1))),
% 2.42/0.68    inference(cnf_transformation,[],[f30])).
% 2.42/0.68  fof(f30,plain,(
% 2.42/0.68    ? [X0] : (? [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.42/0.68    inference(flattening,[],[f29])).
% 2.42/0.68  fof(f29,plain,(
% 2.42/0.68    ? [X0] : (? [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.42/0.68    inference(ennf_transformation,[],[f25])).
% 2.42/0.68  fof(f25,negated_conjecture,(
% 2.42/0.68    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 2.42/0.68    inference(negated_conjecture,[],[f24])).
% 2.42/0.68  fof(f24,conjecture,(
% 2.42/0.68    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_lattices)).
% 2.42/0.68  fof(f2038,plain,(
% 2.42/0.68    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))),
% 2.42/0.68    inference(backward_demodulation,[],[f364,f2037])).
% 2.42/0.68  fof(f2037,plain,(
% 2.42/0.68    sK1 = k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k6_lattices(sK0))),
% 2.42/0.68    inference(forward_demodulation,[],[f2036,f887])).
% 2.42/0.68  fof(f887,plain,(
% 2.42/0.68    sK1 = k1_lattices(sK0,sK1,k5_lattices(sK0))),
% 2.42/0.68    inference(forward_demodulation,[],[f871,f633])).
% 2.42/0.68  fof(f633,plain,(
% 2.42/0.68    sK1 = k3_lattices(sK0,sK1,k5_lattices(sK0))),
% 2.42/0.68    inference(forward_demodulation,[],[f621,f190])).
% 2.42/0.68  fof(f190,plain,(
% 2.42/0.68    sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1)),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f139,f78,f80,f77,f75,f103])).
% 2.42/0.68  fof(f103,plain,(
% 2.42/0.68    ( ! [X0,X1] : (~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k3_lattices(X0,k5_lattices(X0),X1) = X1) )),
% 2.42/0.68    inference(cnf_transformation,[],[f51])).
% 2.42/0.68  fof(f51,plain,(
% 2.42/0.68    ! [X0] : (! [X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.68    inference(flattening,[],[f50])).
% 2.42/0.68  fof(f50,plain,(
% 2.42/0.68    ! [X0] : (! [X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.42/0.68    inference(ennf_transformation,[],[f19])).
% 2.42/0.68  fof(f19,axiom,(
% 2.42/0.68    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k5_lattices(X0),X1) = X1))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_lattices)).
% 2.42/0.68  fof(f75,plain,(
% 2.42/0.68    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.42/0.68    inference(cnf_transformation,[],[f30])).
% 2.42/0.68  fof(f77,plain,(
% 2.42/0.68    ~v2_struct_0(sK0)),
% 2.42/0.68    inference(cnf_transformation,[],[f30])).
% 2.42/0.68  fof(f80,plain,(
% 2.42/0.68    l3_lattices(sK0)),
% 2.42/0.68    inference(cnf_transformation,[],[f30])).
% 2.42/0.68  fof(f78,plain,(
% 2.42/0.68    v10_lattices(sK0)),
% 2.42/0.68    inference(cnf_transformation,[],[f30])).
% 2.42/0.68  fof(f139,plain,(
% 2.42/0.68    v13_lattices(sK0)),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f80,f77,f137,f83])).
% 2.42/0.68  fof(f83,plain,(
% 2.42/0.68    ( ! [X0] : (v13_lattices(X0) | v2_struct_0(X0) | ~v15_lattices(X0) | ~l3_lattices(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f33])).
% 2.42/0.68  fof(f33,plain,(
% 2.42/0.68    ! [X0] : ((v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0)) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.42/0.68    inference(flattening,[],[f32])).
% 2.42/0.68  fof(f32,plain,(
% 2.42/0.68    ! [X0] : (((v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0)) | (~v15_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.42/0.68    inference(ennf_transformation,[],[f3])).
% 2.42/0.68  fof(f3,axiom,(
% 2.42/0.68    ! [X0] : (l3_lattices(X0) => ((v15_lattices(X0) & ~v2_struct_0(X0)) => (v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0))))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_lattices)).
% 2.42/0.68  fof(f137,plain,(
% 2.42/0.68    v15_lattices(sK0)),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f80,f77,f79,f86])).
% 2.42/0.68  fof(f86,plain,(
% 2.42/0.68    ( ! [X0] : (~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v15_lattices(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f35])).
% 2.42/0.68  fof(f35,plain,(
% 2.42/0.68    ! [X0] : ((v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.42/0.68    inference(flattening,[],[f34])).
% 2.42/0.68  fof(f34,plain,(
% 2.42/0.68    ! [X0] : (((v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | (~v17_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.42/0.68    inference(ennf_transformation,[],[f26])).
% 2.42/0.68  fof(f26,plain,(
% 2.42/0.68    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 2.42/0.68    inference(pure_predicate_removal,[],[f4])).
% 2.42/0.68  fof(f4,axiom,(
% 2.42/0.68    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_lattices)).
% 2.42/0.68  fof(f79,plain,(
% 2.42/0.68    v17_lattices(sK0)),
% 2.42/0.68    inference(cnf_transformation,[],[f30])).
% 2.42/0.68  fof(f621,plain,(
% 2.42/0.68    k3_lattices(sK0,k5_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k5_lattices(sK0))),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f135,f77,f140,f145,f75,f122])).
% 2.42/0.68  fof(f122,plain,(
% 2.42/0.68    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f68])).
% 2.42/0.68  fof(f68,plain,(
% 2.42/0.68    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.68    inference(flattening,[],[f67])).
% 2.42/0.68  fof(f67,plain,(
% 2.42/0.68    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 2.42/0.68    inference(ennf_transformation,[],[f5])).
% 2.42/0.68  fof(f5,axiom,(
% 2.42/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 2.42/0.68  fof(f145,plain,(
% 2.42/0.68    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f77,f134,f93])).
% 2.42/0.68  fof(f93,plain,(
% 2.42/0.68    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f43])).
% 2.42/0.68  fof(f43,plain,(
% 2.42/0.68    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.68    inference(flattening,[],[f42])).
% 2.42/0.68  fof(f42,plain,(
% 2.42/0.68    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 2.42/0.68    inference(ennf_transformation,[],[f12])).
% 2.42/0.68  fof(f12,axiom,(
% 2.42/0.68    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 2.42/0.68  fof(f134,plain,(
% 2.42/0.68    l1_lattices(sK0)),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f80,f81])).
% 2.42/0.68  fof(f81,plain,(
% 2.42/0.68    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f31])).
% 2.42/0.68  fof(f31,plain,(
% 2.42/0.68    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 2.42/0.68    inference(ennf_transformation,[],[f15])).
% 2.42/0.68  fof(f15,axiom,(
% 2.42/0.68    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 2.42/0.68  fof(f140,plain,(
% 2.42/0.68    v4_lattices(sK0)),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f80,f78,f77,f87])).
% 2.42/0.68  fof(f87,plain,(
% 2.42/0.68    ( ! [X0] : (v4_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f37])).
% 2.42/0.68  fof(f37,plain,(
% 2.42/0.68    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.42/0.68    inference(flattening,[],[f36])).
% 2.42/0.68  fof(f36,plain,(
% 2.42/0.68    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.42/0.68    inference(ennf_transformation,[],[f28])).
% 2.42/0.68  fof(f28,plain,(
% 2.42/0.68    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.42/0.68    inference(pure_predicate_removal,[],[f27])).
% 2.42/0.68  fof(f27,plain,(
% 2.42/0.68    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.42/0.68    inference(pure_predicate_removal,[],[f2])).
% 2.42/0.68  fof(f2,axiom,(
% 2.42/0.68    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 2.42/0.68  fof(f135,plain,(
% 2.42/0.68    l2_lattices(sK0)),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f80,f82])).
% 2.42/0.68  fof(f82,plain,(
% 2.42/0.68    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f31])).
% 2.42/0.68  fof(f871,plain,(
% 2.42/0.68    k1_lattices(sK0,sK1,k5_lattices(sK0)) = k3_lattices(sK0,sK1,k5_lattices(sK0))),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f135,f77,f140,f145,f75,f123])).
% 2.42/0.68  fof(f123,plain,(
% 2.42/0.68    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f70])).
% 2.42/0.68  fof(f70,plain,(
% 2.42/0.68    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.68    inference(flattening,[],[f69])).
% 2.42/0.68  fof(f69,plain,(
% 2.42/0.68    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 2.42/0.68    inference(ennf_transformation,[],[f16])).
% 2.42/0.68  fof(f16,axiom,(
% 2.42/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 2.42/0.68  fof(f2036,plain,(
% 2.42/0.68    k1_lattices(sK0,sK1,k5_lattices(sK0)) = k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k6_lattices(sK0))),
% 2.42/0.68    inference(forward_demodulation,[],[f2035,f880])).
% 2.42/0.68  fof(f880,plain,(
% 2.42/0.68    k6_lattices(sK0) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))),
% 2.42/0.68    inference(forward_demodulation,[],[f877,f631])).
% 2.42/0.68  fof(f631,plain,(
% 2.42/0.68    k6_lattices(sK0) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK1))),
% 2.42/0.68    inference(forward_demodulation,[],[f629,f248])).
% 2.42/0.68  fof(f248,plain,(
% 2.42/0.68    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1)),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f79,f78,f80,f77,f75,f105])).
% 2.42/0.68  fof(f105,plain,(
% 2.42/0.68    ( ! [X0,X1] : (~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f55])).
% 2.42/0.68  fof(f55,plain,(
% 2.42/0.68    ! [X0] : (! [X1] : (k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.68    inference(flattening,[],[f54])).
% 2.42/0.68  fof(f54,plain,(
% 2.42/0.68    ! [X0] : (! [X1] : (k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.42/0.68    inference(ennf_transformation,[],[f23])).
% 2.42/0.68  fof(f23,axiom,(
% 2.42/0.68    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattices)).
% 2.42/0.68  fof(f629,plain,(
% 2.42/0.68    k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK1))),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f135,f77,f140,f149,f75,f122])).
% 2.42/0.68  fof(f149,plain,(
% 2.42/0.68    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f77,f80,f75,f121])).
% 2.42/0.68  fof(f121,plain,(
% 2.42/0.68    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f66])).
% 2.42/0.68  fof(f66,plain,(
% 2.42/0.68    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.68    inference(flattening,[],[f65])).
% 2.42/0.68  fof(f65,plain,(
% 2.42/0.68    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.42/0.68    inference(ennf_transformation,[],[f14])).
% 2.42/0.68  fof(f14,axiom,(
% 2.42/0.68    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).
% 2.42/0.68  fof(f877,plain,(
% 2.42/0.68    k1_lattices(sK0,sK1,k7_lattices(sK0,sK1)) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK1))),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f135,f77,f140,f149,f75,f123])).
% 2.42/0.68  fof(f2035,plain,(
% 2.42/0.68    k1_lattices(sK0,sK1,k5_lattices(sK0)) = k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k1_lattices(sK0,sK1,k7_lattices(sK0,sK1)))),
% 2.42/0.68    inference(forward_demodulation,[],[f2034,f1800])).
% 2.42/0.68  fof(f1800,plain,(
% 2.42/0.68    sK1 = k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1)),
% 2.42/0.68    inference(backward_demodulation,[],[f1142,f1797])).
% 2.42/0.68  fof(f1797,plain,(
% 2.42/0.68    sK1 = k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))),
% 2.42/0.68    inference(backward_demodulation,[],[f1117,f1796])).
% 2.42/0.68  fof(f1796,plain,(
% 2.42/0.68    sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))),
% 2.42/0.68    inference(forward_demodulation,[],[f1795,f911])).
% 2.42/0.68  fof(f911,plain,(
% 2.42/0.68    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0))),
% 2.42/0.68    inference(forward_demodulation,[],[f855,f641])).
% 2.42/0.68  fof(f641,plain,(
% 2.42/0.68    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0))),
% 2.42/0.68    inference(forward_demodulation,[],[f601,f188])).
% 2.42/0.68  fof(f188,plain,(
% 2.42/0.68    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,k7_lattices(sK0,sK1)))),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f139,f78,f80,f77,f152,f103])).
% 2.42/0.68  fof(f152,plain,(
% 2.42/0.68    m1_subset_1(k7_lattices(sK0,k7_lattices(sK0,sK1)),u1_struct_0(sK0))),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f77,f80,f149,f121])).
% 2.42/0.68  fof(f601,plain,(
% 2.42/0.68    k3_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,k7_lattices(sK0,sK1))) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0))),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f135,f77,f140,f145,f152,f122])).
% 2.42/0.68  fof(f855,plain,(
% 2.42/0.68    k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0))),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f135,f77,f140,f145,f152,f123])).
% 2.42/0.68  fof(f1795,plain,(
% 2.42/0.68    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0)))),
% 2.42/0.68    inference(forward_demodulation,[],[f1794,f1781])).
% 2.42/0.68  fof(f1781,plain,(
% 2.42/0.68    sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),k5_lattices(sK0))),
% 2.42/0.68    inference(forward_demodulation,[],[f1780,f360])).
% 2.42/0.68  fof(f360,plain,(
% 2.42/0.68    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))),
% 2.42/0.68    inference(forward_demodulation,[],[f350,f158])).
% 2.42/0.68  fof(f158,plain,(
% 2.42/0.68    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f135,f77,f138,f75,f130])).
% 2.42/0.68  fof(f130,plain,(
% 2.42/0.68    ( ! [X2,X0] : (~l2_lattices(X0) | v2_struct_0(X0) | ~v14_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k6_lattices(X0) = k1_lattices(X0,X2,k6_lattices(X0))) )),
% 2.42/0.68    inference(subsumption_resolution,[],[f126,f92])).
% 2.42/0.68  fof(f92,plain,(
% 2.42/0.68    ( ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f41])).
% 2.42/0.68  fof(f41,plain,(
% 2.42/0.68    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.68    inference(flattening,[],[f40])).
% 2.42/0.68  fof(f40,plain,(
% 2.42/0.68    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 2.42/0.68    inference(ennf_transformation,[],[f13])).
% 2.42/0.68  fof(f13,axiom,(
% 2.42/0.68    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).
% 2.42/0.68  fof(f126,plain,(
% 2.42/0.68    ( ! [X2,X0] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~v14_lattices(X0) | ~m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k6_lattices(X0) = k1_lattices(X0,X2,k6_lattices(X0))) )),
% 2.42/0.68    inference(equality_resolution,[],[f96])).
% 2.42/0.68  fof(f96,plain,(
% 2.42/0.68    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~v14_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X2,X1) = X1 | k6_lattices(X0) != X1) )),
% 2.42/0.68    inference(cnf_transformation,[],[f45])).
% 2.42/0.68  fof(f45,plain,(
% 2.42/0.68    ! [X0] : (! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.68    inference(flattening,[],[f44])).
% 2.42/0.68  fof(f44,plain,(
% 2.42/0.68    ! [X0] : ((! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 2.42/0.68    inference(ennf_transformation,[],[f9])).
% 2.42/0.68  fof(f9,axiom,(
% 2.42/0.68    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => (v14_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k6_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1))))))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattices)).
% 2.42/0.68  fof(f138,plain,(
% 2.42/0.68    v14_lattices(sK0)),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f80,f77,f137,f84])).
% 2.42/0.68  fof(f84,plain,(
% 2.42/0.68    ( ! [X0] : (v14_lattices(X0) | v2_struct_0(X0) | ~v15_lattices(X0) | ~l3_lattices(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f33])).
% 2.42/0.68  fof(f350,plain,(
% 2.42/0.68    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k6_lattices(sK0)))),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f77,f143,f80,f144,f75,f114])).
% 2.42/0.68  fof(f114,plain,(
% 2.42/0.68    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | v2_struct_0(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f61])).
% 2.42/0.68  fof(f61,plain,(
% 2.42/0.68    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.68    inference(flattening,[],[f60])).
% 2.42/0.68  fof(f60,plain,(
% 2.42/0.68    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.42/0.68    inference(ennf_transformation,[],[f11])).
% 2.42/0.68  fof(f11,axiom,(
% 2.42/0.68    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).
% 2.42/0.68  fof(f144,plain,(
% 2.42/0.68    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f77,f135,f92])).
% 2.42/0.68  fof(f143,plain,(
% 2.42/0.68    v9_lattices(sK0)),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f80,f78,f77,f90])).
% 2.42/0.68  fof(f90,plain,(
% 2.42/0.68    ( ! [X0] : (v9_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f37])).
% 2.42/0.68  fof(f1780,plain,(
% 2.42/0.68    k2_lattices(sK0,sK1,k6_lattices(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),k5_lattices(sK0))),
% 2.42/0.68    inference(forward_demodulation,[],[f1779,f902])).
% 2.42/0.68  fof(f902,plain,(
% 2.42/0.68    k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))),
% 2.42/0.68    inference(forward_demodulation,[],[f861,f247])).
% 2.42/0.68  fof(f247,plain,(
% 2.42/0.68    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f79,f78,f80,f77,f149,f105])).
% 2.42/0.68  fof(f861,plain,(
% 2.42/0.68    k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) = k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f135,f77,f140,f149,f152,f123])).
% 2.42/0.68  fof(f1779,plain,(
% 2.42/0.68    k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))) = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),k5_lattices(sK0))),
% 2.42/0.68    inference(forward_demodulation,[],[f1778,f1117])).
% 2.42/0.68  fof(f1778,plain,(
% 2.42/0.68    k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))) = k1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),k5_lattices(sK0))),
% 2.42/0.68    inference(forward_demodulation,[],[f1717,f1121])).
% 2.42/0.68  fof(f1121,plain,(
% 2.42/0.68    k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK1))),
% 2.42/0.68    inference(forward_demodulation,[],[f1118,f1032])).
% 2.42/0.68  fof(f1032,plain,(
% 2.42/0.68    k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK1))),
% 2.42/0.68    inference(forward_demodulation,[],[f1030,f258])).
% 2.42/0.68  fof(f258,plain,(
% 2.42/0.68    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f79,f78,f80,f77,f75,f106])).
% 2.42/0.68  fof(f106,plain,(
% 2.42/0.68    ( ! [X0,X1] : (~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f57])).
% 2.42/0.68  fof(f57,plain,(
% 2.42/0.68    ! [X0] : (! [X1] : (k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.68    inference(flattening,[],[f56])).
% 2.42/0.68  fof(f56,plain,(
% 2.42/0.68    ! [X0] : (! [X1] : (k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.42/0.68    inference(ennf_transformation,[],[f22])).
% 2.42/0.68  fof(f22,axiom,(
% 2.42/0.68    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattices)).
% 2.42/0.68  fof(f1030,plain,(
% 2.42/0.68    k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK1))),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f134,f77,f141,f149,f75,f124])).
% 2.42/0.68  fof(f124,plain,(
% 2.42/0.68    ( ! [X2,X0,X1] : (~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f72])).
% 2.42/0.68  fof(f72,plain,(
% 2.42/0.68    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.68    inference(flattening,[],[f71])).
% 2.42/0.68  fof(f71,plain,(
% 2.42/0.68    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.42/0.68    inference(ennf_transformation,[],[f6])).
% 2.42/0.68  fof(f6,axiom,(
% 2.42/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 2.42/0.68  fof(f141,plain,(
% 2.42/0.68    v6_lattices(sK0)),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f80,f78,f77,f88])).
% 2.42/0.68  fof(f88,plain,(
% 2.42/0.68    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f37])).
% 2.42/0.68  fof(f1118,plain,(
% 2.42/0.68    k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK1))),
% 2.42/0.68    inference(unit_resulting_resolution,[],[f134,f77,f141,f149,f75,f125])).
% 2.42/0.68  fof(f125,plain,(
% 2.42/0.68    ( ! [X2,X0,X1] : (~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f74])).
% 2.42/0.68  fof(f74,plain,(
% 2.42/0.68    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.68    inference(flattening,[],[f73])).
% 2.42/0.68  fof(f73,plain,(
% 2.42/0.68    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.42/0.68    inference(ennf_transformation,[],[f17])).
% 2.47/0.68  fof(f17,axiom,(
% 2.47/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 2.47/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 2.47/0.68  fof(f1717,plain,(
% 2.47/0.68    k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))) = k1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)))),
% 2.47/0.68    inference(unit_resulting_resolution,[],[f77,f136,f80,f149,f152,f75,f107])).
% 2.47/0.68  fof(f107,plain,(
% 2.47/0.68    ( ! [X2,X0,X3,X1] : (~v11_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | v2_struct_0(X0)) )),
% 2.47/0.68    inference(cnf_transformation,[],[f59])).
% 2.47/0.69  fof(f59,plain,(
% 2.47/0.69    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.47/0.69    inference(flattening,[],[f58])).
% 2.47/0.69  fof(f58,plain,(
% 2.47/0.69    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.47/0.69    inference(ennf_transformation,[],[f7])).
% 2.47/0.69  fof(f7,axiom,(
% 2.47/0.69    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v11_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)))))))),
% 2.47/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattices)).
% 2.47/0.69  fof(f136,plain,(
% 2.47/0.69    v11_lattices(sK0)),
% 2.47/0.69    inference(unit_resulting_resolution,[],[f80,f79,f77,f85])).
% 2.47/0.69  fof(f85,plain,(
% 2.47/0.69    ( ! [X0] : (v11_lattices(X0) | v2_struct_0(X0) | ~v17_lattices(X0) | ~l3_lattices(X0)) )),
% 2.47/0.69    inference(cnf_transformation,[],[f35])).
% 2.47/0.69  fof(f1794,plain,(
% 2.47/0.69    k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),k5_lattices(sK0))),
% 2.47/0.69    inference(forward_demodulation,[],[f1793,f1117])).
% 2.47/0.69  fof(f1793,plain,(
% 2.47/0.69    k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0))) = k1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),k5_lattices(sK0))),
% 2.47/0.69    inference(forward_demodulation,[],[f1713,f176])).
% 2.47/0.69  fof(f176,plain,(
% 2.47/0.69    k5_lattices(sK0) = k2_lattices(sK0,sK1,k5_lattices(sK0))),
% 2.47/0.69    inference(unit_resulting_resolution,[],[f134,f77,f139,f75,f132])).
% 2.47/0.69  fof(f132,plain,(
% 2.47/0.69    ( ! [X2,X0] : (~l1_lattices(X0) | v2_struct_0(X0) | ~v13_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0))) )),
% 2.47/0.69    inference(subsumption_resolution,[],[f128,f93])).
% 2.47/0.69  fof(f128,plain,(
% 2.47/0.69    ( ! [X2,X0] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~v13_lattices(X0) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0))) )),
% 2.47/0.69    inference(equality_resolution,[],[f100])).
% 2.47/0.69  fof(f100,plain,(
% 2.47/0.69    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X2,X1) = X1 | k5_lattices(X0) != X1) )),
% 2.47/0.69    inference(cnf_transformation,[],[f47])).
% 2.47/0.69  fof(f47,plain,(
% 2.47/0.69    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.47/0.69    inference(flattening,[],[f46])).
% 2.47/0.69  fof(f46,plain,(
% 2.47/0.69    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 2.47/0.69    inference(ennf_transformation,[],[f8])).
% 2.47/0.69  fof(f8,axiom,(
% 2.47/0.69    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 2.47/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 2.47/0.69  fof(f1713,plain,(
% 2.47/0.69    k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k5_lattices(sK0))) = k1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),k2_lattices(sK0,sK1,k5_lattices(sK0)))),
% 2.47/0.69    inference(unit_resulting_resolution,[],[f77,f136,f80,f145,f152,f75,f107])).
% 2.47/0.69  fof(f1117,plain,(
% 2.47/0.69    k2_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))),
% 2.47/0.69    inference(unit_resulting_resolution,[],[f134,f77,f141,f152,f75,f125])).
% 2.47/0.69  fof(f1142,plain,(
% 2.47/0.69    k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))),
% 2.47/0.69    inference(forward_demodulation,[],[f1103,f1029])).
% 2.47/0.69  fof(f1029,plain,(
% 2.47/0.69    k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))),
% 2.47/0.69    inference(unit_resulting_resolution,[],[f134,f77,f141,f152,f75,f124])).
% 2.47/0.69  fof(f1103,plain,(
% 2.47/0.69    k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1)),
% 2.47/0.69    inference(unit_resulting_resolution,[],[f134,f77,f141,f75,f152,f125])).
% 2.47/0.69  fof(f2034,plain,(
% 2.47/0.69    k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))) = k1_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1),k5_lattices(sK0))),
% 2.47/0.69    inference(forward_demodulation,[],[f1657,f1144])).
% 2.47/0.69  fof(f1144,plain,(
% 2.47/0.69    k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))),
% 2.47/0.69    inference(forward_demodulation,[],[f1102,f257])).
% 2.47/0.69  fof(f257,plain,(
% 2.47/0.69    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))),
% 2.47/0.69    inference(unit_resulting_resolution,[],[f79,f78,f80,f77,f149,f106])).
% 2.47/0.69  fof(f1102,plain,(
% 2.47/0.69    k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) = k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))),
% 2.47/0.69    inference(unit_resulting_resolution,[],[f134,f77,f141,f149,f152,f125])).
% 2.47/0.69  fof(f1657,plain,(
% 2.47/0.69    k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))) = k1_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1),k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)))),
% 2.47/0.69    inference(unit_resulting_resolution,[],[f77,f136,f80,f149,f75,f152,f107])).
% 2.47/0.69  fof(f364,plain,(
% 2.47/0.69    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k6_lattices(sK0))),
% 2.47/0.69    inference(forward_demodulation,[],[f330,f161])).
% 2.47/0.69  fof(f161,plain,(
% 2.47/0.69    k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k6_lattices(sK0))),
% 2.47/0.69    inference(unit_resulting_resolution,[],[f77,f135,f138,f152,f130])).
% 2.47/0.69  fof(f330,plain,(
% 2.47/0.69    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k2_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k6_lattices(sK0)))),
% 2.47/0.69    inference(unit_resulting_resolution,[],[f77,f143,f80,f144,f152,f114])).
% 2.47/0.69  % SZS output end Proof for theBenchmark
% 2.47/0.69  % (31076)------------------------------
% 2.47/0.69  % (31076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.47/0.69  % (31076)Termination reason: Refutation
% 2.47/0.69  
% 2.47/0.69  % (31076)Memory used [KB]: 2558
% 2.47/0.69  % (31076)Time elapsed: 0.216 s
% 2.47/0.69  % (31076)------------------------------
% 2.47/0.69  % (31076)------------------------------
% 2.47/0.69  % (31068)Success in time 0.317 s
%------------------------------------------------------------------------------
