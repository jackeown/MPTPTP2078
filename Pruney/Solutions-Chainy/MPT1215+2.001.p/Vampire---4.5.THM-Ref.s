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
% DateTime   : Thu Dec  3 13:10:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 275 expanded)
%              Number of leaves         :    7 (  47 expanded)
%              Depth                    :   22
%              Number of atoms          :  300 (1417 expanded)
%              Number of equality atoms :   37 ( 185 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1024,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1023,f29])).

fof(f29,plain,(
    k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) != k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_lattices(X0,k3_lattices(X0,X1,X2)) != k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_lattices(X0,k3_lattices(X0,X1,X2)) != k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_lattices)).

fof(f1023,plain,(
    k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) ),
    inference(forward_demodulation,[],[f1022,f399])).

fof(f399,plain,(
    k3_lattices(sK0,sK1,sK2) = k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))) ),
    inference(forward_demodulation,[],[f389,f57])).

fof(f57,plain,(
    sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f56,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,
    ( v2_struct_0(sK0)
    | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f55,f34])).

fof(f34,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f54,f33])).

fof(f33,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,
    ( ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f47,f32])).

fof(f32,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,
    ( ~ v10_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) ),
    inference(resolution,[],[f28,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).

fof(f28,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f389,plain,(
    k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))) = k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK2))) ),
    inference(resolution,[],[f116,f50])).

fof(f50,plain,(
    m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f49,f31])).

fof(f49,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f45,f34])).

fof(f45,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f28,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f116,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),X1)) = k3_lattices(sK0,sK1,k7_lattices(sK0,X1)) ) ),
    inference(forward_demodulation,[],[f115,f74])).

fof(f74,plain,(
    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f73,f31])).

fof(f73,plain,
    ( v2_struct_0(sK0)
    | sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f72,f34])).

fof(f72,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f71,f33])).

fof(f71,plain,
    ( ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f64,f32])).

fof(f64,plain,
    ( ~ v10_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    inference(resolution,[],[f30,f36])).

fof(f30,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f115,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),X1)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f114,f31])).

fof(f114,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),X1)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f113,f34])).

fof(f113,plain,(
    ! [X1] :
      ( ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),X1)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f112,f33])).

fof(f112,plain,(
    ! [X1] :
      ( ~ v17_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),X1)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f101,f32])).

fof(f101,plain,(
    ! [X1] :
      ( ~ v10_lattices(sK0)
      | ~ v17_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),X1)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,X1)) ) ),
    inference(resolution,[],[f67,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattices)).

fof(f67,plain,(
    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f66,f31])).

fof(f66,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f62,f34])).

fof(f62,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f30,f38])).

fof(f1022,plain,(
    k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))) ),
    inference(subsumption_resolution,[],[f1021,f31])).

fof(f1021,plain,
    ( v2_struct_0(sK0)
    | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))) ),
    inference(subsumption_resolution,[],[f1020,f34])).

fof(f1020,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))) ),
    inference(subsumption_resolution,[],[f1019,f33])).

fof(f1019,plain,
    ( ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))) ),
    inference(subsumption_resolution,[],[f1007,f32])).

fof(f1007,plain,
    ( ~ v10_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))) ),
    inference(resolution,[],[f707,f36])).

fof(f707,plain,(
    m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f107,f50])).

fof(f107,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,sK1),X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f106,f31])).

fof(f106,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,sK1),X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f105,f44])).

fof(f44,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f34,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f105,plain,(
    ! [X0] :
      ( ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,sK1),X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f99,f43])).

fof(f43,plain,(
    v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f42,f34])).

fof(f42,plain,
    ( ~ l3_lattices(sK0)
    | v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f41,f31])).

fof(f41,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v6_lattices(sK0) ),
    inference(resolution,[],[f32,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v7_lattices(X0)
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

fof(f99,plain,(
    ! [X0] :
      ( ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,sK1),X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f67,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (32078)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (32070)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  % (32075)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.49  % (32089)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.49  % (32080)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.50  % (32074)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (32068)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (32072)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (32084)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.50  % (32067)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (32073)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (32076)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (32069)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (32083)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (32066)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (32069)Refutation not found, incomplete strategy% (32069)------------------------------
% 0.21/0.51  % (32069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32069)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32069)Memory used [KB]: 10618
% 0.21/0.51  % (32069)Time elapsed: 0.092 s
% 0.21/0.51  % (32069)------------------------------
% 0.21/0.51  % (32069)------------------------------
% 0.21/0.52  % (32085)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.52  % (32086)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.52  % (32088)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.52  % (32091)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.52  % (32071)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.53  % (32077)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.53  % (32082)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.53  % (32092)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.54  % (32079)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.56  % (32092)Refutation not found, incomplete strategy% (32092)------------------------------
% 0.21/0.56  % (32092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32092)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32092)Memory used [KB]: 10618
% 0.21/0.56  % (32092)Time elapsed: 0.149 s
% 0.21/0.56  % (32092)------------------------------
% 0.21/0.56  % (32092)------------------------------
% 0.21/0.56  % (32088)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f1024,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(subsumption_resolution,[],[f1023,f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) != k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) != k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) != k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,negated_conjecture,(
% 0.21/0.56    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 0.21/0.56    inference(negated_conjecture,[],[f7])).
% 0.21/0.56  fof(f7,conjecture,(
% 0.21/0.56    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_lattices)).
% 0.21/0.56  fof(f1023,plain,(
% 0.21/0.56    k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))),
% 0.21/0.56    inference(forward_demodulation,[],[f1022,f399])).
% 0.21/0.56  fof(f399,plain,(
% 0.21/0.56    k3_lattices(sK0,sK1,sK2) = k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))),
% 0.21/0.56    inference(forward_demodulation,[],[f389,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))),
% 0.21/0.56    inference(subsumption_resolution,[],[f56,f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ~v2_struct_0(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    v2_struct_0(sK0) | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))),
% 0.21/0.56    inference(subsumption_resolution,[],[f55,f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    l3_lattices(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ~l3_lattices(sK0) | v2_struct_0(sK0) | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))),
% 0.21/0.56    inference(subsumption_resolution,[],[f54,f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    v17_lattices(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ~v17_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))),
% 0.21/0.56    inference(subsumption_resolution,[],[f47,f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    v10_lattices(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ~v10_lattices(sK0) | ~v17_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))),
% 0.21/0.56    inference(resolution,[],[f28,f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v10_lattices(X0) | ~v17_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | k7_lattices(X0,k7_lattices(X0,X1)) = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f389,plain,(
% 0.21/0.56    k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))) = k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK2)))),
% 0.21/0.56    inference(resolution,[],[f116,f50])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 0.21/0.56    inference(subsumption_resolution,[],[f49,f31])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    v2_struct_0(sK0) | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 0.21/0.56    inference(subsumption_resolution,[],[f45,f34])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ~l3_lattices(sK0) | v2_struct_0(sK0) | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 0.21/0.56    inference(resolution,[],[f28,f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0) | m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),X1)) = k3_lattices(sK0,sK1,k7_lattices(sK0,X1))) )),
% 0.21/0.56    inference(forward_demodulation,[],[f115,f74])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))),
% 0.21/0.56    inference(subsumption_resolution,[],[f73,f31])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    v2_struct_0(sK0) | sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))),
% 0.21/0.56    inference(subsumption_resolution,[],[f72,f34])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    ~l3_lattices(sK0) | v2_struct_0(sK0) | sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))),
% 0.21/0.56    inference(subsumption_resolution,[],[f71,f33])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ~v17_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))),
% 0.21/0.56    inference(subsumption_resolution,[],[f64,f32])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ~v10_lattices(sK0) | ~v17_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))),
% 0.21/0.56    inference(resolution,[],[f30,f36])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f115,plain,(
% 0.21/0.56    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),X1)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,X1))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f114,f31])).
% 0.21/0.56  fof(f114,plain,(
% 0.21/0.56    ( ! [X1] : (v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),X1)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,X1))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f113,f34])).
% 0.21/0.56  fof(f113,plain,(
% 0.21/0.56    ( ! [X1] : (~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),X1)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,X1))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f112,f33])).
% 0.21/0.56  fof(f112,plain,(
% 0.21/0.56    ( ! [X1] : (~v17_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),X1)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,X1))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f101,f32])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    ( ! [X1] : (~v10_lattices(sK0) | ~v17_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),X1)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,X1))) )),
% 0.21/0.56    inference(resolution,[],[f67,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v10_lattices(X0) | ~v17_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattices)).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.56    inference(subsumption_resolution,[],[f66,f31])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    v2_struct_0(sK0) | m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.56    inference(subsumption_resolution,[],[f62,f34])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ~l3_lattices(sK0) | v2_struct_0(sK0) | m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.56    inference(resolution,[],[f30,f38])).
% 0.21/0.56  fof(f1022,plain,(
% 0.21/0.56    k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))))),
% 0.21/0.56    inference(subsumption_resolution,[],[f1021,f31])).
% 0.21/0.56  fof(f1021,plain,(
% 0.21/0.56    v2_struct_0(sK0) | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))))),
% 0.21/0.56    inference(subsumption_resolution,[],[f1020,f34])).
% 0.21/0.56  fof(f1020,plain,(
% 0.21/0.56    ~l3_lattices(sK0) | v2_struct_0(sK0) | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))))),
% 0.21/0.56    inference(subsumption_resolution,[],[f1019,f33])).
% 0.21/0.56  fof(f1019,plain,(
% 0.21/0.56    ~v17_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))))),
% 0.21/0.56    inference(subsumption_resolution,[],[f1007,f32])).
% 0.21/0.56  fof(f1007,plain,(
% 0.21/0.56    ~v10_lattices(sK0) | ~v17_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))))),
% 0.21/0.56    inference(resolution,[],[f707,f36])).
% 0.21/0.56  fof(f707,plain,(
% 0.21/0.56    m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)),u1_struct_0(sK0))),
% 0.21/0.56    inference(resolution,[],[f107,f50])).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,sK1),X0),u1_struct_0(sK0))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f106,f31])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,sK1),X0),u1_struct_0(sK0))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f105,f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    l1_lattices(sK0)),
% 0.21/0.56    inference(resolution,[],[f34,f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ( ! [X0] : (~l3_lattices(X0) | l1_lattices(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,plain,(
% 0.21/0.56    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 0.21/0.56    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    ( ! [X0] : (~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,sK1),X0),u1_struct_0(sK0))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f99,f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    v6_lattices(sK0)),
% 0.21/0.56    inference(subsumption_resolution,[],[f42,f34])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ~l3_lattices(sK0) | v6_lattices(sK0)),
% 0.21/0.56    inference(subsumption_resolution,[],[f41,f31])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    v2_struct_0(sK0) | ~l3_lattices(sK0) | v6_lattices(sK0)),
% 0.21/0.56    inference(resolution,[],[f32,f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v6_lattices(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0] : ((v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.56    inference(flattening,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0] : (((v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.56    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.56    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.56    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.56    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.56  fof(f10,plain,(
% 0.21/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.56    inference(pure_predicate_removal,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    ( ! [X0] : (~v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,sK1),X0),u1_struct_0(sK0))) )),
% 0.21/0.56    inference(resolution,[],[f67,f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (32088)------------------------------
% 0.21/0.56  % (32088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32088)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (32088)Memory used [KB]: 6780
% 0.21/0.56  % (32088)Time elapsed: 0.148 s
% 0.21/0.56  % (32088)------------------------------
% 0.21/0.56  % (32088)------------------------------
% 1.68/0.57  % (32062)Success in time 0.211 s
%------------------------------------------------------------------------------
