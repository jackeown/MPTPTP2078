%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 257 expanded)
%              Number of leaves         :    7 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  239 (1282 expanded)
%              Number of equality atoms :   38 (  57 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f291,plain,(
    $false ),
    inference(subsumption_resolution,[],[f290,f269])).

fof(f269,plain,(
    m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f157,f268])).

fof(f268,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1) ),
    inference(forward_demodulation,[],[f242,f234])).

fof(f234,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) ),
    inference(resolution,[],[f84,f24])).

fof(f24,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).

fof(f84,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2,X4) = k4_lattices(sK0,X4,sK2) ) ),
    inference(subsumption_resolution,[],[f83,f56])).

fof(f56,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f28,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f28,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f83,plain,(
    ! [X4] :
      ( ~ l1_lattices(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2,X4) = k4_lattices(sK0,X4,sK2) ) ),
    inference(subsumption_resolution,[],[f82,f26])).

fof(f26,plain,(
    v6_lattices(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f82,plain,(
    ! [X4] :
      ( ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2,X4) = k4_lattices(sK0,X4,sK2) ) ),
    inference(subsumption_resolution,[],[f66,f25])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X4] :
      ( v2_struct_0(sK0)
      | ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2,X4) = k4_lattices(sK0,X4,sK2) ) ),
    inference(resolution,[],[f22,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f22,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f242,plain,(
    k4_lattices(sK0,sK2,sK1) = k2_lattices(sK0,sK2,sK1) ),
    inference(resolution,[],[f87,f24])).

fof(f87,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2,X6) = k2_lattices(sK0,sK2,X6) ) ),
    inference(subsumption_resolution,[],[f86,f56])).

fof(f86,plain,(
    ! [X6] :
      ( ~ l1_lattices(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2,X6) = k2_lattices(sK0,sK2,X6) ) ),
    inference(subsumption_resolution,[],[f85,f26])).

fof(f85,plain,(
    ! [X6] :
      ( ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2,X6) = k2_lattices(sK0,sK2,X6) ) ),
    inference(subsumption_resolution,[],[f68,f25])).

fof(f68,plain,(
    ! [X6] :
      ( v2_struct_0(sK0)
      | ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2,X6) = k2_lattices(sK0,sK2,X6) ) ),
    inference(resolution,[],[f22,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f157,plain,(
    m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f92,f24])).

fof(f92,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,u1_struct_0(sK0))
      | m1_subset_1(k2_lattices(sK0,sK2,X8),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f91,f56])).

fof(f91,plain,(
    ! [X8] :
      ( ~ l1_lattices(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | m1_subset_1(k2_lattices(sK0,sK2,X8),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f70,f25])).

fof(f70,plain,(
    ! [X8] :
      ( v2_struct_0(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | m1_subset_1(k2_lattices(sK0,sK2,X8),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f22,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattices)).

fof(f290,plain,(
    ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(trivial_inequality_removal,[],[f289])).

fof(f289,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f143,f288])).

fof(f288,plain,(
    sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) ),
    inference(forward_demodulation,[],[f283,f268])).

fof(f283,plain,(
    sK1 = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f97,f24])).

fof(f97,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,sK2,X10),X10) = X10 ) ),
    inference(subsumption_resolution,[],[f96,f27])).

fof(f27,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f96,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,sK2,X10),X10) = X10
      | ~ v8_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f95,f28])).

fof(f95,plain,(
    ! [X10] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,sK2,X10),X10) = X10
      | ~ v8_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f72,f25])).

fof(f72,plain,(
    ! [X10] :
      ( v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,sK2,X10),X10) = X10
      | ~ v8_lattices(sK0) ) ),
    inference(resolution,[],[f22,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
      | ~ v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f143,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | sK1 != k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f142,f24])).

fof(f142,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 != k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f141,f57])).

fof(f57,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f28,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f141,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 != k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f140,f25])).

fof(f140,plain,
    ( v2_struct_0(sK0)
    | ~ l2_lattices(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 != k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) ),
    inference(resolution,[],[f23,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) != X2
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f23,plain,(
    ~ r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:58:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (14085)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.49  % (14085)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f291,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f290,f269])).
% 0.22/0.49  fof(f269,plain,(
% 0.22/0.49    m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.22/0.49    inference(backward_demodulation,[],[f157,f268])).
% 0.22/0.49  fof(f268,plain,(
% 0.22/0.49    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1)),
% 0.22/0.49    inference(forward_demodulation,[],[f242,f234])).
% 0.22/0.49  fof(f234,plain,(
% 0.22/0.49    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)),
% 0.22/0.49    inference(resolution,[],[f84,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (~r1_lattices(X0,k4_lattices(X0,X1,X2),X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (~r1_lattices(X0,k4_lattices(X0,X1,X2),X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 0.22/0.49    inference(negated_conjecture,[],[f7])).
% 0.22/0.49  fof(f7,conjecture,(
% 0.22/0.49    ! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | k4_lattices(sK0,sK2,X4) = k4_lattices(sK0,X4,sK2)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f83,f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    l1_lattices(sK0)),
% 0.22/0.49    inference(resolution,[],[f28,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0] : (~l3_lattices(X0) | l1_lattices(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    l3_lattices(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ( ! [X4] : (~l1_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k4_lattices(sK0,sK2,X4) = k4_lattices(sK0,X4,sK2)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f82,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    v6_lattices(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ( ! [X4] : (~v6_lattices(sK0) | ~l1_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k4_lattices(sK0,sK2,X4) = k4_lattices(sK0,X4,sK2)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f66,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X4] : (v2_struct_0(sK0) | ~v6_lattices(sK0) | ~l1_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k4_lattices(sK0,sK2,X4) = k4_lattices(sK0,X4,sK2)) )),
% 0.22/0.50    inference(resolution,[],[f22,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f242,plain,(
% 0.22/0.50    k4_lattices(sK0,sK2,sK1) = k2_lattices(sK0,sK2,sK1)),
% 0.22/0.50    inference(resolution,[],[f87,f24])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ( ! [X6] : (~m1_subset_1(X6,u1_struct_0(sK0)) | k4_lattices(sK0,sK2,X6) = k2_lattices(sK0,sK2,X6)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f86,f56])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ( ! [X6] : (~l1_lattices(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | k4_lattices(sK0,sK2,X6) = k2_lattices(sK0,sK2,X6)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f85,f26])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X6] : (~v6_lattices(sK0) | ~l1_lattices(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | k4_lattices(sK0,sK2,X6) = k2_lattices(sK0,sK2,X6)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f68,f25])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X6] : (v2_struct_0(sK0) | ~v6_lattices(sK0) | ~l1_lattices(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | k4_lattices(sK0,sK2,X6) = k2_lattices(sK0,sK2,X6)) )),
% 0.22/0.50    inference(resolution,[],[f22,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0))),
% 0.22/0.50    inference(resolution,[],[f92,f24])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    ( ! [X8] : (~m1_subset_1(X8,u1_struct_0(sK0)) | m1_subset_1(k2_lattices(sK0,sK2,X8),u1_struct_0(sK0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f91,f56])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ( ! [X8] : (~l1_lattices(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | m1_subset_1(k2_lattices(sK0,sK2,X8),u1_struct_0(sK0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f70,f25])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X8] : (v2_struct_0(sK0) | ~l1_lattices(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | m1_subset_1(k2_lattices(sK0,sK2,X8),u1_struct_0(sK0))) )),
% 0.22/0.50    inference(resolution,[],[f22,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattices)).
% 0.22/0.50  fof(f290,plain,(
% 0.22/0.50    ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f289])).
% 0.22/0.50  fof(f289,plain,(
% 0.22/0.50    sK1 != sK1 | ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.22/0.50    inference(backward_demodulation,[],[f143,f288])).
% 0.22/0.50  fof(f288,plain,(
% 0.22/0.50    sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)),
% 0.22/0.50    inference(forward_demodulation,[],[f283,f268])).
% 0.22/0.50  fof(f283,plain,(
% 0.22/0.50    sK1 = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1)),
% 0.22/0.50    inference(resolution,[],[f97,f24])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ( ! [X10] : (~m1_subset_1(X10,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,sK2,X10),X10) = X10) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f96,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    v8_lattices(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ( ! [X10] : (~m1_subset_1(X10,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,sK2,X10),X10) = X10 | ~v8_lattices(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f95,f28])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ( ! [X10] : (~l3_lattices(sK0) | ~m1_subset_1(X10,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,sK2,X10),X10) = X10 | ~v8_lattices(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f72,f25])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X10] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X10,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,sK2,X10),X10) = X10 | ~v8_lattices(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f22,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~v8_lattices(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | sK1 != k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)),
% 0.22/0.50    inference(subsumption_resolution,[],[f142,f24])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 != k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)),
% 0.22/0.50    inference(subsumption_resolution,[],[f141,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    l2_lattices(sK0)),
% 0.22/0.50    inference(resolution,[],[f28,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0] : (~l3_lattices(X0) | l2_lattices(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    ~l2_lattices(sK0) | ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 != k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)),
% 0.22/0.50    inference(subsumption_resolution,[],[f140,f25])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    v2_struct_0(sK0) | ~l2_lattices(sK0) | ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 != k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)),
% 0.22/0.50    inference(resolution,[],[f23,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) != X2 | r1_lattices(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ~r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (14085)------------------------------
% 0.22/0.50  % (14085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (14085)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (14085)Memory used [KB]: 1791
% 0.22/0.50  % (14085)Time elapsed: 0.078 s
% 0.22/0.50  % (14085)------------------------------
% 0.22/0.50  % (14085)------------------------------
% 0.22/0.50  % (14063)Success in time 0.138 s
%------------------------------------------------------------------------------
