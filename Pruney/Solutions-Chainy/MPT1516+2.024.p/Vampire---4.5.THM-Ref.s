%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:52 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  164 (3200 expanded)
%              Number of leaves         :   13 ( 566 expanded)
%              Depth                    :   52
%              Number of atoms          :  758 (21121 expanded)
%              Number of equality atoms :  119 (2252 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f426,plain,(
    $false ),
    inference(subsumption_resolution,[],[f425,f361])).

fof(f361,plain,(
    m1_subset_1(sK2(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f360,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
          & l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).

fof(f360,plain,
    ( m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f357,f54])).

fof(f54,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f357,plain,
    ( m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f87,f346])).

fof(f346,plain,(
    k15_lattice3(sK0,k1_xboole_0) = sK2(sK0) ),
    inference(subsumption_resolution,[],[f345,f54])).

fof(f345,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = sK2(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f344,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f344,plain,
    ( ~ l1_lattices(sK0)
    | k15_lattice3(sK0,k1_xboole_0) = sK2(sK0) ),
    inference(subsumption_resolution,[],[f343,f273])).

fof(f273,plain,(
    v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f272,f51])).

fof(f272,plain,
    ( v13_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f271,f54])).

fof(f271,plain,
    ( v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f268,f87])).

fof(f268,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f267,f54])).

fof(f267,plain,
    ( v13_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f266,f56])).

fof(f266,plain,
    ( ~ l1_lattices(sK0)
    | v13_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f265,f51])).

fof(f265,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v13_lattices(sK0) ),
    inference(resolution,[],[f258,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).

fof(f258,plain,
    ( ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | v13_lattices(sK0) ),
    inference(trivial_inequality_removal,[],[f257])).

fof(f257,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0)
    | v13_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) ),
    inference(superposition,[],[f218,f252])).

fof(f252,plain,(
    ! [X2] :
      ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f251,f51])).

fof(f251,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f250,f54])).

fof(f250,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X2)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f243,f87])).

fof(f243,plain,(
    ! [X4] :
      ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X4) ) ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,(
    ! [X4] :
      ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f236,f160])).

fof(f160,plain,(
    ! [X0] :
      ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f143,f159])).

fof(f159,plain,(
    ! [X2] :
      ( k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f124,f54])).

fof(f124,plain,(
    ! [X2] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2 ) ),
    inference(subsumption_resolution,[],[f123,f51])).

fof(f123,plain,(
    ! [X2] :
      ( v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2 ) ),
    inference(subsumption_resolution,[],[f111,f52])).

fof(f52,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f111,plain,(
    ! [X2] :
      ( ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2 ) ),
    inference(resolution,[],[f53,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattice3)).

fof(f53,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f143,plain,(
    ! [X0] : r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) ),
    inference(resolution,[],[f142,f55])).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f142,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,X5)
      | r3_lattices(sK0,k15_lattice3(sK0,X4),k15_lattice3(sK0,X5)) ) ),
    inference(subsumption_resolution,[],[f128,f54])).

fof(f128,plain,(
    ! [X4,X5] :
      ( ~ l3_lattices(sK0)
      | ~ r1_tarski(X4,X5)
      | r3_lattices(sK0,k15_lattice3(sK0,X4),k15_lattice3(sK0,X5)) ) ),
    inference(subsumption_resolution,[],[f127,f51])).

fof(f127,plain,(
    ! [X4,X5] :
      ( v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ r1_tarski(X4,X5)
      | r3_lattices(sK0,k15_lattice3(sK0,X4),k15_lattice3(sK0,X5)) ) ),
    inference(subsumption_resolution,[],[f113,f52])).

fof(f113,plain,(
    ! [X4,X5] :
      ( ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ r1_tarski(X4,X5)
      | r3_lattices(sK0,k15_lattice3(sK0,X4),k15_lattice3(sK0,X5)) ) ),
    inference(resolution,[],[f53,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ r1_tarski(X1,X2)
      | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_lattice3)).

fof(f236,plain,(
    ! [X2,X3] :
      ( ~ r3_lattices(sK0,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k2_lattices(sK0,X2,X3) = X2 ) ),
    inference(subsumption_resolution,[],[f235,f54])).

fof(f235,plain,(
    ! [X2,X3] :
      ( k2_lattices(sK0,X2,X3) = X2
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X2,X3)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f234,f52])).

fof(f234,plain,(
    ! [X2,X3] :
      ( k2_lattices(sK0,X2,X3) = X2
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X2,X3)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f233,f51])).

fof(f233,plain,(
    ! [X2,X3] :
      ( k2_lattices(sK0,X2,X3) = X2
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X2,X3)
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f230,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f230,plain,(
    ! [X2,X3] :
      ( ~ v6_lattices(sK0)
      | k2_lattices(sK0,X3,X2) = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f229])).

fof(f229,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k2_lattices(sK0,X3,X2) = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | ~ r3_lattices(sK0,X3,X2) ) ),
    inference(resolution,[],[f227,f193])).

fof(f193,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | ~ r3_lattices(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f192,f54])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ v6_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X1)
      | ~ r3_lattices(sK0,X0,X1)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f191,f52])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ v6_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X1)
      | ~ r3_lattices(sK0,X0,X1)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f190,f51])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ v6_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X1)
      | ~ r3_lattices(sK0,X0,X1)
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f189,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X1)
      | ~ r3_lattices(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f188,f54])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X1)
      | ~ r3_lattices(sK0,X0,X1)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f187,f52])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X1)
      | ~ r3_lattices(sK0,X0,X1)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f186,f51])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X1)
      | ~ r3_lattices(sK0,X0,X1)
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f185,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f185,plain,(
    ! [X2,X3] :
      ( ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r1_lattices(sK0,X2,X3)
      | ~ r3_lattices(sK0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f104,f54])).

fof(f104,plain,(
    ! [X2,X3] :
      ( ~ v6_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r1_lattices(sK0,X2,X3)
      | ~ r3_lattices(sK0,X2,X3) ) ),
    inference(resolution,[],[f51,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f46,plain,(
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

fof(f227,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f226,f54])).

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = X0
      | ~ r1_lattices(sK0,X0,X1)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f225,f52])).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = X0
      | ~ r1_lattices(sK0,X0,X1)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f224,f51])).

fof(f224,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = X0
      | ~ r1_lattices(sK0,X0,X1)
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f223,f62])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ v8_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = X0
      | ~ r1_lattices(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f222,f54])).

fof(f222,plain,(
    ! [X0,X1] :
      ( ~ v8_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = X0
      | ~ r1_lattices(sK0,X0,X1)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f221,f52])).

fof(f221,plain,(
    ! [X0,X1] :
      ( ~ v8_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = X0
      | ~ r1_lattices(sK0,X0,X1)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f220,f51])).

fof(f220,plain,(
    ! [X0,X1] :
      ( ~ v8_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = X0
      | ~ r1_lattices(sK0,X0,X1)
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f219,f63])).

fof(f219,plain,(
    ! [X10,X9] :
      ( ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | k2_lattices(sK0,X9,X10) = X9
      | ~ r1_lattices(sK0,X9,X10) ) ),
    inference(subsumption_resolution,[],[f108,f54])).

fof(f108,plain,(
    ! [X10,X9] :
      ( ~ v8_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | k2_lattices(sK0,X9,X10) = X9
      | ~ r1_lattices(sK0,X9,X10) ) ),
    inference(resolution,[],[f51,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f218,plain,(
    ! [X0] :
      ( k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
      | v13_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f217,f54])).

fof(f217,plain,(
    ! [X0] :
      ( v13_lattices(sK0)
      | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f216,f56])).

fof(f216,plain,(
    ! [X2] :
      ( ~ l1_lattices(sK0)
      | v13_lattices(sK0)
      | k2_lattices(sK0,X2,sK3(sK0,X2)) != X2
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f215,f51])).

fof(f215,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v13_lattices(sK0)
      | k2_lattices(sK0,X2,sK3(sK0,X2)) != X2
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v13_lattices(sK0)
      | k2_lattices(sK0,X2,sK3(sK0,X2)) != X2
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | v13_lattices(sK0) ) ),
    inference(resolution,[],[f211,f75])).

fof(f211,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3(sK0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v13_lattices(sK0)
      | k2_lattices(sK0,X1,sK3(sK0,X1)) != X1 ) ),
    inference(duplicate_literal_removal,[],[f210])).

fof(f210,plain,(
    ! [X1] :
      ( k2_lattices(sK0,X1,sK3(sK0,X1)) != X1
      | k2_lattices(sK0,X1,sK3(sK0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v13_lattices(sK0)
      | ~ m1_subset_1(sK3(sK0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f197,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f171,f54])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f170,f52])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f169,f51])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f168,f60])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ v6_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f167,f54])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0)
      | ~ v6_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f105,f56])).

fof(f105,plain,(
    ! [X4,X5] :
      ( ~ l1_lattices(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | k2_lattices(sK0,X4,X5) = k2_lattices(sK0,X5,X4)
      | ~ v6_lattices(sK0) ) ),
    inference(resolution,[],[f51,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
      | ~ v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).

fof(f197,plain,(
    ! [X0] :
      ( k2_lattices(sK0,sK3(sK0,X0),X0) != X0
      | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v13_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f196,f54])).

fof(f196,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
      | k2_lattices(sK0,sK3(sK0,X0),X0) != X0
      | v13_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f106,f56])).

fof(f106,plain,(
    ! [X6] :
      ( ~ l1_lattices(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6
      | k2_lattices(sK0,sK3(sK0,X6),X6) != X6
      | v13_lattices(sK0) ) ),
    inference(resolution,[],[f51,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_lattices(X0,X1,sK3(X0,X1)) != X1
      | k2_lattices(X0,sK3(X0,X1),X1) != X1
      | v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f343,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = sK2(sK0)
    | ~ l1_lattices(sK0)
    | ~ v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f342,f51])).

fof(f342,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = sK2(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v13_lattices(sK0) ),
    inference(resolution,[],[f328,f76])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f328,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | k15_lattice3(sK0,k1_xboole_0) = sK2(sK0) ),
    inference(superposition,[],[f311,f252])).

fof(f311,plain,(
    ! [X2] : sK2(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0)) ),
    inference(subsumption_resolution,[],[f310,f51])).

fof(f310,plain,(
    ! [X2] :
      ( sK2(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f301,f54])).

fof(f301,plain,(
    ! [X2] :
      ( sK2(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f298,f87])).

fof(f298,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK2(sK0) = k2_lattices(sK0,X0,sK2(sK0)) ) ),
    inference(subsumption_resolution,[],[f297,f54])).

fof(f297,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK2(sK0) = k2_lattices(sK0,X0,sK2(sK0))
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f281,f56])).

fof(f281,plain,(
    ! [X1] :
      ( ~ l1_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | sK2(sK0) = k2_lattices(sK0,X1,sK2(sK0)) ) ),
    inference(subsumption_resolution,[],[f276,f51])).

fof(f276,plain,(
    ! [X1] :
      ( ~ l1_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | sK2(sK0) = k2_lattices(sK0,X1,sK2(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f273,f73])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sK2(X0) = k2_lattices(X0,X2,sK2(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f425,plain,(
    ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f413,f358])).

fof(f358,plain,(
    k5_lattices(sK0) != sK2(sK0) ),
    inference(subsumption_resolution,[],[f348,f273])).

fof(f348,plain,
    ( k5_lattices(sK0) != sK2(sK0)
    | ~ v13_lattices(sK0) ),
    inference(backward_demodulation,[],[f148,f346])).

fof(f148,plain,
    ( ~ v13_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f147,f54])).

fof(f147,plain,
    ( ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f146,f52])).

fof(f146,plain,
    ( ~ v10_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f50,f51])).

fof(f50,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f413,plain,
    ( k5_lattices(sK0) = sK2(sK0)
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0)) ),
    inference(superposition,[],[f412,f335])).

fof(f335,plain,(
    sK2(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK2(sK0)) ),
    inference(subsumption_resolution,[],[f334,f54])).

fof(f334,plain,
    ( sK2(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK2(sK0))
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f309,f56])).

fof(f309,plain,
    ( ~ l1_lattices(sK0)
    | sK2(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK2(sK0)) ),
    inference(subsumption_resolution,[],[f300,f51])).

fof(f300,plain,
    ( sK2(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK2(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f298,f67])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f412,plain,(
    ! [X0] :
      ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f411,f54])).

fof(f411,plain,(
    ! [X0] :
      ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f410,f56])).

fof(f410,plain,(
    ! [X2] :
      ( ~ l1_lattices(sK0)
      | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f409,f51])).

fof(f409,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X2)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f407,f67])).

fof(f407,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f406,f54])).

fof(f406,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f283,f56])).

fof(f283,plain,(
    ! [X3] :
      ( ~ l1_lattices(sK0)
      | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X3) ) ),
    inference(subsumption_resolution,[],[f278,f51])).

fof(f278,plain,(
    ! [X3] :
      ( ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X3) ) ),
    inference(resolution,[],[f273,f101])).

fof(f101,plain,(
    ! [X2,X0] :
      ( ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X2) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = X1
      | k5_lattices(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:15:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.21/0.53  % (6840)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.21/0.53  % (6840)Refutation not found, incomplete strategy% (6840)------------------------------
% 1.21/0.53  % (6840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (6840)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (6840)Memory used [KB]: 1663
% 1.21/0.53  % (6840)Time elapsed: 0.002 s
% 1.21/0.53  % (6840)------------------------------
% 1.21/0.53  % (6840)------------------------------
% 1.21/0.54  % (6855)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.21/0.54  % (6842)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.21/0.54  % (6868)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.21/0.54  % (6848)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.21/0.54  % (6869)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.21/0.54  % (6847)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.21/0.54  % (6845)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.21/0.54  % (6851)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.55  % (6846)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.55  % (6844)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.55  % (6863)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.55  % (6866)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.55  % (6865)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.55  % (6860)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.55  % (6862)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.55  % (6861)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.55  % (6843)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.55  % (6857)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.55  % (6859)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.56  % (6857)Refutation not found, incomplete strategy% (6857)------------------------------
% 1.35/0.56  % (6857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (6857)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (6857)Memory used [KB]: 10618
% 1.35/0.56  % (6857)Time elapsed: 0.138 s
% 1.35/0.56  % (6857)------------------------------
% 1.35/0.56  % (6857)------------------------------
% 1.35/0.56  % (6858)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.56  % (6853)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.56  % (6850)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.56  % (6841)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.56  % (6854)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.56  % (6850)Refutation not found, incomplete strategy% (6850)------------------------------
% 1.35/0.56  % (6850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (6852)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.56  % (6862)Refutation not found, incomplete strategy% (6862)------------------------------
% 1.35/0.56  % (6862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (6862)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (6862)Memory used [KB]: 10746
% 1.35/0.56  % (6862)Time elapsed: 0.146 s
% 1.35/0.56  % (6862)------------------------------
% 1.35/0.56  % (6862)------------------------------
% 1.35/0.56  % (6867)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.57  % (6851)Refutation not found, incomplete strategy% (6851)------------------------------
% 1.35/0.57  % (6851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  % (6851)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.57  
% 1.35/0.57  % (6851)Memory used [KB]: 10746
% 1.35/0.57  % (6851)Time elapsed: 0.127 s
% 1.35/0.57  % (6851)------------------------------
% 1.35/0.57  % (6851)------------------------------
% 1.35/0.57  % (6849)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.57  % (6849)Refutation not found, incomplete strategy% (6849)------------------------------
% 1.35/0.57  % (6849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  % (6849)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.57  
% 1.35/0.57  % (6849)Memory used [KB]: 10618
% 1.35/0.57  % (6849)Time elapsed: 0.002 s
% 1.35/0.57  % (6849)------------------------------
% 1.35/0.57  % (6849)------------------------------
% 1.35/0.58  % (6856)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.58  % (6864)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.58  % (6850)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.58  
% 1.35/0.58  % (6850)Memory used [KB]: 10746
% 1.35/0.58  % (6850)Time elapsed: 0.150 s
% 1.35/0.58  % (6850)------------------------------
% 1.35/0.58  % (6850)------------------------------
% 1.35/0.59  % (6861)Refutation found. Thanks to Tanya!
% 1.35/0.59  % SZS status Theorem for theBenchmark
% 1.35/0.59  % SZS output start Proof for theBenchmark
% 1.35/0.59  fof(f426,plain,(
% 1.35/0.59    $false),
% 1.35/0.59    inference(subsumption_resolution,[],[f425,f361])).
% 1.35/0.59  fof(f361,plain,(
% 1.35/0.59    m1_subset_1(sK2(sK0),u1_struct_0(sK0))),
% 1.35/0.59    inference(subsumption_resolution,[],[f360,f51])).
% 1.35/0.59  fof(f51,plain,(
% 1.35/0.59    ~v2_struct_0(sK0)),
% 1.35/0.59    inference(cnf_transformation,[],[f21])).
% 1.35/0.59  fof(f21,plain,(
% 1.35/0.59    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.35/0.59    inference(flattening,[],[f20])).
% 1.35/0.59  fof(f20,plain,(
% 1.35/0.59    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.35/0.59    inference(ennf_transformation,[],[f19])).
% 1.35/0.59  fof(f19,negated_conjecture,(
% 1.35/0.59    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.35/0.59    inference(negated_conjecture,[],[f18])).
% 1.35/0.59  fof(f18,conjecture,(
% 1.35/0.59    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.35/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).
% 1.35/0.59  fof(f360,plain,(
% 1.35/0.59    m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 1.35/0.59    inference(subsumption_resolution,[],[f357,f54])).
% 1.35/0.59  fof(f54,plain,(
% 1.35/0.59    l3_lattices(sK0)),
% 1.35/0.59    inference(cnf_transformation,[],[f21])).
% 1.35/0.59  fof(f357,plain,(
% 1.35/0.59    m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 1.35/0.59    inference(superposition,[],[f87,f346])).
% 1.35/0.59  fof(f346,plain,(
% 1.35/0.59    k15_lattice3(sK0,k1_xboole_0) = sK2(sK0)),
% 1.35/0.59    inference(subsumption_resolution,[],[f345,f54])).
% 1.35/0.59  fof(f345,plain,(
% 1.35/0.59    k15_lattice3(sK0,k1_xboole_0) = sK2(sK0) | ~l3_lattices(sK0)),
% 1.35/0.59    inference(resolution,[],[f344,f56])).
% 1.35/0.59  fof(f56,plain,(
% 1.35/0.59    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 1.35/0.59    inference(cnf_transformation,[],[f22])).
% 1.35/0.59  fof(f22,plain,(
% 1.35/0.59    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.35/0.59    inference(ennf_transformation,[],[f8])).
% 1.35/0.59  fof(f8,axiom,(
% 1.35/0.59    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.35/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 1.35/0.59  fof(f344,plain,(
% 1.35/0.59    ~l1_lattices(sK0) | k15_lattice3(sK0,k1_xboole_0) = sK2(sK0)),
% 1.35/0.59    inference(subsumption_resolution,[],[f343,f273])).
% 1.35/0.59  fof(f273,plain,(
% 1.35/0.59    v13_lattices(sK0)),
% 1.35/0.59    inference(subsumption_resolution,[],[f272,f51])).
% 1.35/0.59  fof(f272,plain,(
% 1.35/0.59    v13_lattices(sK0) | v2_struct_0(sK0)),
% 1.35/0.59    inference(subsumption_resolution,[],[f271,f54])).
% 1.35/0.59  fof(f271,plain,(
% 1.35/0.59    v13_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 1.35/0.59    inference(resolution,[],[f268,f87])).
% 1.35/0.59  fof(f268,plain,(
% 1.35/0.59    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v13_lattices(sK0)),
% 1.35/0.59    inference(subsumption_resolution,[],[f267,f54])).
% 1.35/0.59  fof(f267,plain,(
% 1.35/0.59    v13_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0)),
% 1.35/0.59    inference(resolution,[],[f266,f56])).
% 1.35/0.59  fof(f266,plain,(
% 1.35/0.59    ~l1_lattices(sK0) | v13_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))),
% 1.35/0.59    inference(subsumption_resolution,[],[f265,f51])).
% 1.35/0.59  fof(f265,plain,(
% 1.35/0.59    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)),
% 1.35/0.59    inference(duplicate_literal_removal,[],[f264])).
% 1.35/0.59  fof(f264,plain,(
% 1.35/0.59    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v13_lattices(sK0) | ~l1_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0)),
% 1.35/0.59    inference(resolution,[],[f258,f75])).
% 1.35/0.59  fof(f75,plain,(
% 1.35/0.59    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | v13_lattices(X0)) )),
% 1.35/0.59    inference(cnf_transformation,[],[f33])).
% 1.35/0.59  fof(f33,plain,(
% 1.35/0.59    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.35/0.59    inference(flattening,[],[f32])).
% 1.35/0.59  fof(f32,plain,(
% 1.35/0.59    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.35/0.59    inference(ennf_transformation,[],[f11])).
% 1.35/0.61  fof(f11,axiom,(
% 1.35/0.61    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 1.35/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).
% 1.35/0.61  fof(f258,plain,(
% 1.35/0.61    ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v13_lattices(sK0)),
% 1.35/0.61    inference(trivial_inequality_removal,[],[f257])).
% 1.35/0.61  fof(f257,plain,(
% 1.35/0.61    k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0) | v13_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))),
% 1.35/0.61    inference(superposition,[],[f218,f252])).
% 1.35/0.61  fof(f252,plain,(
% 1.35/0.61    ( ! [X2] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X2) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f251,f51])).
% 1.35/0.61  fof(f251,plain,(
% 1.35/0.61    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X2) | v2_struct_0(sK0)) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f250,f54])).
% 1.35/0.61  fof(f250,plain,(
% 1.35/0.61    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X2) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.35/0.61    inference(resolution,[],[f243,f87])).
% 1.35/0.61  fof(f243,plain,(
% 1.35/0.61    ( ! [X4] : (~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X4)) )),
% 1.35/0.61    inference(duplicate_literal_removal,[],[f240])).
% 1.35/0.61  fof(f240,plain,(
% 1.35/0.61    ( ! [X4] : (~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X4) | ~m1_subset_1(X4,u1_struct_0(sK0))) )),
% 1.35/0.61    inference(resolution,[],[f236,f160])).
% 1.35/0.61  fof(f160,plain,(
% 1.35/0.61    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.35/0.61    inference(superposition,[],[f143,f159])).
% 1.35/0.61  fof(f159,plain,(
% 1.35/0.61    ( ! [X2] : (k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f124,f54])).
% 1.35/0.61  fof(f124,plain,(
% 1.35/0.61    ( ! [X2] : (~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f123,f51])).
% 1.35/0.61  fof(f123,plain,(
% 1.35/0.61    ( ! [X2] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f111,f52])).
% 1.35/0.61  fof(f52,plain,(
% 1.35/0.61    v10_lattices(sK0)),
% 1.35/0.61    inference(cnf_transformation,[],[f21])).
% 1.35/0.61  fof(f111,plain,(
% 1.35/0.61    ( ! [X2] : (~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2) )),
% 1.35/0.61    inference(resolution,[],[f53,f83])).
% 1.35/0.61  fof(f83,plain,(
% 1.35/0.61    ( ! [X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) )),
% 1.35/0.61    inference(cnf_transformation,[],[f39])).
% 1.35/0.61  fof(f39,plain,(
% 1.35/0.61    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.35/0.61    inference(flattening,[],[f38])).
% 1.35/0.61  fof(f38,plain,(
% 1.35/0.61    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.35/0.61    inference(ennf_transformation,[],[f15])).
% 1.35/0.61  fof(f15,axiom,(
% 1.35/0.61    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 1.35/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattice3)).
% 1.35/0.61  fof(f53,plain,(
% 1.35/0.61    v4_lattice3(sK0)),
% 1.35/0.61    inference(cnf_transformation,[],[f21])).
% 1.35/0.61  fof(f143,plain,(
% 1.35/0.61    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) )),
% 1.35/0.61    inference(resolution,[],[f142,f55])).
% 1.35/0.61  fof(f55,plain,(
% 1.35/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.35/0.61    inference(cnf_transformation,[],[f2])).
% 1.35/0.61  fof(f2,axiom,(
% 1.35/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.35/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.35/0.61  fof(f142,plain,(
% 1.35/0.61    ( ! [X4,X5] : (~r1_tarski(X4,X5) | r3_lattices(sK0,k15_lattice3(sK0,X4),k15_lattice3(sK0,X5))) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f128,f54])).
% 1.35/0.61  fof(f128,plain,(
% 1.35/0.61    ( ! [X4,X5] : (~l3_lattices(sK0) | ~r1_tarski(X4,X5) | r3_lattices(sK0,k15_lattice3(sK0,X4),k15_lattice3(sK0,X5))) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f127,f51])).
% 1.35/0.61  fof(f127,plain,(
% 1.35/0.61    ( ! [X4,X5] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | ~r1_tarski(X4,X5) | r3_lattices(sK0,k15_lattice3(sK0,X4),k15_lattice3(sK0,X5))) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f113,f52])).
% 1.35/0.61  fof(f113,plain,(
% 1.35/0.61    ( ! [X4,X5] : (~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~r1_tarski(X4,X5) | r3_lattices(sK0,k15_lattice3(sK0,X4),k15_lattice3(sK0,X5))) )),
% 1.35/0.61    inference(resolution,[],[f53,f85])).
% 1.35/0.61  fof(f85,plain,(
% 1.35/0.61    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~r1_tarski(X1,X2) | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) )),
% 1.35/0.61    inference(cnf_transformation,[],[f41])).
% 1.35/0.61  fof(f41,plain,(
% 1.35/0.61    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.35/0.61    inference(flattening,[],[f40])).
% 1.35/0.61  fof(f40,plain,(
% 1.35/0.61    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.35/0.61    inference(ennf_transformation,[],[f16])).
% 1.35/0.61  fof(f16,axiom,(
% 1.35/0.61    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 1.35/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_lattice3)).
% 1.35/0.61  fof(f236,plain,(
% 1.35/0.61    ( ! [X2,X3] : (~r3_lattices(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X2,X3) = X2) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f235,f54])).
% 1.35/0.61  fof(f235,plain,(
% 1.35/0.61    ( ! [X2,X3] : (k2_lattices(sK0,X2,X3) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_lattices(sK0,X2,X3) | ~l3_lattices(sK0)) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f234,f52])).
% 1.35/0.61  fof(f234,plain,(
% 1.35/0.61    ( ! [X2,X3] : (k2_lattices(sK0,X2,X3) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_lattices(sK0,X2,X3) | ~v10_lattices(sK0) | ~l3_lattices(sK0)) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f233,f51])).
% 1.35/0.61  fof(f233,plain,(
% 1.35/0.61    ( ! [X2,X3] : (k2_lattices(sK0,X2,X3) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_lattices(sK0,X2,X3) | v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)) )),
% 1.35/0.61    inference(resolution,[],[f230,f60])).
% 1.35/0.61  fof(f60,plain,(
% 1.35/0.61    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.35/0.61    inference(cnf_transformation,[],[f24])).
% 1.35/0.61  fof(f24,plain,(
% 1.35/0.61    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.35/0.61    inference(flattening,[],[f23])).
% 1.35/0.61  fof(f23,plain,(
% 1.35/0.61    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.35/0.61    inference(ennf_transformation,[],[f5])).
% 1.35/0.61  fof(f5,axiom,(
% 1.35/0.61    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.35/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 1.35/0.61  fof(f230,plain,(
% 1.35/0.61    ( ! [X2,X3] : (~v6_lattices(sK0) | k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X3,X2)) )),
% 1.35/0.61    inference(duplicate_literal_removal,[],[f229])).
% 1.35/0.61  fof(f229,plain,(
% 1.35/0.61    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v6_lattices(sK0) | ~r3_lattices(sK0,X3,X2)) )),
% 1.35/0.61    inference(resolution,[],[f227,f193])).
% 1.35/0.61  fof(f193,plain,(
% 1.35/0.61    ( ! [X0,X1] : (r1_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v6_lattices(sK0) | ~r3_lattices(sK0,X0,X1)) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f192,f54])).
% 1.35/0.61  fof(f192,plain,(
% 1.35/0.61    ( ! [X0,X1] : (~v6_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X1) | ~r3_lattices(sK0,X0,X1) | ~l3_lattices(sK0)) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f191,f52])).
% 1.35/0.61  fof(f191,plain,(
% 1.35/0.61    ( ! [X0,X1] : (~v6_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X1) | ~r3_lattices(sK0,X0,X1) | ~v10_lattices(sK0) | ~l3_lattices(sK0)) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f190,f51])).
% 1.35/0.61  fof(f190,plain,(
% 1.35/0.61    ( ! [X0,X1] : (~v6_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X1) | ~r3_lattices(sK0,X0,X1) | v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)) )),
% 1.35/0.61    inference(resolution,[],[f189,f62])).
% 1.35/0.61  fof(f62,plain,(
% 1.35/0.61    ( ! [X0] : (v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.35/0.61    inference(cnf_transformation,[],[f24])).
% 1.35/0.61  fof(f189,plain,(
% 1.35/0.61    ( ! [X0,X1] : (~v8_lattices(sK0) | ~v6_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X1) | ~r3_lattices(sK0,X0,X1)) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f188,f54])).
% 1.35/0.61  fof(f188,plain,(
% 1.35/0.61    ( ! [X0,X1] : (~v8_lattices(sK0) | ~v6_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X1) | ~r3_lattices(sK0,X0,X1) | ~l3_lattices(sK0)) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f187,f52])).
% 1.35/0.61  fof(f187,plain,(
% 1.35/0.61    ( ! [X0,X1] : (~v8_lattices(sK0) | ~v6_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X1) | ~r3_lattices(sK0,X0,X1) | ~v10_lattices(sK0) | ~l3_lattices(sK0)) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f186,f51])).
% 1.35/0.61  fof(f186,plain,(
% 1.35/0.61    ( ! [X0,X1] : (~v8_lattices(sK0) | ~v6_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X1) | ~r3_lattices(sK0,X0,X1) | v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)) )),
% 1.35/0.61    inference(resolution,[],[f185,f63])).
% 1.35/0.61  fof(f63,plain,(
% 1.35/0.61    ( ! [X0] : (v9_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.35/0.61    inference(cnf_transformation,[],[f24])).
% 1.35/0.61  fof(f185,plain,(
% 1.35/0.61    ( ! [X2,X3] : (~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,X2,X3) | ~r3_lattices(sK0,X2,X3)) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f104,f54])).
% 1.35/0.61  fof(f104,plain,(
% 1.35/0.61    ( ! [X2,X3] : (~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,X2,X3) | ~r3_lattices(sK0,X2,X3)) )),
% 1.35/0.61    inference(resolution,[],[f51,f93])).
% 1.35/0.61  fof(f93,plain,(
% 1.35/0.61    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2)) )),
% 1.35/0.61    inference(cnf_transformation,[],[f47])).
% 1.35/0.61  fof(f47,plain,(
% 1.35/0.61    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.35/0.61    inference(flattening,[],[f46])).
% 1.35/0.61  fof(f46,plain,(
% 1.35/0.61    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.35/0.61    inference(ennf_transformation,[],[f9])).
% 1.35/0.61  fof(f9,axiom,(
% 1.35/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.35/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 1.35/0.62  fof(f227,plain,(
% 1.35/0.62    ( ! [X0,X1] : (~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f226,f54])).
% 1.35/0.62  fof(f226,plain,(
% 1.35/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = X0 | ~r1_lattices(sK0,X0,X1) | ~l3_lattices(sK0)) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f225,f52])).
% 1.35/0.62  fof(f225,plain,(
% 1.35/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = X0 | ~r1_lattices(sK0,X0,X1) | ~v10_lattices(sK0) | ~l3_lattices(sK0)) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f224,f51])).
% 1.35/0.62  fof(f224,plain,(
% 1.35/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = X0 | ~r1_lattices(sK0,X0,X1) | v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)) )),
% 1.35/0.62    inference(resolution,[],[f223,f62])).
% 1.35/0.62  fof(f223,plain,(
% 1.35/0.62    ( ! [X0,X1] : (~v8_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = X0 | ~r1_lattices(sK0,X0,X1)) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f222,f54])).
% 1.35/0.62  fof(f222,plain,(
% 1.35/0.62    ( ! [X0,X1] : (~v8_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = X0 | ~r1_lattices(sK0,X0,X1) | ~l3_lattices(sK0)) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f221,f52])).
% 1.35/0.62  fof(f221,plain,(
% 1.35/0.62    ( ! [X0,X1] : (~v8_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = X0 | ~r1_lattices(sK0,X0,X1) | ~v10_lattices(sK0) | ~l3_lattices(sK0)) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f220,f51])).
% 1.35/0.62  fof(f220,plain,(
% 1.35/0.62    ( ! [X0,X1] : (~v8_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = X0 | ~r1_lattices(sK0,X0,X1) | v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)) )),
% 1.35/0.62    inference(resolution,[],[f219,f63])).
% 1.35/0.62  fof(f219,plain,(
% 1.35/0.62    ( ! [X10,X9] : (~v9_lattices(sK0) | ~v8_lattices(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | k2_lattices(sK0,X9,X10) = X9 | ~r1_lattices(sK0,X9,X10)) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f108,f54])).
% 1.35/0.62  fof(f108,plain,(
% 1.35/0.62    ( ! [X10,X9] : (~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | k2_lattices(sK0,X9,X10) = X9 | ~r1_lattices(sK0,X9,X10)) )),
% 1.35/0.62    inference(resolution,[],[f51,f66])).
% 1.35/0.62  fof(f66,plain,(
% 1.35/0.62    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2)) )),
% 1.35/0.62    inference(cnf_transformation,[],[f27])).
% 1.35/0.62  fof(f27,plain,(
% 1.35/0.62    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.35/0.62    inference(flattening,[],[f26])).
% 1.35/0.62  fof(f26,plain,(
% 1.35/0.62    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 1.35/0.62    inference(ennf_transformation,[],[f10])).
% 1.35/0.62  fof(f10,axiom,(
% 1.35/0.62    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.35/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 1.35/0.62  fof(f218,plain,(
% 1.35/0.62    ( ! [X0] : (k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | v13_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f217,f54])).
% 1.35/0.62  fof(f217,plain,(
% 1.35/0.62    ( ! [X0] : (v13_lattices(sK0) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0)) )),
% 1.35/0.62    inference(resolution,[],[f216,f56])).
% 1.35/0.62  fof(f216,plain,(
% 1.35/0.62    ( ! [X2] : (~l1_lattices(sK0) | v13_lattices(sK0) | k2_lattices(sK0,X2,sK3(sK0,X2)) != X2 | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f215,f51])).
% 1.35/0.62  fof(f215,plain,(
% 1.35/0.62    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | v13_lattices(sK0) | k2_lattices(sK0,X2,sK3(sK0,X2)) != X2 | ~l1_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.35/0.62    inference(duplicate_literal_removal,[],[f214])).
% 1.35/0.62  fof(f214,plain,(
% 1.35/0.62    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | v13_lattices(sK0) | k2_lattices(sK0,X2,sK3(sK0,X2)) != X2 | ~l1_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0)) )),
% 1.35/0.62    inference(resolution,[],[f211,f75])).
% 1.35/0.62  fof(f211,plain,(
% 1.35/0.62    ( ! [X1] : (~m1_subset_1(sK3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v13_lattices(sK0) | k2_lattices(sK0,X1,sK3(sK0,X1)) != X1) )),
% 1.35/0.62    inference(duplicate_literal_removal,[],[f210])).
% 1.35/0.62  fof(f210,plain,(
% 1.35/0.62    ( ! [X1] : (k2_lattices(sK0,X1,sK3(sK0,X1)) != X1 | k2_lattices(sK0,X1,sK3(sK0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | v13_lattices(sK0) | ~m1_subset_1(sK3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.35/0.62    inference(superposition,[],[f197,f172])).
% 1.35/0.62  fof(f172,plain,(
% 1.35/0.62    ( ! [X0,X1] : (k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f171,f54])).
% 1.35/0.62  fof(f171,plain,(
% 1.35/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0)) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f170,f52])).
% 1.35/0.62  fof(f170,plain,(
% 1.35/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v10_lattices(sK0) | ~l3_lattices(sK0)) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f169,f51])).
% 1.35/0.62  fof(f169,plain,(
% 1.35/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)) )),
% 1.35/0.62    inference(resolution,[],[f168,f60])).
% 1.35/0.62  fof(f168,plain,(
% 1.35/0.62    ( ! [X0,X1] : (~v6_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f167,f54])).
% 1.35/0.62  fof(f167,plain,(
% 1.35/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0) | ~v6_lattices(sK0) | ~l3_lattices(sK0)) )),
% 1.35/0.62    inference(resolution,[],[f105,f56])).
% 1.35/0.62  fof(f105,plain,(
% 1.35/0.62    ( ! [X4,X5] : (~l1_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k2_lattices(sK0,X4,X5) = k2_lattices(sK0,X5,X4) | ~v6_lattices(sK0)) )),
% 1.35/0.62    inference(resolution,[],[f51,f79])).
% 1.35/0.62  fof(f79,plain,(
% 1.35/0.62    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~v6_lattices(X0)) )),
% 1.35/0.62    inference(cnf_transformation,[],[f35])).
% 1.35/0.62  fof(f35,plain,(
% 1.35/0.62    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.35/0.62    inference(flattening,[],[f34])).
% 1.35/0.62  fof(f34,plain,(
% 1.35/0.62    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.35/0.62    inference(ennf_transformation,[],[f12])).
% 1.35/0.62  fof(f12,axiom,(
% 1.35/0.62    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 1.35/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).
% 1.35/0.62  fof(f197,plain,(
% 1.35/0.62    ( ! [X0] : (k2_lattices(sK0,sK3(sK0,X0),X0) != X0 | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v13_lattices(sK0)) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f196,f54])).
% 1.35/0.62  fof(f196,plain,(
% 1.35/0.62    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | k2_lattices(sK0,sK3(sK0,X0),X0) != X0 | v13_lattices(sK0) | ~l3_lattices(sK0)) )),
% 1.35/0.62    inference(resolution,[],[f106,f56])).
% 1.35/0.62  fof(f106,plain,(
% 1.35/0.62    ( ! [X6] : (~l1_lattices(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6 | k2_lattices(sK0,sK3(sK0,X6),X6) != X6 | v13_lattices(sK0)) )),
% 1.35/0.62    inference(resolution,[],[f51,f74])).
% 1.35/0.62  fof(f74,plain,(
% 1.35/0.62    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k2_lattices(X0,X1,sK3(X0,X1)) != X1 | k2_lattices(X0,sK3(X0,X1),X1) != X1 | v13_lattices(X0)) )),
% 1.35/0.62    inference(cnf_transformation,[],[f33])).
% 1.35/0.62  fof(f343,plain,(
% 1.35/0.62    k15_lattice3(sK0,k1_xboole_0) = sK2(sK0) | ~l1_lattices(sK0) | ~v13_lattices(sK0)),
% 1.35/0.62    inference(subsumption_resolution,[],[f342,f51])).
% 1.35/0.62  fof(f342,plain,(
% 1.35/0.62    k15_lattice3(sK0,k1_xboole_0) = sK2(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~v13_lattices(sK0)),
% 1.35/0.62    inference(resolution,[],[f328,f76])).
% 1.35/0.62  fof(f76,plain,(
% 1.35/0.62    ( ! [X0] : (m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0) | ~v13_lattices(X0)) )),
% 1.35/0.62    inference(cnf_transformation,[],[f33])).
% 1.35/0.62  fof(f328,plain,(
% 1.35/0.62    ~m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = sK2(sK0)),
% 1.35/0.62    inference(superposition,[],[f311,f252])).
% 1.35/0.62  fof(f311,plain,(
% 1.35/0.62    ( ! [X2] : (sK2(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0))) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f310,f51])).
% 1.35/0.62  fof(f310,plain,(
% 1.35/0.62    ( ! [X2] : (sK2(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0)) | v2_struct_0(sK0)) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f301,f54])).
% 1.35/0.62  fof(f301,plain,(
% 1.35/0.62    ( ! [X2] : (sK2(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.35/0.62    inference(resolution,[],[f298,f87])).
% 1.35/0.62  fof(f298,plain,(
% 1.35/0.62    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK2(sK0) = k2_lattices(sK0,X0,sK2(sK0))) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f297,f54])).
% 1.35/0.62  fof(f297,plain,(
% 1.35/0.62    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK2(sK0) = k2_lattices(sK0,X0,sK2(sK0)) | ~l3_lattices(sK0)) )),
% 1.35/0.62    inference(resolution,[],[f281,f56])).
% 1.35/0.62  fof(f281,plain,(
% 1.35/0.62    ( ! [X1] : (~l1_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK2(sK0) = k2_lattices(sK0,X1,sK2(sK0))) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f276,f51])).
% 1.35/0.62  fof(f276,plain,(
% 1.35/0.62    ( ! [X1] : (~l1_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK2(sK0) = k2_lattices(sK0,X1,sK2(sK0)) | v2_struct_0(sK0)) )),
% 1.35/0.62    inference(resolution,[],[f273,f73])).
% 1.35/0.62  fof(f73,plain,(
% 1.35/0.62    ( ! [X2,X0] : (~v13_lattices(X0) | ~l1_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | sK2(X0) = k2_lattices(X0,X2,sK2(X0)) | v2_struct_0(X0)) )),
% 1.35/0.62    inference(cnf_transformation,[],[f33])).
% 1.35/0.62  fof(f87,plain,(
% 1.35/0.62    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.35/0.62    inference(cnf_transformation,[],[f43])).
% 1.35/0.62  fof(f43,plain,(
% 1.35/0.62    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.35/0.62    inference(flattening,[],[f42])).
% 1.35/0.62  fof(f42,plain,(
% 1.35/0.62    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.35/0.62    inference(ennf_transformation,[],[f13])).
% 1.35/0.62  fof(f13,axiom,(
% 1.35/0.62    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.35/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 1.35/0.62  fof(f425,plain,(
% 1.35/0.62    ~m1_subset_1(sK2(sK0),u1_struct_0(sK0))),
% 1.35/0.62    inference(subsumption_resolution,[],[f413,f358])).
% 1.35/0.62  fof(f358,plain,(
% 1.35/0.62    k5_lattices(sK0) != sK2(sK0)),
% 1.35/0.62    inference(subsumption_resolution,[],[f348,f273])).
% 1.35/0.62  fof(f348,plain,(
% 1.35/0.62    k5_lattices(sK0) != sK2(sK0) | ~v13_lattices(sK0)),
% 1.35/0.62    inference(backward_demodulation,[],[f148,f346])).
% 1.35/0.62  fof(f148,plain,(
% 1.35/0.62    ~v13_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 1.35/0.62    inference(subsumption_resolution,[],[f147,f54])).
% 1.35/0.62  fof(f147,plain,(
% 1.35/0.62    ~v13_lattices(sK0) | ~l3_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 1.35/0.62    inference(subsumption_resolution,[],[f146,f52])).
% 1.35/0.62  fof(f146,plain,(
% 1.35/0.62    ~v10_lattices(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 1.35/0.62    inference(subsumption_resolution,[],[f50,f51])).
% 1.35/0.62  fof(f50,plain,(
% 1.35/0.62    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 1.35/0.62    inference(cnf_transformation,[],[f21])).
% 1.35/0.62  fof(f413,plain,(
% 1.35/0.62    k5_lattices(sK0) = sK2(sK0) | ~m1_subset_1(sK2(sK0),u1_struct_0(sK0))),
% 1.35/0.62    inference(superposition,[],[f412,f335])).
% 1.35/0.62  fof(f335,plain,(
% 1.35/0.62    sK2(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK2(sK0))),
% 1.35/0.62    inference(subsumption_resolution,[],[f334,f54])).
% 1.35/0.62  fof(f334,plain,(
% 1.35/0.62    sK2(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK2(sK0)) | ~l3_lattices(sK0)),
% 1.35/0.62    inference(resolution,[],[f309,f56])).
% 1.35/0.62  fof(f309,plain,(
% 1.35/0.62    ~l1_lattices(sK0) | sK2(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK2(sK0))),
% 1.35/0.62    inference(subsumption_resolution,[],[f300,f51])).
% 1.35/0.62  fof(f300,plain,(
% 1.35/0.62    sK2(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK2(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)),
% 1.35/0.62    inference(resolution,[],[f298,f67])).
% 1.35/0.62  fof(f67,plain,(
% 1.35/0.62    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.35/0.62    inference(cnf_transformation,[],[f29])).
% 1.35/0.62  fof(f29,plain,(
% 1.35/0.62    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.35/0.62    inference(flattening,[],[f28])).
% 1.35/0.62  fof(f28,plain,(
% 1.35/0.62    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.35/0.62    inference(ennf_transformation,[],[f7])).
% 1.35/0.62  fof(f7,axiom,(
% 1.35/0.62    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 1.35/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 1.35/0.62  fof(f412,plain,(
% 1.35/0.62    ( ! [X0] : (k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f411,f54])).
% 1.35/0.62  fof(f411,plain,(
% 1.35/0.62    ( ! [X0] : (k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0)) )),
% 1.35/0.62    inference(resolution,[],[f410,f56])).
% 1.35/0.62  fof(f410,plain,(
% 1.35/0.62    ( ! [X2] : (~l1_lattices(sK0) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X2) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f409,f51])).
% 1.35/0.62  fof(f409,plain,(
% 1.35/0.62    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X2) | ~l1_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.35/0.62    inference(resolution,[],[f407,f67])).
% 1.35/0.62  fof(f407,plain,(
% 1.35/0.62    ( ! [X0] : (~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f406,f54])).
% 1.35/0.62  fof(f406,plain,(
% 1.35/0.62    ( ! [X0] : (~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) | ~l3_lattices(sK0)) )),
% 1.35/0.62    inference(resolution,[],[f283,f56])).
% 1.35/0.62  fof(f283,plain,(
% 1.35/0.62    ( ! [X3] : (~l1_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X3)) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f278,f51])).
% 1.35/0.62  fof(f278,plain,(
% 1.35/0.62    ( ! [X3] : (~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X3)) )),
% 1.35/0.62    inference(resolution,[],[f273,f101])).
% 1.35/0.62  fof(f101,plain,(
% 1.35/0.62    ( ! [X2,X0] : (~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X2)) )),
% 1.35/0.62    inference(equality_resolution,[],[f69])).
% 1.35/0.62  fof(f69,plain,(
% 1.35/0.62    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = X1 | k5_lattices(X0) != X1) )),
% 1.35/0.62    inference(cnf_transformation,[],[f31])).
% 1.35/0.62  fof(f31,plain,(
% 1.35/0.62    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.35/0.62    inference(flattening,[],[f30])).
% 1.35/0.62  fof(f30,plain,(
% 1.35/0.62    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.35/0.62    inference(ennf_transformation,[],[f6])).
% 1.35/0.62  fof(f6,axiom,(
% 1.35/0.62    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 1.35/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).
% 1.35/0.62  % SZS output end Proof for theBenchmark
% 1.35/0.62  % (6861)------------------------------
% 1.35/0.62  % (6861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.62  % (6861)Termination reason: Refutation
% 1.35/0.62  
% 1.35/0.62  % (6861)Memory used [KB]: 1918
% 1.35/0.62  % (6861)Time elapsed: 0.182 s
% 1.35/0.62  % (6861)------------------------------
% 1.35/0.62  % (6861)------------------------------
% 1.35/0.62  % (6839)Success in time 0.249 s
%------------------------------------------------------------------------------
