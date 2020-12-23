%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:48 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 493 expanded)
%              Number of leaves         :   32 ( 174 expanded)
%              Depth                    :   20
%              Number of atoms          : 1097 (2193 expanded)
%              Number of equality atoms :  100 ( 199 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f884,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f118,f123,f128,f187,f227,f232,f237,f258,f263,f271,f294,f431,f499,f570,f741,f750,f858,f883])).

fof(f883,plain,
    ( spl9_1
    | spl9_6
    | ~ spl9_9
    | ~ spl9_24
    | spl9_26 ),
    inference(avatar_contradiction_clause,[],[f882])).

fof(f882,plain,
    ( $false
    | spl9_1
    | spl9_6
    | ~ spl9_9
    | ~ spl9_24
    | spl9_26 ),
    inference(subsumption_resolution,[],[f881,f186])).

fof(f186,plain,
    ( ~ v13_lattices(sK0)
    | spl9_6 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl9_6
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f881,plain,
    ( v13_lattices(sK0)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_24
    | spl9_26 ),
    inference(subsumption_resolution,[],[f880,f112])).

fof(f112,plain,
    ( ~ v2_struct_0(sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl9_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f880,plain,
    ( v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl9_9
    | ~ spl9_24
    | spl9_26 ),
    inference(subsumption_resolution,[],[f879,f739])).

fof(f739,plain,
    ( m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f738])).

fof(f738,plain,
    ( spl9_24
  <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f879,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl9_9
    | spl9_26 ),
    inference(subsumption_resolution,[],[f878,f225])).

fof(f225,plain,
    ( l1_lattices(sK0)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl9_9
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f878,plain,
    ( ~ l1_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v13_lattices(sK0)
    | spl9_26 ),
    inference(resolution,[],[f857,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

fof(f857,plain,
    ( ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl9_26 ),
    inference(avatar_component_clause,[],[f855])).

fof(f855,plain,
    ( spl9_26
  <=> m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f858,plain,
    ( ~ spl9_26
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_16
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f802,f738,f497,f125,f120,f115,f110,f855])).

fof(f115,plain,
    ( spl9_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f120,plain,
    ( spl9_3
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f125,plain,
    ( spl9_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f497,plain,
    ( spl9_16
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X2,sK3(sK0,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f802,plain,
    ( ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_16
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f797,f739])).

fof(f797,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_16 ),
    inference(resolution,[],[f498,f418])).

fof(f418,plain,
    ( ! [X1] :
        ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(superposition,[],[f360,f157])).

fof(f157,plain,
    ( ! [X2] :
        ( k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f156,f127])).

fof(f127,plain,
    ( l3_lattices(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f156,plain,
    ( ! [X2] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2 )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f155,f112])).

fof(f155,plain,
    ( ! [X2] :
        ( v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2 )
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f141,f117])).

fof(f117,plain,
    ( v10_lattices(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f141,plain,
    ( ! [X2] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2 )
    | ~ spl9_3 ),
    inference(resolution,[],[f122,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattice3)).

fof(f122,plain,
    ( v4_lattice3(sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f360,plain,
    ( ! [X0] : r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(resolution,[],[f190,f54])).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f190,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,a_2_5_lattice3(sK0,X0))
        | r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(superposition,[],[f163,f151])).

fof(f151,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f150,f127])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ l3_lattices(sK0)
        | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f149,f112])).

fof(f149,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0)) )
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f139,f117])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0)) )
    | ~ spl9_3 ),
    inference(resolution,[],[f122,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).

fof(f163,plain,
    ( ! [X4,X5] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X4),k15_lattice3(sK0,X5))
        | ~ r1_tarski(X4,X5) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f162,f127])).

fof(f162,plain,
    ( ! [X4,X5] :
        ( ~ l3_lattices(sK0)
        | ~ r1_tarski(X4,X5)
        | r3_lattices(sK0,k15_lattice3(sK0,X4),k15_lattice3(sK0,X5)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f161,f112])).

fof(f161,plain,
    ( ! [X4,X5] :
        ( v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X4,X5)
        | r3_lattices(sK0,k15_lattice3(sK0,X4),k15_lattice3(sK0,X5)) )
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f143,f117])).

fof(f143,plain,
    ( ! [X4,X5] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X4,X5)
        | r3_lattices(sK0,k15_lattice3(sK0,X4),k15_lattice3(sK0,X5)) )
    | ~ spl9_3 ),
    inference(resolution,[],[f122,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ r1_tarski(X1,X2)
      | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).

fof(f498,plain,
    ( ! [X2] :
        ( ~ r3_lattices(sK0,X2,sK3(sK0,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f497])).

fof(f750,plain,
    ( spl9_1
    | ~ spl9_4
    | spl9_24 ),
    inference(avatar_contradiction_clause,[],[f749])).

fof(f749,plain,
    ( $false
    | spl9_1
    | ~ spl9_4
    | spl9_24 ),
    inference(subsumption_resolution,[],[f748,f112])).

fof(f748,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_4
    | spl9_24 ),
    inference(subsumption_resolution,[],[f747,f127])).

fof(f747,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_24 ),
    inference(resolution,[],[f740,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f740,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl9_24 ),
    inference(avatar_component_clause,[],[f738])).

fof(f741,plain,
    ( ~ spl9_24
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f731,f562,f255,f251,f248,f224,f184,f180,f125,f120,f115,f110,f738])).

fof(f180,plain,
    ( spl9_5
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f248,plain,
    ( spl9_10
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X2,X3)
        | r1_lattices(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f251,plain,
    ( spl9_11
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f255,plain,
    ( spl9_12
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f562,plain,
    ( spl9_19
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f731,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f730,f563])).

fof(f563,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f562])).

fof(f730,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f720,f182])).

fof(f182,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f180])).

fof(f720,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_19 ),
    inference(resolution,[],[f712,f418])).

fof(f712,plain,
    ( ! [X1] :
        ( ~ r3_lattices(sK0,X1,k5_lattices(sK0))
        | k5_lattices(sK0) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_19 ),
    inference(duplicate_literal_removal,[],[f711])).

fof(f711,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = X1
        | ~ r3_lattices(sK0,X1,k5_lattices(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_19 ),
    inference(superposition,[],[f673,f157])).

fof(f673,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | k5_lattices(sK0) = k15_lattice3(sK0,X1)
        | ~ r3_lattices(sK0,k15_lattice3(sK0,X1),k5_lattices(sK0)) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f667,f563])).

fof(f667,plain,
    ( ! [X1] :
        ( k5_lattices(sK0) = k15_lattice3(sK0,X1)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,k15_lattice3(sK0,X1),k5_lattices(sK0)) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_19 ),
    inference(superposition,[],[f599,f285])).

fof(f285,plain,
    ( ! [X2,X3] :
        ( k2_lattices(sK0,X3,X2) = X3
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X3,X2) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12 ),
    inference(duplicate_literal_removal,[],[f284])).

fof(f284,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,X3,X2) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12 ),
    inference(resolution,[],[f273,f249])).

fof(f249,plain,
    ( ! [X2,X3] :
        ( r1_lattices(sK0,X2,X3)
        | ~ r3_lattices(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f248])).

fof(f273,plain,
    ( ! [X10,X9] :
        ( ~ r1_lattices(sK0,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | k2_lattices(sK0,X9,X10) = X9
        | ~ m1_subset_1(X9,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_11
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f265,f256])).

fof(f256,plain,
    ( v8_lattices(sK0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f255])).

fof(f265,plain,
    ( ! [X10,X9] :
        ( ~ v8_lattices(sK0)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | k2_lattices(sK0,X9,X10) = X9
        | ~ r1_lattices(sK0,X9,X10) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f138,f252])).

fof(f252,plain,
    ( v9_lattices(sK0)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f251])).

fof(f138,plain,
    ( ! [X10,X9] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | k2_lattices(sK0,X9,X10) = X9
        | ~ r1_lattices(sK0,X9,X10) )
    | spl9_1
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f134,f127])).

fof(f134,plain,
    ( ! [X10,X9] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | k2_lattices(sK0,X9,X10) = X9
        | ~ r1_lattices(sK0,X9,X10) )
    | spl9_1 ),
    inference(resolution,[],[f112,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(f599,plain,
    ( ! [X2] : k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f598,f112])).

fof(f598,plain,
    ( ! [X2] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f590,f127])).

fof(f590,plain,
    ( ! [X2] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_19 ),
    inference(resolution,[],[f571,f85])).

fof(f571,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0)) )
    | spl9_1
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f516,f563])).

fof(f516,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0)) )
    | spl9_1
    | ~ spl9_6
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f515,f112])).

fof(f515,plain,
    ( ! [X4] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0)) )
    | ~ spl9_6
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f506,f225])).

fof(f506,plain,
    ( ! [X4] :
        ( ~ l1_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f185,f101])).

fof(f101,plain,(
    ! [X2,X0] :
      ( ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X2,X1) = X1
      | k5_lattices(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(f185,plain,
    ( v13_lattices(sK0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f184])).

fof(f570,plain,
    ( spl9_1
    | ~ spl9_9
    | spl9_19 ),
    inference(avatar_contradiction_clause,[],[f569])).

fof(f569,plain,
    ( $false
    | spl9_1
    | ~ spl9_9
    | spl9_19 ),
    inference(subsumption_resolution,[],[f568,f112])).

fof(f568,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_9
    | spl9_19 ),
    inference(subsumption_resolution,[],[f567,f225])).

fof(f567,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_19 ),
    inference(resolution,[],[f564,f65])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f564,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl9_19 ),
    inference(avatar_component_clause,[],[f562])).

fof(f499,plain,
    ( spl9_6
    | spl9_16
    | spl9_1
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f490,f429,f255,f251,f248,f224,f125,f110,f497,f184])).

fof(f429,plain,
    ( spl9_15
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,X2,sK3(sK0,X2)) != X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f490,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X2,sK3(sK0,X2))
        | v13_lattices(sK0) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f489,f112])).

fof(f489,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X2,sK3(sK0,X2))
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f488,f225])).

fof(f488,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X2,sK3(sK0,X2))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(duplicate_literal_removal,[],[f487])).

fof(f487,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X2,sK3(sK0,X2))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(resolution,[],[f434,f73])).

fof(f434,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,sK3(sK0,X0)) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(trivial_inequality_removal,[],[f433])).

fof(f433,plain,
    ( ! [X0] :
        ( X0 != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,sK3(sK0,X0)) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(duplicate_literal_removal,[],[f432])).

fof(f432,plain,
    ( ! [X0] :
        ( X0 != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,sK3(sK0,X0)) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(superposition,[],[f430,f285])).

fof(f430,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,X2,sK3(sK0,X2)) != X2
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f429])).

fof(f431,plain,
    ( spl9_6
    | spl9_15
    | spl9_1
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f416,f292,f224,f221,f110,f429,f184])).

fof(f221,plain,
    ( spl9_8
  <=> ! [X5,X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k2_lattices(sK0,X4,X5) = k2_lattices(sK0,X5,X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f292,plain,
    ( spl9_13
  <=> ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k2_lattices(sK0,sK3(sK0,X6),X6) != X6
        | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f416,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,X2,sK3(sK0,X2)) != X2
        | v13_lattices(sK0) )
    | spl9_1
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f415,f112])).

fof(f415,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,X2,sK3(sK0,X2)) != X2
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f414,f225])).

fof(f414,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,X2,sK3(sK0,X2)) != X2
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | ~ spl9_8
    | ~ spl9_13 ),
    inference(duplicate_literal_removal,[],[f413])).

fof(f413,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,X2,sK3(sK0,X2)) != X2
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | ~ spl9_8
    | ~ spl9_13 ),
    inference(resolution,[],[f298,f73])).

fof(f298,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 )
    | ~ spl9_8
    | ~ spl9_13 ),
    inference(duplicate_literal_removal,[],[f295])).

fof(f295,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl9_8
    | ~ spl9_13 ),
    inference(superposition,[],[f293,f222])).

fof(f222,plain,
    ( ! [X4,X5] :
        ( k2_lattices(sK0,X4,X5) = k2_lattices(sK0,X5,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f221])).

fof(f293,plain,
    ( ! [X6] :
        ( k2_lattices(sK0,sK3(sK0,X6),X6) != X6
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6 )
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f292])).

fof(f294,plain,
    ( spl9_6
    | spl9_13
    | spl9_1
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f238,f224,f110,f292,f184])).

fof(f238,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6
        | k2_lattices(sK0,sK3(sK0,X6),X6) != X6
        | v13_lattices(sK0) )
    | spl9_1
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f132,f225])).

fof(f132,plain,
    ( ! [X6] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6
        | k2_lattices(sK0,sK3(sK0,X6),X6) != X6
        | v13_lattices(sK0) )
    | spl9_1 ),
    inference(resolution,[],[f112,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_lattices(X0,X1,sK3(X0,X1)) != X1
      | k2_lattices(X0,sK3(X0,X1),X1) != X1
      | v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f271,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_12 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_12 ),
    inference(subsumption_resolution,[],[f269,f127])).

fof(f269,plain,
    ( ~ l3_lattices(sK0)
    | spl9_1
    | ~ spl9_2
    | spl9_12 ),
    inference(subsumption_resolution,[],[f268,f117])).

fof(f268,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_1
    | spl9_12 ),
    inference(subsumption_resolution,[],[f267,f112])).

fof(f267,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_12 ),
    inference(resolution,[],[f257,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v8_lattices(X0)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f257,plain,
    ( ~ v8_lattices(sK0)
    | spl9_12 ),
    inference(avatar_component_clause,[],[f255])).

fof(f263,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_11 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_11 ),
    inference(subsumption_resolution,[],[f261,f127])).

fof(f261,plain,
    ( ~ l3_lattices(sK0)
    | spl9_1
    | ~ spl9_2
    | spl9_11 ),
    inference(subsumption_resolution,[],[f260,f117])).

fof(f260,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_1
    | spl9_11 ),
    inference(subsumption_resolution,[],[f259,f112])).

fof(f259,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_11 ),
    inference(resolution,[],[f253,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f253,plain,
    ( ~ v9_lattices(sK0)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f251])).

fof(f258,plain,
    ( spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | spl9_1
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f233,f217,f125,f110,f255,f251,f248])).

fof(f217,plain,
    ( spl9_7
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f233,plain,
    ( ! [X2,X3] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_lattices(sK0,X2,X3)
        | ~ r3_lattices(sK0,X2,X3) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f136,f218])).

fof(f218,plain,
    ( v6_lattices(sK0)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f217])).

fof(f136,plain,
    ( ! [X2,X3] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_lattices(sK0,X2,X3)
        | ~ r3_lattices(sK0,X2,X3) )
    | spl9_1
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f130,f127])).

fof(f130,plain,
    ( ! [X2,X3] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_lattices(sK0,X2,X3)
        | ~ r3_lattices(sK0,X2,X3) )
    | spl9_1 ),
    inference(resolution,[],[f112,f94])).

fof(f94,plain,(
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
    inference(cnf_transformation,[],[f46])).

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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f237,plain,
    ( ~ spl9_4
    | spl9_9 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl9_4
    | spl9_9 ),
    inference(subsumption_resolution,[],[f235,f127])).

fof(f235,plain,
    ( ~ l3_lattices(sK0)
    | spl9_9 ),
    inference(resolution,[],[f226,f55])).

fof(f55,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f226,plain,
    ( ~ l1_lattices(sK0)
    | spl9_9 ),
    inference(avatar_component_clause,[],[f224])).

fof(f232,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_7 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_7 ),
    inference(subsumption_resolution,[],[f230,f127])).

fof(f230,plain,
    ( ~ l3_lattices(sK0)
    | spl9_1
    | ~ spl9_2
    | spl9_7 ),
    inference(subsumption_resolution,[],[f229,f117])).

fof(f229,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_1
    | spl9_7 ),
    inference(subsumption_resolution,[],[f228,f112])).

fof(f228,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_7 ),
    inference(resolution,[],[f219,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f219,plain,
    ( ~ v6_lattices(sK0)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f217])).

fof(f227,plain,
    ( ~ spl9_7
    | spl9_8
    | ~ spl9_9
    | spl9_1 ),
    inference(avatar_split_clause,[],[f131,f110,f224,f221,f217])).

fof(f131,plain,
    ( ! [X4,X5] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k2_lattices(sK0,X4,X5) = k2_lattices(sK0,X5,X4)
        | ~ v6_lattices(sK0) )
    | spl9_1 ),
    inference(resolution,[],[f112,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
      | ~ v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

fof(f187,plain,
    ( ~ spl9_5
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f108,f184,f180])).

fof(f108,plain,
    ( ~ v13_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f107,f53])).

fof(f53,plain,(
    l3_lattices(sK0) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

fof(f107,plain,
    ( ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f106,f51])).

fof(f51,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f106,plain,
    ( ~ v10_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f49,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f128,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f53,f125])).

fof(f123,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f52,f120])).

fof(f52,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f118,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f51,f115])).

fof(f113,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f50,f110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:30:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (10235)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.48  % (10250)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.50  % (10243)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.50  % (10248)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (10233)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (10242)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (10239)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (10229)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (10231)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (10255)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (10237)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (10254)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (10247)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (10236)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (10236)Refutation not found, incomplete strategy% (10236)------------------------------
% 0.22/0.55  % (10236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10236)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (10236)Memory used [KB]: 10618
% 0.22/0.55  % (10236)Time elapsed: 0.002 s
% 0.22/0.55  % (10236)------------------------------
% 0.22/0.55  % (10236)------------------------------
% 0.22/0.55  % (10241)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (10228)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.49/0.56  % (10227)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.49/0.56  % (10246)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.49/0.56  % (10227)Refutation not found, incomplete strategy% (10227)------------------------------
% 1.49/0.56  % (10227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (10227)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (10227)Memory used [KB]: 1663
% 1.49/0.56  % (10227)Time elapsed: 0.001 s
% 1.49/0.56  % (10227)------------------------------
% 1.49/0.56  % (10227)------------------------------
% 1.49/0.56  % (10237)Refutation not found, incomplete strategy% (10237)------------------------------
% 1.49/0.56  % (10237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (10237)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (10237)Memory used [KB]: 10746
% 1.49/0.56  % (10237)Time elapsed: 0.120 s
% 1.49/0.56  % (10237)------------------------------
% 1.49/0.56  % (10237)------------------------------
% 1.49/0.56  % (10238)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.49/0.56  % (10238)Refutation not found, incomplete strategy% (10238)------------------------------
% 1.49/0.56  % (10238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (10238)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (10238)Memory used [KB]: 10746
% 1.49/0.56  % (10238)Time elapsed: 0.146 s
% 1.49/0.56  % (10238)------------------------------
% 1.49/0.56  % (10238)------------------------------
% 1.49/0.56  % (10230)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.49/0.56  % (10251)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.49/0.56  % (10253)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.49/0.57  % (10232)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.49/0.57  % (10252)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.49/0.57  % (10234)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.64/0.58  % (10256)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.64/0.58  % (10249)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.64/0.58  % (10249)Refutation not found, incomplete strategy% (10249)------------------------------
% 1.64/0.58  % (10249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (10249)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (10249)Memory used [KB]: 10746
% 1.64/0.58  % (10249)Time elapsed: 0.179 s
% 1.64/0.58  % (10249)------------------------------
% 1.64/0.58  % (10249)------------------------------
% 1.64/0.58  % (10244)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.64/0.59  % (10240)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.64/0.59  % (10244)Refutation not found, incomplete strategy% (10244)------------------------------
% 1.64/0.59  % (10244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.60  % (10245)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.64/0.60  % (10244)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.60  
% 1.64/0.60  % (10244)Memory used [KB]: 10618
% 1.64/0.60  % (10244)Time elapsed: 0.180 s
% 1.64/0.60  % (10244)------------------------------
% 1.64/0.60  % (10244)------------------------------
% 1.64/0.60  % (10247)Refutation found. Thanks to Tanya!
% 1.64/0.60  % SZS status Theorem for theBenchmark
% 1.64/0.60  % SZS output start Proof for theBenchmark
% 1.64/0.60  fof(f884,plain,(
% 1.64/0.60    $false),
% 1.64/0.60    inference(avatar_sat_refutation,[],[f113,f118,f123,f128,f187,f227,f232,f237,f258,f263,f271,f294,f431,f499,f570,f741,f750,f858,f883])).
% 1.64/0.60  fof(f883,plain,(
% 1.64/0.60    spl9_1 | spl9_6 | ~spl9_9 | ~spl9_24 | spl9_26),
% 1.64/0.60    inference(avatar_contradiction_clause,[],[f882])).
% 1.64/0.60  fof(f882,plain,(
% 1.64/0.60    $false | (spl9_1 | spl9_6 | ~spl9_9 | ~spl9_24 | spl9_26)),
% 1.64/0.60    inference(subsumption_resolution,[],[f881,f186])).
% 1.64/0.60  fof(f186,plain,(
% 1.64/0.60    ~v13_lattices(sK0) | spl9_6),
% 1.64/0.60    inference(avatar_component_clause,[],[f184])).
% 1.64/0.60  fof(f184,plain,(
% 1.64/0.60    spl9_6 <=> v13_lattices(sK0)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.64/0.60  fof(f881,plain,(
% 1.64/0.60    v13_lattices(sK0) | (spl9_1 | ~spl9_9 | ~spl9_24 | spl9_26)),
% 1.64/0.60    inference(subsumption_resolution,[],[f880,f112])).
% 1.64/0.60  fof(f112,plain,(
% 1.64/0.60    ~v2_struct_0(sK0) | spl9_1),
% 1.64/0.60    inference(avatar_component_clause,[],[f110])).
% 1.64/0.60  fof(f110,plain,(
% 1.64/0.60    spl9_1 <=> v2_struct_0(sK0)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.64/0.60  fof(f880,plain,(
% 1.64/0.60    v2_struct_0(sK0) | v13_lattices(sK0) | (~spl9_9 | ~spl9_24 | spl9_26)),
% 1.64/0.60    inference(subsumption_resolution,[],[f879,f739])).
% 1.64/0.60  fof(f739,plain,(
% 1.64/0.60    m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~spl9_24),
% 1.64/0.60    inference(avatar_component_clause,[],[f738])).
% 1.64/0.60  fof(f738,plain,(
% 1.64/0.60    spl9_24 <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 1.64/0.60  fof(f879,plain,(
% 1.64/0.60    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0) | (~spl9_9 | spl9_26)),
% 1.64/0.60    inference(subsumption_resolution,[],[f878,f225])).
% 1.64/0.60  fof(f225,plain,(
% 1.64/0.60    l1_lattices(sK0) | ~spl9_9),
% 1.64/0.60    inference(avatar_component_clause,[],[f224])).
% 1.64/0.60  fof(f224,plain,(
% 1.64/0.60    spl9_9 <=> l1_lattices(sK0)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 1.64/0.60  fof(f878,plain,(
% 1.64/0.60    ~l1_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0) | spl9_26),
% 1.64/0.60    inference(resolution,[],[f857,f73])).
% 1.64/0.60  fof(f73,plain,(
% 1.64/0.60    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | v13_lattices(X0)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f32])).
% 1.64/0.60  fof(f32,plain,(
% 1.64/0.60    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.64/0.60    inference(flattening,[],[f31])).
% 1.64/0.60  fof(f31,plain,(
% 1.64/0.60    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.64/0.60    inference(ennf_transformation,[],[f11])).
% 1.64/0.60  fof(f11,axiom,(
% 1.64/0.60    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).
% 1.64/0.60  fof(f857,plain,(
% 1.64/0.60    ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | spl9_26),
% 1.64/0.60    inference(avatar_component_clause,[],[f855])).
% 1.64/0.60  fof(f855,plain,(
% 1.64/0.60    spl9_26 <=> m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 1.64/0.60  fof(f858,plain,(
% 1.64/0.60    ~spl9_26 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_16 | ~spl9_24),
% 1.64/0.60    inference(avatar_split_clause,[],[f802,f738,f497,f125,f120,f115,f110,f855])).
% 1.64/0.60  fof(f115,plain,(
% 1.64/0.60    spl9_2 <=> v10_lattices(sK0)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.64/0.60  fof(f120,plain,(
% 1.64/0.60    spl9_3 <=> v4_lattice3(sK0)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.64/0.60  fof(f125,plain,(
% 1.64/0.60    spl9_4 <=> l3_lattices(sK0)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.64/0.60  fof(f497,plain,(
% 1.64/0.60    spl9_16 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X2,sK3(sK0,X2)))),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 1.64/0.60  fof(f802,plain,(
% 1.64/0.60    ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_16 | ~spl9_24)),
% 1.64/0.60    inference(subsumption_resolution,[],[f797,f739])).
% 1.64/0.60  fof(f797,plain,(
% 1.64/0.60    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_16)),
% 1.64/0.60    inference(resolution,[],[f498,f418])).
% 1.64/0.60  fof(f418,plain,(
% 1.64/0.60    ( ! [X1] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 1.64/0.60    inference(superposition,[],[f360,f157])).
% 1.64/0.60  fof(f157,plain,(
% 1.64/0.60    ( ! [X2] : (k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 1.64/0.60    inference(subsumption_resolution,[],[f156,f127])).
% 1.64/0.60  fof(f127,plain,(
% 1.64/0.60    l3_lattices(sK0) | ~spl9_4),
% 1.64/0.60    inference(avatar_component_clause,[],[f125])).
% 1.64/0.60  fof(f156,plain,(
% 1.64/0.60    ( ! [X2] : (~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2) ) | (spl9_1 | ~spl9_2 | ~spl9_3)),
% 1.64/0.60    inference(subsumption_resolution,[],[f155,f112])).
% 1.64/0.60  fof(f155,plain,(
% 1.64/0.60    ( ! [X2] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2) ) | (~spl9_2 | ~spl9_3)),
% 1.64/0.60    inference(subsumption_resolution,[],[f141,f117])).
% 1.64/0.60  fof(f117,plain,(
% 1.64/0.60    v10_lattices(sK0) | ~spl9_2),
% 1.64/0.60    inference(avatar_component_clause,[],[f115])).
% 1.64/0.60  fof(f141,plain,(
% 1.64/0.60    ( ! [X2] : (~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2) ) | ~spl9_3),
% 1.64/0.60    inference(resolution,[],[f122,f81])).
% 1.64/0.60  fof(f81,plain,(
% 1.64/0.60    ( ! [X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) )),
% 1.64/0.60    inference(cnf_transformation,[],[f38])).
% 1.64/0.60  fof(f38,plain,(
% 1.64/0.60    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.64/0.60    inference(flattening,[],[f37])).
% 1.64/0.60  fof(f37,plain,(
% 1.64/0.60    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.64/0.60    inference(ennf_transformation,[],[f15])).
% 1.64/0.60  fof(f15,axiom,(
% 1.64/0.60    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattice3)).
% 1.64/0.60  fof(f122,plain,(
% 1.64/0.60    v4_lattice3(sK0) | ~spl9_3),
% 1.64/0.60    inference(avatar_component_clause,[],[f120])).
% 1.64/0.60  fof(f360,plain,(
% 1.64/0.60    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 1.64/0.60    inference(resolution,[],[f190,f54])).
% 1.64/0.60  fof(f54,plain,(
% 1.64/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f3])).
% 1.64/0.60  fof(f3,axiom,(
% 1.64/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.64/0.60  fof(f190,plain,(
% 1.64/0.60    ( ! [X0,X1] : (~r1_tarski(X1,a_2_5_lattice3(sK0,X0)) | r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 1.64/0.60    inference(superposition,[],[f163,f151])).
% 1.64/0.60  fof(f151,plain,(
% 1.64/0.60    ( ! [X0] : (k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 1.64/0.60    inference(subsumption_resolution,[],[f150,f127])).
% 1.64/0.60  fof(f150,plain,(
% 1.64/0.60    ( ! [X0] : (~l3_lattices(sK0) | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3)),
% 1.64/0.60    inference(subsumption_resolution,[],[f149,f112])).
% 1.64/0.60  fof(f149,plain,(
% 1.64/0.60    ( ! [X0] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))) ) | (~spl9_2 | ~spl9_3)),
% 1.64/0.60    inference(subsumption_resolution,[],[f139,f117])).
% 1.64/0.60  fof(f139,plain,(
% 1.64/0.60    ( ! [X0] : (~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))) ) | ~spl9_3),
% 1.64/0.60    inference(resolution,[],[f122,f79])).
% 1.64/0.60  fof(f79,plain,(
% 1.64/0.60    ( ! [X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) )),
% 1.64/0.60    inference(cnf_transformation,[],[f36])).
% 1.64/0.60  fof(f36,plain,(
% 1.64/0.60    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.64/0.60    inference(flattening,[],[f35])).
% 1.64/0.60  fof(f35,plain,(
% 1.64/0.60    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.64/0.60    inference(ennf_transformation,[],[f17])).
% 1.64/0.60  fof(f17,axiom,(
% 1.64/0.60    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).
% 1.64/0.60  fof(f163,plain,(
% 1.64/0.60    ( ! [X4,X5] : (r3_lattices(sK0,k15_lattice3(sK0,X4),k15_lattice3(sK0,X5)) | ~r1_tarski(X4,X5)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 1.64/0.60    inference(subsumption_resolution,[],[f162,f127])).
% 1.64/0.60  fof(f162,plain,(
% 1.64/0.60    ( ! [X4,X5] : (~l3_lattices(sK0) | ~r1_tarski(X4,X5) | r3_lattices(sK0,k15_lattice3(sK0,X4),k15_lattice3(sK0,X5))) ) | (spl9_1 | ~spl9_2 | ~spl9_3)),
% 1.64/0.60    inference(subsumption_resolution,[],[f161,f112])).
% 1.64/0.60  fof(f161,plain,(
% 1.64/0.60    ( ! [X4,X5] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | ~r1_tarski(X4,X5) | r3_lattices(sK0,k15_lattice3(sK0,X4),k15_lattice3(sK0,X5))) ) | (~spl9_2 | ~spl9_3)),
% 1.64/0.60    inference(subsumption_resolution,[],[f143,f117])).
% 1.64/0.60  fof(f143,plain,(
% 1.64/0.60    ( ! [X4,X5] : (~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~r1_tarski(X4,X5) | r3_lattices(sK0,k15_lattice3(sK0,X4),k15_lattice3(sK0,X5))) ) | ~spl9_3),
% 1.64/0.60    inference(resolution,[],[f122,f83])).
% 1.64/0.60  fof(f83,plain,(
% 1.64/0.60    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~r1_tarski(X1,X2) | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) )),
% 1.64/0.60    inference(cnf_transformation,[],[f40])).
% 1.64/0.60  fof(f40,plain,(
% 1.64/0.60    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.64/0.60    inference(flattening,[],[f39])).
% 1.64/0.60  fof(f39,plain,(
% 1.64/0.60    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.64/0.60    inference(ennf_transformation,[],[f16])).
% 1.64/0.60  fof(f16,axiom,(
% 1.64/0.60    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).
% 1.64/0.60  fof(f498,plain,(
% 1.64/0.60    ( ! [X2] : (~r3_lattices(sK0,X2,sK3(sK0,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl9_16),
% 1.64/0.60    inference(avatar_component_clause,[],[f497])).
% 1.64/0.60  fof(f750,plain,(
% 1.64/0.60    spl9_1 | ~spl9_4 | spl9_24),
% 1.64/0.60    inference(avatar_contradiction_clause,[],[f749])).
% 1.64/0.60  fof(f749,plain,(
% 1.64/0.60    $false | (spl9_1 | ~spl9_4 | spl9_24)),
% 1.64/0.60    inference(subsumption_resolution,[],[f748,f112])).
% 1.64/0.60  fof(f748,plain,(
% 1.64/0.60    v2_struct_0(sK0) | (~spl9_4 | spl9_24)),
% 1.64/0.60    inference(subsumption_resolution,[],[f747,f127])).
% 1.64/0.60  fof(f747,plain,(
% 1.64/0.60    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl9_24),
% 1.64/0.60    inference(resolution,[],[f740,f85])).
% 1.64/0.61  fof(f85,plain,(
% 1.64/0.61    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f42])).
% 1.64/0.61  fof(f42,plain,(
% 1.64/0.61    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.64/0.61    inference(flattening,[],[f41])).
% 1.64/0.61  fof(f41,plain,(
% 1.64/0.61    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.64/0.61    inference(ennf_transformation,[],[f13])).
% 1.64/0.61  fof(f13,axiom,(
% 1.64/0.61    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.64/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 1.64/0.61  fof(f740,plain,(
% 1.64/0.61    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | spl9_24),
% 1.64/0.61    inference(avatar_component_clause,[],[f738])).
% 1.64/0.61  fof(f741,plain,(
% 1.64/0.61    ~spl9_24 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_19),
% 1.64/0.61    inference(avatar_split_clause,[],[f731,f562,f255,f251,f248,f224,f184,f180,f125,f120,f115,f110,f738])).
% 1.64/0.61  fof(f180,plain,(
% 1.64/0.61    spl9_5 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.64/0.61  fof(f248,plain,(
% 1.64/0.61    spl9_10 <=> ! [X3,X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X2,X3) | r1_lattices(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)))),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.64/0.61  fof(f251,plain,(
% 1.64/0.61    spl9_11 <=> v9_lattices(sK0)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.64/0.61  fof(f255,plain,(
% 1.64/0.61    spl9_12 <=> v8_lattices(sK0)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.64/0.61  fof(f562,plain,(
% 1.64/0.61    spl9_19 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 1.64/0.61  fof(f731,plain,(
% 1.64/0.61    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_19)),
% 1.64/0.61    inference(subsumption_resolution,[],[f730,f563])).
% 1.64/0.61  fof(f563,plain,(
% 1.64/0.61    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl9_19),
% 1.64/0.61    inference(avatar_component_clause,[],[f562])).
% 1.64/0.61  fof(f730,plain,(
% 1.64/0.61    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_19)),
% 1.64/0.61    inference(subsumption_resolution,[],[f720,f182])).
% 1.64/0.61  fof(f182,plain,(
% 1.64/0.61    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl9_5),
% 1.64/0.61    inference(avatar_component_clause,[],[f180])).
% 1.64/0.61  fof(f720,plain,(
% 1.64/0.61    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_19)),
% 1.64/0.61    inference(resolution,[],[f712,f418])).
% 1.64/0.61  fof(f712,plain,(
% 1.64/0.61    ( ! [X1] : (~r3_lattices(sK0,X1,k5_lattices(sK0)) | k5_lattices(sK0) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_19)),
% 1.64/0.61    inference(duplicate_literal_removal,[],[f711])).
% 1.64/0.61  fof(f711,plain,(
% 1.64/0.61    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = X1 | ~r3_lattices(sK0,X1,k5_lattices(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_19)),
% 1.64/0.61    inference(superposition,[],[f673,f157])).
% 1.64/0.61  fof(f673,plain,(
% 1.64/0.61    ( ! [X1] : (~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | k5_lattices(sK0) = k15_lattice3(sK0,X1) | ~r3_lattices(sK0,k15_lattice3(sK0,X1),k5_lattices(sK0))) ) | (spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_19)),
% 1.64/0.61    inference(subsumption_resolution,[],[f667,f563])).
% 1.64/0.61  fof(f667,plain,(
% 1.64/0.61    ( ! [X1] : (k5_lattices(sK0) = k15_lattice3(sK0,X1) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,X1),k5_lattices(sK0))) ) | (spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_19)),
% 1.64/0.61    inference(superposition,[],[f599,f285])).
% 1.64/0.61  fof(f285,plain,(
% 1.64/0.61    ( ! [X2,X3] : (k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_lattices(sK0,X3,X2)) ) | (spl9_1 | ~spl9_4 | ~spl9_10 | ~spl9_11 | ~spl9_12)),
% 1.64/0.61    inference(duplicate_literal_removal,[],[f284])).
% 1.64/0.61  fof(f284,plain,(
% 1.64/0.61    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_lattices(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_4 | ~spl9_10 | ~spl9_11 | ~spl9_12)),
% 1.64/0.61    inference(resolution,[],[f273,f249])).
% 1.64/0.61  fof(f249,plain,(
% 1.64/0.61    ( ! [X2,X3] : (r1_lattices(sK0,X2,X3) | ~r3_lattices(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | ~spl9_10),
% 1.64/0.61    inference(avatar_component_clause,[],[f248])).
% 1.64/0.61  fof(f273,plain,(
% 1.64/0.61    ( ! [X10,X9] : (~r1_lattices(sK0,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | k2_lattices(sK0,X9,X10) = X9 | ~m1_subset_1(X9,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_4 | ~spl9_11 | ~spl9_12)),
% 1.64/0.61    inference(subsumption_resolution,[],[f265,f256])).
% 1.64/0.61  fof(f256,plain,(
% 1.64/0.61    v8_lattices(sK0) | ~spl9_12),
% 1.64/0.61    inference(avatar_component_clause,[],[f255])).
% 1.64/0.61  fof(f265,plain,(
% 1.64/0.61    ( ! [X10,X9] : (~v8_lattices(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | k2_lattices(sK0,X9,X10) = X9 | ~r1_lattices(sK0,X9,X10)) ) | (spl9_1 | ~spl9_4 | ~spl9_11)),
% 1.64/0.61    inference(subsumption_resolution,[],[f138,f252])).
% 1.64/0.61  fof(f252,plain,(
% 1.64/0.61    v9_lattices(sK0) | ~spl9_11),
% 1.64/0.61    inference(avatar_component_clause,[],[f251])).
% 1.64/0.61  fof(f138,plain,(
% 1.64/0.61    ( ! [X10,X9] : (~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | k2_lattices(sK0,X9,X10) = X9 | ~r1_lattices(sK0,X9,X10)) ) | (spl9_1 | ~spl9_4)),
% 1.64/0.61    inference(subsumption_resolution,[],[f134,f127])).
% 1.64/0.61  fof(f134,plain,(
% 1.64/0.61    ( ! [X10,X9] : (~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | k2_lattices(sK0,X9,X10) = X9 | ~r1_lattices(sK0,X9,X10)) ) | spl9_1),
% 1.64/0.61    inference(resolution,[],[f112,f64])).
% 1.64/0.61  fof(f64,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f26])).
% 1.64/0.61  fof(f26,plain,(
% 1.64/0.61    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.64/0.61    inference(flattening,[],[f25])).
% 1.64/0.61  fof(f25,plain,(
% 1.64/0.61    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 1.64/0.61    inference(ennf_transformation,[],[f10])).
% 1.64/0.61  fof(f10,axiom,(
% 1.64/0.61    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.64/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 1.64/0.61  fof(f599,plain,(
% 1.64/0.61    ( ! [X2] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0))) ) | (spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_9 | ~spl9_19)),
% 1.64/0.61    inference(subsumption_resolution,[],[f598,f112])).
% 1.64/0.61  fof(f598,plain,(
% 1.64/0.61    ( ! [X2] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0)) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_9 | ~spl9_19)),
% 1.64/0.61    inference(subsumption_resolution,[],[f590,f127])).
% 1.64/0.61  fof(f590,plain,(
% 1.64/0.61    ( ! [X2] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_6 | ~spl9_9 | ~spl9_19)),
% 1.64/0.61    inference(resolution,[],[f571,f85])).
% 1.64/0.61  fof(f571,plain,(
% 1.64/0.61    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0))) ) | (spl9_1 | ~spl9_6 | ~spl9_9 | ~spl9_19)),
% 1.64/0.61    inference(subsumption_resolution,[],[f516,f563])).
% 1.64/0.61  fof(f516,plain,(
% 1.64/0.61    ( ! [X4] : (~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0))) ) | (spl9_1 | ~spl9_6 | ~spl9_9)),
% 1.64/0.61    inference(subsumption_resolution,[],[f515,f112])).
% 1.64/0.61  fof(f515,plain,(
% 1.64/0.61    ( ! [X4] : (v2_struct_0(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0))) ) | (~spl9_6 | ~spl9_9)),
% 1.64/0.61    inference(subsumption_resolution,[],[f506,f225])).
% 1.64/0.61  fof(f506,plain,(
% 1.64/0.61    ( ! [X4] : (~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0))) ) | ~spl9_6),
% 1.64/0.61    inference(resolution,[],[f185,f101])).
% 1.64/0.61  fof(f101,plain,(
% 1.64/0.61    ( ! [X2,X0] : (~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0))) )),
% 1.64/0.61    inference(equality_resolution,[],[f68])).
% 1.64/0.61  fof(f68,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X2,X1) = X1 | k5_lattices(X0) != X1) )),
% 1.64/0.61    inference(cnf_transformation,[],[f30])).
% 1.64/0.61  fof(f30,plain,(
% 1.64/0.61    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.64/0.61    inference(flattening,[],[f29])).
% 1.64/0.61  fof(f29,plain,(
% 1.64/0.61    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.64/0.61    inference(ennf_transformation,[],[f6])).
% 1.64/0.61  fof(f6,axiom,(
% 1.64/0.61    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 1.64/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 1.64/0.61  fof(f185,plain,(
% 1.64/0.61    v13_lattices(sK0) | ~spl9_6),
% 1.64/0.61    inference(avatar_component_clause,[],[f184])).
% 1.64/0.61  fof(f570,plain,(
% 1.64/0.61    spl9_1 | ~spl9_9 | spl9_19),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f569])).
% 1.64/0.61  fof(f569,plain,(
% 1.64/0.61    $false | (spl9_1 | ~spl9_9 | spl9_19)),
% 1.64/0.61    inference(subsumption_resolution,[],[f568,f112])).
% 1.64/0.61  fof(f568,plain,(
% 1.64/0.61    v2_struct_0(sK0) | (~spl9_9 | spl9_19)),
% 1.64/0.61    inference(subsumption_resolution,[],[f567,f225])).
% 1.64/0.61  fof(f567,plain,(
% 1.64/0.61    ~l1_lattices(sK0) | v2_struct_0(sK0) | spl9_19),
% 1.64/0.61    inference(resolution,[],[f564,f65])).
% 1.64/0.61  fof(f65,plain,(
% 1.64/0.61    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f28])).
% 1.64/0.61  fof(f28,plain,(
% 1.64/0.61    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.64/0.61    inference(flattening,[],[f27])).
% 1.64/0.61  fof(f27,plain,(
% 1.64/0.61    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.64/0.61    inference(ennf_transformation,[],[f7])).
% 1.64/0.61  fof(f7,axiom,(
% 1.64/0.61    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 1.64/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 1.64/0.61  fof(f564,plain,(
% 1.64/0.61    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | spl9_19),
% 1.64/0.61    inference(avatar_component_clause,[],[f562])).
% 1.64/0.61  fof(f499,plain,(
% 1.64/0.61    spl9_6 | spl9_16 | spl9_1 | ~spl9_4 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_15),
% 1.64/0.61    inference(avatar_split_clause,[],[f490,f429,f255,f251,f248,f224,f125,f110,f497,f184])).
% 1.64/0.61  fof(f429,plain,(
% 1.64/0.61    spl9_15 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X2,sK3(sK0,X2)) != X2)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 1.64/0.61  fof(f490,plain,(
% 1.64/0.61    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X2,sK3(sK0,X2)) | v13_lattices(sK0)) ) | (spl9_1 | ~spl9_4 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_15)),
% 1.64/0.61    inference(subsumption_resolution,[],[f489,f112])).
% 1.64/0.61  fof(f489,plain,(
% 1.64/0.61    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X2,sK3(sK0,X2)) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (spl9_1 | ~spl9_4 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_15)),
% 1.64/0.61    inference(subsumption_resolution,[],[f488,f225])).
% 1.64/0.61  fof(f488,plain,(
% 1.64/0.61    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X2,sK3(sK0,X2)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (spl9_1 | ~spl9_4 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_15)),
% 1.64/0.61    inference(duplicate_literal_removal,[],[f487])).
% 1.64/0.61  fof(f487,plain,(
% 1.64/0.61    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X2,sK3(sK0,X2)) | ~l1_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (spl9_1 | ~spl9_4 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_15)),
% 1.64/0.61    inference(resolution,[],[f434,f73])).
% 1.64/0.61  fof(f434,plain,(
% 1.64/0.61    ( ! [X0] : (~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,sK3(sK0,X0))) ) | (spl9_1 | ~spl9_4 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_15)),
% 1.64/0.61    inference(trivial_inequality_removal,[],[f433])).
% 1.64/0.61  fof(f433,plain,(
% 1.64/0.61    ( ! [X0] : (X0 != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,sK3(sK0,X0))) ) | (spl9_1 | ~spl9_4 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_15)),
% 1.64/0.61    inference(duplicate_literal_removal,[],[f432])).
% 1.64/0.61  fof(f432,plain,(
% 1.64/0.61    ( ! [X0] : (X0 != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,sK3(sK0,X0))) ) | (spl9_1 | ~spl9_4 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_15)),
% 1.64/0.61    inference(superposition,[],[f430,f285])).
% 1.64/0.61  fof(f430,plain,(
% 1.64/0.61    ( ! [X2] : (k2_lattices(sK0,X2,sK3(sK0,X2)) != X2 | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl9_15),
% 1.64/0.61    inference(avatar_component_clause,[],[f429])).
% 1.64/0.61  fof(f431,plain,(
% 1.64/0.61    spl9_6 | spl9_15 | spl9_1 | ~spl9_8 | ~spl9_9 | ~spl9_13),
% 1.64/0.61    inference(avatar_split_clause,[],[f416,f292,f224,f221,f110,f429,f184])).
% 1.64/0.61  fof(f221,plain,(
% 1.64/0.61    spl9_8 <=> ! [X5,X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | k2_lattices(sK0,X4,X5) = k2_lattices(sK0,X5,X4) | ~m1_subset_1(X5,u1_struct_0(sK0)))),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 1.64/0.61  fof(f292,plain,(
% 1.64/0.61    spl9_13 <=> ! [X6] : (~m1_subset_1(X6,u1_struct_0(sK0)) | k2_lattices(sK0,sK3(sK0,X6),X6) != X6 | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 1.64/0.61  fof(f416,plain,(
% 1.64/0.61    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X2,sK3(sK0,X2)) != X2 | v13_lattices(sK0)) ) | (spl9_1 | ~spl9_8 | ~spl9_9 | ~spl9_13)),
% 1.64/0.61    inference(subsumption_resolution,[],[f415,f112])).
% 1.64/0.61  fof(f415,plain,(
% 1.64/0.61    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X2,sK3(sK0,X2)) != X2 | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (~spl9_8 | ~spl9_9 | ~spl9_13)),
% 1.64/0.61    inference(subsumption_resolution,[],[f414,f225])).
% 1.64/0.61  fof(f414,plain,(
% 1.64/0.61    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X2,sK3(sK0,X2)) != X2 | ~l1_lattices(sK0) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (~spl9_8 | ~spl9_13)),
% 1.64/0.61    inference(duplicate_literal_removal,[],[f413])).
% 1.64/0.61  fof(f413,plain,(
% 1.64/0.61    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X2,sK3(sK0,X2)) != X2 | ~l1_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (~spl9_8 | ~spl9_13)),
% 1.64/0.61    inference(resolution,[],[f298,f73])).
% 1.64/0.61  fof(f298,plain,(
% 1.64/0.61    ( ! [X0] : (~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0) ) | (~spl9_8 | ~spl9_13)),
% 1.64/0.61    inference(duplicate_literal_removal,[],[f295])).
% 1.64/0.61  fof(f295,plain,(
% 1.64/0.61    ( ! [X0] : (k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))) ) | (~spl9_8 | ~spl9_13)),
% 1.64/0.61    inference(superposition,[],[f293,f222])).
% 1.64/0.61  fof(f222,plain,(
% 1.64/0.61    ( ! [X4,X5] : (k2_lattices(sK0,X4,X5) = k2_lattices(sK0,X5,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | ~spl9_8),
% 1.64/0.61    inference(avatar_component_clause,[],[f221])).
% 1.64/0.61  fof(f293,plain,(
% 1.64/0.61    ( ! [X6] : (k2_lattices(sK0,sK3(sK0,X6),X6) != X6 | ~m1_subset_1(X6,u1_struct_0(sK0)) | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6) ) | ~spl9_13),
% 1.64/0.61    inference(avatar_component_clause,[],[f292])).
% 1.64/0.61  fof(f294,plain,(
% 1.64/0.61    spl9_6 | spl9_13 | spl9_1 | ~spl9_9),
% 1.64/0.61    inference(avatar_split_clause,[],[f238,f224,f110,f292,f184])).
% 1.64/0.61  fof(f238,plain,(
% 1.64/0.61    ( ! [X6] : (~m1_subset_1(X6,u1_struct_0(sK0)) | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6 | k2_lattices(sK0,sK3(sK0,X6),X6) != X6 | v13_lattices(sK0)) ) | (spl9_1 | ~spl9_9)),
% 1.64/0.61    inference(subsumption_resolution,[],[f132,f225])).
% 1.64/0.61  fof(f132,plain,(
% 1.64/0.61    ( ! [X6] : (~l1_lattices(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6 | k2_lattices(sK0,sK3(sK0,X6),X6) != X6 | v13_lattices(sK0)) ) | spl9_1),
% 1.64/0.61    inference(resolution,[],[f112,f72])).
% 1.64/0.61  fof(f72,plain,(
% 1.64/0.61    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k2_lattices(X0,X1,sK3(X0,X1)) != X1 | k2_lattices(X0,sK3(X0,X1),X1) != X1 | v13_lattices(X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f32])).
% 1.64/0.61  fof(f271,plain,(
% 1.64/0.61    spl9_1 | ~spl9_2 | ~spl9_4 | spl9_12),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f270])).
% 1.64/0.61  fof(f270,plain,(
% 1.64/0.61    $false | (spl9_1 | ~spl9_2 | ~spl9_4 | spl9_12)),
% 1.64/0.61    inference(subsumption_resolution,[],[f269,f127])).
% 1.64/0.61  fof(f269,plain,(
% 1.64/0.61    ~l3_lattices(sK0) | (spl9_1 | ~spl9_2 | spl9_12)),
% 1.64/0.61    inference(subsumption_resolution,[],[f268,f117])).
% 1.64/0.61  fof(f268,plain,(
% 1.64/0.61    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl9_1 | spl9_12)),
% 1.64/0.61    inference(subsumption_resolution,[],[f267,f112])).
% 1.64/0.61  fof(f267,plain,(
% 1.64/0.61    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl9_12),
% 1.64/0.61    inference(resolution,[],[f257,f61])).
% 1.64/0.61  fof(f61,plain,(
% 1.64/0.61    ( ! [X0] : (v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f24])).
% 1.64/0.61  fof(f24,plain,(
% 1.64/0.61    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.64/0.61    inference(flattening,[],[f23])).
% 1.64/0.61  fof(f23,plain,(
% 1.64/0.61    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.64/0.61    inference(ennf_transformation,[],[f5])).
% 1.64/0.61  fof(f5,axiom,(
% 1.64/0.61    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.64/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 1.64/0.61  fof(f257,plain,(
% 1.64/0.61    ~v8_lattices(sK0) | spl9_12),
% 1.64/0.61    inference(avatar_component_clause,[],[f255])).
% 1.64/0.61  fof(f263,plain,(
% 1.64/0.61    spl9_1 | ~spl9_2 | ~spl9_4 | spl9_11),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f262])).
% 1.64/0.61  fof(f262,plain,(
% 1.64/0.61    $false | (spl9_1 | ~spl9_2 | ~spl9_4 | spl9_11)),
% 1.64/0.61    inference(subsumption_resolution,[],[f261,f127])).
% 1.64/0.61  fof(f261,plain,(
% 1.64/0.61    ~l3_lattices(sK0) | (spl9_1 | ~spl9_2 | spl9_11)),
% 1.64/0.61    inference(subsumption_resolution,[],[f260,f117])).
% 1.64/0.61  fof(f260,plain,(
% 1.64/0.61    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl9_1 | spl9_11)),
% 1.64/0.61    inference(subsumption_resolution,[],[f259,f112])).
% 1.64/0.61  fof(f259,plain,(
% 1.64/0.61    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl9_11),
% 1.64/0.61    inference(resolution,[],[f253,f62])).
% 1.64/0.61  fof(f62,plain,(
% 1.64/0.61    ( ! [X0] : (v9_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f24])).
% 1.64/0.61  fof(f253,plain,(
% 1.64/0.61    ~v9_lattices(sK0) | spl9_11),
% 1.64/0.61    inference(avatar_component_clause,[],[f251])).
% 1.64/0.61  fof(f258,plain,(
% 1.64/0.61    spl9_10 | ~spl9_11 | ~spl9_12 | spl9_1 | ~spl9_4 | ~spl9_7),
% 1.64/0.61    inference(avatar_split_clause,[],[f233,f217,f125,f110,f255,f251,f248])).
% 1.64/0.61  fof(f217,plain,(
% 1.64/0.61    spl9_7 <=> v6_lattices(sK0)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.64/0.61  fof(f233,plain,(
% 1.64/0.61    ( ! [X2,X3] : (~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,X2,X3) | ~r3_lattices(sK0,X2,X3)) ) | (spl9_1 | ~spl9_4 | ~spl9_7)),
% 1.64/0.61    inference(subsumption_resolution,[],[f136,f218])).
% 1.64/0.61  fof(f218,plain,(
% 1.64/0.61    v6_lattices(sK0) | ~spl9_7),
% 1.64/0.61    inference(avatar_component_clause,[],[f217])).
% 1.64/0.61  fof(f136,plain,(
% 1.64/0.61    ( ! [X2,X3] : (~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,X2,X3) | ~r3_lattices(sK0,X2,X3)) ) | (spl9_1 | ~spl9_4)),
% 1.64/0.61    inference(subsumption_resolution,[],[f130,f127])).
% 1.64/0.61  fof(f130,plain,(
% 1.64/0.61    ( ! [X2,X3] : (~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,X2,X3) | ~r3_lattices(sK0,X2,X3)) ) | spl9_1),
% 1.64/0.61    inference(resolution,[],[f112,f94])).
% 1.64/0.61  fof(f94,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f46])).
% 1.64/0.61  fof(f46,plain,(
% 1.64/0.61    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.64/0.61    inference(flattening,[],[f45])).
% 1.64/0.61  fof(f45,plain,(
% 1.64/0.61    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.64/0.61    inference(ennf_transformation,[],[f9])).
% 1.64/0.61  fof(f9,axiom,(
% 1.64/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.64/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 1.64/0.61  fof(f237,plain,(
% 1.64/0.61    ~spl9_4 | spl9_9),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f236])).
% 1.64/0.61  fof(f236,plain,(
% 1.64/0.61    $false | (~spl9_4 | spl9_9)),
% 1.64/0.61    inference(subsumption_resolution,[],[f235,f127])).
% 1.64/0.61  fof(f235,plain,(
% 1.64/0.61    ~l3_lattices(sK0) | spl9_9),
% 1.64/0.61    inference(resolution,[],[f226,f55])).
% 1.64/0.61  fof(f55,plain,(
% 1.64/0.61    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f22])).
% 1.64/0.61  fof(f22,plain,(
% 1.64/0.61    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.64/0.61    inference(ennf_transformation,[],[f8])).
% 1.64/0.61  fof(f8,axiom,(
% 1.64/0.61    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.64/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 1.64/0.61  fof(f226,plain,(
% 1.64/0.61    ~l1_lattices(sK0) | spl9_9),
% 1.64/0.61    inference(avatar_component_clause,[],[f224])).
% 1.64/0.61  fof(f232,plain,(
% 1.64/0.61    spl9_1 | ~spl9_2 | ~spl9_4 | spl9_7),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f231])).
% 1.64/0.61  fof(f231,plain,(
% 1.64/0.61    $false | (spl9_1 | ~spl9_2 | ~spl9_4 | spl9_7)),
% 1.64/0.61    inference(subsumption_resolution,[],[f230,f127])).
% 1.64/0.61  fof(f230,plain,(
% 1.64/0.61    ~l3_lattices(sK0) | (spl9_1 | ~spl9_2 | spl9_7)),
% 1.64/0.61    inference(subsumption_resolution,[],[f229,f117])).
% 1.64/0.61  fof(f229,plain,(
% 1.64/0.61    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl9_1 | spl9_7)),
% 1.64/0.61    inference(subsumption_resolution,[],[f228,f112])).
% 1.64/0.61  fof(f228,plain,(
% 1.64/0.61    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl9_7),
% 1.64/0.61    inference(resolution,[],[f219,f59])).
% 1.64/0.61  fof(f59,plain,(
% 1.64/0.61    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f24])).
% 1.64/0.61  fof(f219,plain,(
% 1.64/0.61    ~v6_lattices(sK0) | spl9_7),
% 1.64/0.61    inference(avatar_component_clause,[],[f217])).
% 1.64/0.61  fof(f227,plain,(
% 1.64/0.61    ~spl9_7 | spl9_8 | ~spl9_9 | spl9_1),
% 1.64/0.61    inference(avatar_split_clause,[],[f131,f110,f224,f221,f217])).
% 1.64/0.61  fof(f131,plain,(
% 1.64/0.61    ( ! [X4,X5] : (~l1_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k2_lattices(sK0,X4,X5) = k2_lattices(sK0,X5,X4) | ~v6_lattices(sK0)) ) | spl9_1),
% 1.64/0.61    inference(resolution,[],[f112,f77])).
% 1.64/0.61  fof(f77,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~v6_lattices(X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f34])).
% 1.64/0.61  fof(f34,plain,(
% 1.64/0.61    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.64/0.61    inference(flattening,[],[f33])).
% 1.64/0.61  fof(f33,plain,(
% 1.64/0.61    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.64/0.61    inference(ennf_transformation,[],[f12])).
% 1.64/0.61  fof(f12,axiom,(
% 1.64/0.61    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 1.64/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).
% 1.64/0.61  fof(f187,plain,(
% 1.64/0.61    ~spl9_5 | ~spl9_6),
% 1.64/0.61    inference(avatar_split_clause,[],[f108,f184,f180])).
% 1.64/0.61  fof(f108,plain,(
% 1.64/0.61    ~v13_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 1.64/0.61    inference(subsumption_resolution,[],[f107,f53])).
% 1.64/0.61  fof(f53,plain,(
% 1.64/0.61    l3_lattices(sK0)),
% 1.64/0.61    inference(cnf_transformation,[],[f21])).
% 1.64/0.61  fof(f21,plain,(
% 1.64/0.61    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.64/0.61    inference(flattening,[],[f20])).
% 1.64/0.61  fof(f20,plain,(
% 1.64/0.61    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.64/0.61    inference(ennf_transformation,[],[f19])).
% 1.64/0.61  fof(f19,negated_conjecture,(
% 1.64/0.61    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.64/0.61    inference(negated_conjecture,[],[f18])).
% 1.64/0.61  fof(f18,conjecture,(
% 1.64/0.61    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.64/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).
% 1.64/0.61  fof(f107,plain,(
% 1.64/0.61    ~v13_lattices(sK0) | ~l3_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 1.64/0.61    inference(subsumption_resolution,[],[f106,f51])).
% 1.64/0.61  fof(f51,plain,(
% 1.64/0.61    v10_lattices(sK0)),
% 1.64/0.61    inference(cnf_transformation,[],[f21])).
% 1.64/0.61  fof(f106,plain,(
% 1.64/0.61    ~v10_lattices(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 1.64/0.61    inference(subsumption_resolution,[],[f49,f50])).
% 1.64/0.61  fof(f50,plain,(
% 1.64/0.61    ~v2_struct_0(sK0)),
% 1.64/0.61    inference(cnf_transformation,[],[f21])).
% 1.64/0.61  fof(f49,plain,(
% 1.64/0.61    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 1.64/0.61    inference(cnf_transformation,[],[f21])).
% 1.64/0.61  fof(f128,plain,(
% 1.64/0.61    spl9_4),
% 1.64/0.61    inference(avatar_split_clause,[],[f53,f125])).
% 1.64/0.61  fof(f123,plain,(
% 1.64/0.61    spl9_3),
% 1.64/0.61    inference(avatar_split_clause,[],[f52,f120])).
% 1.64/0.61  fof(f52,plain,(
% 1.64/0.61    v4_lattice3(sK0)),
% 1.64/0.61    inference(cnf_transformation,[],[f21])).
% 1.64/0.61  fof(f118,plain,(
% 1.64/0.61    spl9_2),
% 1.64/0.61    inference(avatar_split_clause,[],[f51,f115])).
% 1.64/0.61  fof(f113,plain,(
% 1.64/0.61    ~spl9_1),
% 1.64/0.61    inference(avatar_split_clause,[],[f50,f110])).
% 1.64/0.61  % SZS output end Proof for theBenchmark
% 1.64/0.61  % (10247)------------------------------
% 1.64/0.61  % (10247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.61  % (10247)Termination reason: Refutation
% 1.64/0.61  
% 1.64/0.61  % (10247)Memory used [KB]: 11385
% 1.64/0.61  % (10247)Time elapsed: 0.197 s
% 1.64/0.61  % (10247)------------------------------
% 1.64/0.61  % (10247)------------------------------
% 1.64/0.62  % (10226)Success in time 0.253 s
%------------------------------------------------------------------------------
