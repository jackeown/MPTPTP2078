%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:09 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 386 expanded)
%              Number of leaves         :   39 ( 151 expanded)
%              Depth                    :   11
%              Number of atoms          :  503 ( 915 expanded)
%              Number of equality atoms :   93 ( 207 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1684,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f73,f92,f99,f128,f136,f140,f154,f212,f213,f220,f228,f241,f256,f515,f601,f687,f704,f896,f1460,f1630,f1669,f1675])).

fof(f1675,plain,
    ( spl2_11
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(avatar_contradiction_clause,[],[f1674])).

fof(f1674,plain,
    ( $false
    | spl2_11
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f186,f237])).

fof(f237,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f236,f229])).

fof(f229,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_16 ),
    inference(superposition,[],[f211,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f211,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl2_16
  <=> k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f236,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_17 ),
    inference(superposition,[],[f55,f219])).

fof(f219,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl2_17
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f186,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl2_11
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f1669,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_17
    | ~ spl2_60
    | ~ spl2_72
    | ~ spl2_102 ),
    inference(avatar_contradiction_clause,[],[f1668])).

fof(f1668,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_17
    | ~ spl2_60
    | ~ spl2_72
    | ~ spl2_102 ),
    inference(subsumption_resolution,[],[f1647,f1667])).

fof(f1667,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_17
    | ~ spl2_60 ),
    inference(subsumption_resolution,[],[f719,f1666])).

fof(f1666,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f84,f1665])).

fof(f1665,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f197,f237])).

fof(f197,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f37,f81])).

fof(f81,plain,
    ( ! [X1] : k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1)
    | ~ spl2_3 ),
    inference(resolution,[],[f72,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f72,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f37,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f84,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f83,f64])).

fof(f64,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f83,plain,
    ( ~ v2_pre_topc(sK0)
    | sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f75,f68])).

fof(f68,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f75,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f72,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f719,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_60 ),
    inference(resolution,[],[f703,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f703,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_60 ),
    inference(avatar_component_clause,[],[f702])).

fof(f702,plain,
    ( spl2_60
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).

fof(f1647,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_72
    | ~ spl2_102 ),
    inference(forward_demodulation,[],[f1639,f895])).

fof(f895,plain,
    ( sK1 = k2_xboole_0(sK1,sK1)
    | ~ spl2_72 ),
    inference(avatar_component_clause,[],[f894])).

fof(f894,plain,
    ( spl2_72
  <=> sK1 = k2_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).

fof(f1639,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,sK1))
    | ~ spl2_102 ),
    inference(resolution,[],[f1629,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f1629,plain,
    ( r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1)
    | ~ spl2_102 ),
    inference(avatar_component_clause,[],[f1628])).

fof(f1628,plain,
    ( spl2_102
  <=> r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_102])])).

fof(f1630,plain,
    ( spl2_102
    | ~ spl2_11
    | ~ spl2_72
    | ~ spl2_96 ),
    inference(avatar_split_clause,[],[f1626,f1458,f894,f138,f1628])).

fof(f1458,plain,
    ( spl2_96
  <=> k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).

fof(f1626,plain,
    ( r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1)
    | ~ spl2_11
    | ~ spl2_72
    | ~ spl2_96 ),
    inference(forward_demodulation,[],[f1625,f895])).

fof(f1625,plain,
    ( r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,sK1)),sK1)
    | ~ spl2_11
    | ~ spl2_72
    | ~ spl2_96 ),
    inference(forward_demodulation,[],[f1620,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1620,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1),sK1)
    | ~ spl2_11
    | ~ spl2_72
    | ~ spl2_96 ),
    inference(superposition,[],[f921,f1459])).

fof(f1459,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_96 ),
    inference(avatar_component_clause,[],[f1458])).

fof(f921,plain,
    ( ! [X5] : r1_tarski(k4_xboole_0(k3_xboole_0(X5,k2_tops_1(sK0,sK1)),sK1),sK1)
    | ~ spl2_11
    | ~ spl2_72 ),
    inference(resolution,[],[f908,f418])).

fof(f418,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(X0,k2_tops_1(sK0,sK1)),sK1)
    | ~ spl2_11 ),
    inference(superposition,[],[f383,f58])).

fof(f383,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k2_tops_1(sK0,sK1),X0),sK1)
    | ~ spl2_11 ),
    inference(superposition,[],[f374,f55])).

fof(f374,plain,
    ( ! [X2] : r1_tarski(k4_xboole_0(k2_tops_1(sK0,sK1),X2),sK1)
    | ~ spl2_11 ),
    inference(superposition,[],[f53,f204])).

fof(f204,plain,
    ( ! [X0] : k4_xboole_0(k2_tops_1(sK0,sK1),X0) = k4_xboole_0(sK1,k2_xboole_0(k1_tops_1(sK0,sK1),X0))
    | ~ spl2_11 ),
    inference(superposition,[],[f54,f139])).

fof(f139,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f908,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | r1_tarski(k4_xboole_0(X0,sK1),sK1) )
    | ~ spl2_72 ),
    inference(superposition,[],[f51,f895])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f1460,plain,
    ( spl2_96
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f532,f513,f1458])).

fof(f513,plain,
    ( spl2_47
  <=> r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f532,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_47 ),
    inference(resolution,[],[f514,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f514,plain,
    ( r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f513])).

fof(f896,plain,
    ( spl2_72
    | ~ spl2_11
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f884,f218,f138,f894])).

fof(f884,plain,
    ( sK1 = k2_xboole_0(sK1,sK1)
    | ~ spl2_11
    | ~ spl2_17 ),
    inference(superposition,[],[f437,f415])).

fof(f415,plain,
    ( ! [X2] : sK1 = k2_xboole_0(k3_xboole_0(k2_tops_1(sK0,sK1),X2),sK1)
    | ~ spl2_11 ),
    inference(resolution,[],[f383,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f437,plain,
    ( ! [X2] : k2_xboole_0(X2,sK1) = k2_xboole_0(sK1,k2_xboole_0(X2,sK1))
    | ~ spl2_11
    | ~ spl2_17 ),
    inference(resolution,[],[f432,f52])).

fof(f432,plain,
    ( ! [X0] : r1_tarski(sK1,k2_xboole_0(X0,sK1))
    | ~ spl2_11
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f425,f405])).

fof(f405,plain,
    ( ! [X3] : k2_xboole_0(X3,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k2_xboole_0(X3,sK1))
    | ~ spl2_11 ),
    inference(resolution,[],[f378,f52])).

fof(f378,plain,
    ( ! [X0] : r1_tarski(k2_tops_1(sK0,sK1),k2_xboole_0(X0,sK1))
    | ~ spl2_11 ),
    inference(resolution,[],[f374,f50])).

fof(f425,plain,
    ( ! [X0] : r1_tarski(sK1,k2_xboole_0(k2_tops_1(sK0,sK1),k2_xboole_0(X0,sK1)))
    | ~ spl2_17 ),
    inference(resolution,[],[f391,f235])).

fof(f235,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),X1)
        | r1_tarski(sK1,k2_xboole_0(k2_tops_1(sK0,sK1),X1)) )
    | ~ spl2_17 ),
    inference(superposition,[],[f50,f219])).

fof(f391,plain,
    ( ! [X0] : r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(X0,sK1))
    | ~ spl2_17 ),
    inference(resolution,[],[f387,f50])).

fof(f387,plain,
    ( ! [X2] : r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),X2),sK1)
    | ~ spl2_17 ),
    inference(superposition,[],[f53,f233])).

fof(f233,plain,
    ( ! [X0] : k4_xboole_0(sK1,k2_xboole_0(k2_tops_1(sK0,sK1),X0)) = k4_xboole_0(k1_tops_1(sK0,sK1),X0)
    | ~ spl2_17 ),
    inference(superposition,[],[f54,f219])).

fof(f704,plain,
    ( spl2_60
    | ~ spl2_19
    | ~ spl2_57 ),
    inference(avatar_split_clause,[],[f696,f685,f226,f702])).

fof(f226,plain,
    ( spl2_19
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f685,plain,
    ( spl2_57
  <=> r1_tarski(k4_xboole_0(sK1,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f696,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_19
    | ~ spl2_57 ),
    inference(forward_demodulation,[],[f692,f227])).

fof(f227,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f226])).

fof(f692,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_57 ),
    inference(resolution,[],[f686,f50])).

fof(f686,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f685])).

fof(f687,plain,
    ( spl2_57
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f667,f599,f685])).

fof(f599,plain,
    ( spl2_55
  <=> k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f667,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_55 ),
    inference(superposition,[],[f53,f600])).

fof(f600,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_xboole_0(sK1,sK1)
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f599])).

fof(f601,plain,
    ( spl2_55
    | ~ spl2_11
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f372,f254,f138,f599])).

fof(f254,plain,
    ( spl2_23
  <=> sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f372,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_xboole_0(sK1,sK1)
    | ~ spl2_11
    | ~ spl2_23 ),
    inference(superposition,[],[f204,f255])).

fof(f255,plain,
    ( sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f254])).

fof(f515,plain,
    ( spl2_47
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f364,f226,f513])).

fof(f364,plain,
    ( r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_19 ),
    inference(resolution,[],[f242,f61])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
        | r1_tarski(k4_xboole_0(X0,sK1),k2_tops_1(sK0,sK1)) )
    | ~ spl2_19 ),
    inference(superposition,[],[f51,f227])).

fof(f256,plain,
    ( spl2_23
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f244,f239,f254])).

fof(f239,plain,
    ( spl2_20
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f244,plain,
    ( sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_20 ),
    inference(resolution,[],[f240,f52])).

fof(f240,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f239])).

fof(f241,plain,
    ( spl2_20
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f234,f218,f239])).

fof(f234,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_17 ),
    inference(superposition,[],[f53,f219])).

fof(f228,plain,
    ( spl2_19
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f191,f126,f90,f71,f226])).

fof(f90,plain,
    ( spl2_4
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f126,plain,
    ( spl2_8
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f191,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f189,f127])).

fof(f127,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f189,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f80,f91])).

fof(f91,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(sK1,X0) = k4_subset_1(u1_struct_0(sK0),sK1,X0) )
    | ~ spl2_3 ),
    inference(resolution,[],[f72,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f220,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f184,f134,f71,f218])).

fof(f134,plain,
    ( spl2_10
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f184,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(superposition,[],[f135,f81])).

fof(f135,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f213,plain,
    ( spl2_13
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f205,f138,f152])).

fof(f152,plain,
    ( spl2_13
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f205,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_11 ),
    inference(superposition,[],[f53,f139])).

fof(f212,plain,
    ( spl2_16
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f159,f152,f210])).

fof(f159,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_13 ),
    inference(resolution,[],[f153,f57])).

fof(f153,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f152])).

fof(f154,plain,
    ( spl2_13
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f149,f94,f71,f67,f152])).

fof(f94,plain,
    ( spl2_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f149,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f86,f95])).

fof(f95,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f86,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f77,f68])).

fof(f77,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f72,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f140,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f123,f97,f71,f138])).

fof(f97,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f123,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f81,f98])).

fof(f98,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f136,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f88,f71,f67,f134])).

fof(f88,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f79,f68])).

fof(f79,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f72,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f128,plain,
    ( spl2_8
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f82,f71,f67,f126])).

fof(f82,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f74,f68])).

fof(f74,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f72,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f99,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f36,f97,f94])).

fof(f36,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f92,plain,
    ( spl2_4
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f87,f71,f67,f90])).

fof(f87,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f78,f68])).

fof(f78,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(resolution,[],[f72,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f73,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f38,f71])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f40,f67])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f39,f63])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (2827)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.49  % (2847)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.50  % (2856)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (2831)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (2825)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (2850)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (2828)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (2829)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (2856)Refutation not found, incomplete strategy% (2856)------------------------------
% 0.21/0.51  % (2856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2848)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (2840)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (2856)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2856)Memory used [KB]: 1663
% 0.21/0.51  % (2856)Time elapsed: 0.117 s
% 0.21/0.51  % (2856)------------------------------
% 0.21/0.51  % (2856)------------------------------
% 0.21/0.51  % (2846)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (2839)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (2837)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.22/0.52  % (2826)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.22/0.52  % (2851)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.22/0.52  % (2832)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.22/0.52  % (2842)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.22/0.53  % (2838)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.22/0.53  % (2835)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.22/0.53  % (2834)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.22/0.53  % (2830)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.22/0.53  % (2849)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.37/0.53  % (2842)Refutation not found, incomplete strategy% (2842)------------------------------
% 1.37/0.53  % (2842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (2841)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.37/0.53  % (2854)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.37/0.54  % (2844)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.37/0.54  % (2852)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.37/0.54  % (2843)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.37/0.54  % (2842)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (2842)Memory used [KB]: 10618
% 1.37/0.54  % (2842)Time elapsed: 0.131 s
% 1.37/0.54  % (2842)------------------------------
% 1.37/0.54  % (2842)------------------------------
% 1.37/0.54  % (2835)Refutation not found, incomplete strategy% (2835)------------------------------
% 1.37/0.54  % (2835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (2835)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (2835)Memory used [KB]: 10874
% 1.37/0.54  % (2835)Time elapsed: 0.145 s
% 1.37/0.54  % (2835)------------------------------
% 1.37/0.54  % (2835)------------------------------
% 1.37/0.54  % (2855)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.37/0.55  % (2833)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.37/0.55  % (2855)Refutation not found, incomplete strategy% (2855)------------------------------
% 1.37/0.55  % (2855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (2855)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (2855)Memory used [KB]: 10874
% 1.37/0.55  % (2855)Time elapsed: 0.143 s
% 1.37/0.55  % (2855)------------------------------
% 1.37/0.55  % (2855)------------------------------
% 1.37/0.55  % (2845)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 2.04/0.66  % (2893)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.04/0.67  % (2904)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.04/0.68  % (2852)Refutation found. Thanks to Tanya!
% 2.04/0.68  % SZS status Theorem for theBenchmark
% 2.04/0.68  % SZS output start Proof for theBenchmark
% 2.04/0.68  fof(f1684,plain,(
% 2.04/0.68    $false),
% 2.04/0.68    inference(avatar_sat_refutation,[],[f65,f69,f73,f92,f99,f128,f136,f140,f154,f212,f213,f220,f228,f241,f256,f515,f601,f687,f704,f896,f1460,f1630,f1669,f1675])).
% 2.04/0.68  fof(f1675,plain,(
% 2.04/0.68    spl2_11 | ~spl2_16 | ~spl2_17),
% 2.04/0.68    inference(avatar_contradiction_clause,[],[f1674])).
% 2.04/0.68  fof(f1674,plain,(
% 2.04/0.68    $false | (spl2_11 | ~spl2_16 | ~spl2_17)),
% 2.04/0.68    inference(subsumption_resolution,[],[f186,f237])).
% 2.04/0.68  fof(f237,plain,(
% 2.04/0.68    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_16 | ~spl2_17)),
% 2.04/0.68    inference(forward_demodulation,[],[f236,f229])).
% 2.04/0.68  fof(f229,plain,(
% 2.04/0.68    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_16),
% 2.04/0.68    inference(superposition,[],[f211,f58])).
% 2.04/0.68  fof(f58,plain,(
% 2.04/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f1])).
% 2.04/0.68  fof(f1,axiom,(
% 2.04/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.04/0.68  fof(f211,plain,(
% 2.04/0.68    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_16),
% 2.04/0.68    inference(avatar_component_clause,[],[f210])).
% 2.04/0.68  fof(f210,plain,(
% 2.04/0.68    spl2_16 <=> k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 2.04/0.68  fof(f236,plain,(
% 2.04/0.68    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_17),
% 2.04/0.68    inference(superposition,[],[f55,f219])).
% 2.04/0.68  fof(f219,plain,(
% 2.04/0.68    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_17),
% 2.04/0.68    inference(avatar_component_clause,[],[f218])).
% 2.04/0.68  fof(f218,plain,(
% 2.04/0.68    spl2_17 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 2.04/0.68  fof(f55,plain,(
% 2.04/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.04/0.68    inference(cnf_transformation,[],[f9])).
% 2.04/0.68  fof(f9,axiom,(
% 2.04/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.04/0.68  fof(f186,plain,(
% 2.04/0.68    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | spl2_11),
% 2.04/0.68    inference(avatar_component_clause,[],[f138])).
% 2.04/0.68  fof(f138,plain,(
% 2.04/0.68    spl2_11 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 2.04/0.68  fof(f1669,plain,(
% 2.04/0.68    ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_16 | ~spl2_17 | ~spl2_60 | ~spl2_72 | ~spl2_102),
% 2.04/0.68    inference(avatar_contradiction_clause,[],[f1668])).
% 2.04/0.68  fof(f1668,plain,(
% 2.04/0.68    $false | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_16 | ~spl2_17 | ~spl2_60 | ~spl2_72 | ~spl2_102)),
% 2.04/0.68    inference(subsumption_resolution,[],[f1647,f1667])).
% 2.04/0.68  fof(f1667,plain,(
% 2.04/0.68    ~r1_tarski(k2_pre_topc(sK0,sK1),sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_16 | ~spl2_17 | ~spl2_60)),
% 2.04/0.68    inference(subsumption_resolution,[],[f719,f1666])).
% 2.04/0.68  fof(f1666,plain,(
% 2.04/0.68    sK1 != k2_pre_topc(sK0,sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_16 | ~spl2_17)),
% 2.04/0.68    inference(subsumption_resolution,[],[f84,f1665])).
% 2.04/0.68  fof(f1665,plain,(
% 2.04/0.68    ~v4_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_16 | ~spl2_17)),
% 2.04/0.68    inference(subsumption_resolution,[],[f197,f237])).
% 2.04/0.68  fof(f197,plain,(
% 2.04/0.68    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~spl2_3),
% 2.04/0.68    inference(forward_demodulation,[],[f37,f81])).
% 2.04/0.68  fof(f81,plain,(
% 2.04/0.68    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1)) ) | ~spl2_3),
% 2.04/0.68    inference(resolution,[],[f72,f44])).
% 2.04/0.68  fof(f44,plain,(
% 2.04/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f21])).
% 2.04/0.68  fof(f21,plain,(
% 2.04/0.68    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.04/0.68    inference(ennf_transformation,[],[f11])).
% 2.04/0.68  fof(f11,axiom,(
% 2.04/0.68    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.04/0.68  fof(f72,plain,(
% 2.04/0.68    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 2.04/0.68    inference(avatar_component_clause,[],[f71])).
% 2.04/0.68  fof(f71,plain,(
% 2.04/0.68    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.04/0.68  fof(f37,plain,(
% 2.04/0.68    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.04/0.68    inference(cnf_transformation,[],[f20])).
% 2.04/0.68  fof(f20,plain,(
% 2.04/0.68    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.04/0.68    inference(flattening,[],[f19])).
% 2.04/0.68  fof(f19,plain,(
% 2.04/0.68    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.04/0.68    inference(ennf_transformation,[],[f18])).
% 2.04/0.68  fof(f18,negated_conjecture,(
% 2.04/0.68    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.04/0.68    inference(negated_conjecture,[],[f17])).
% 2.04/0.68  fof(f17,conjecture,(
% 2.04/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 2.04/0.68  fof(f84,plain,(
% 2.04/0.68    sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 2.04/0.68    inference(subsumption_resolution,[],[f83,f64])).
% 2.04/0.68  fof(f64,plain,(
% 2.04/0.68    v2_pre_topc(sK0) | ~spl2_1),
% 2.04/0.68    inference(avatar_component_clause,[],[f63])).
% 2.04/0.68  fof(f63,plain,(
% 2.04/0.68    spl2_1 <=> v2_pre_topc(sK0)),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.04/0.68  fof(f83,plain,(
% 2.04/0.68    ~v2_pre_topc(sK0) | sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0) | (~spl2_2 | ~spl2_3)),
% 2.04/0.68    inference(subsumption_resolution,[],[f75,f68])).
% 2.04/0.68  fof(f68,plain,(
% 2.04/0.68    l1_pre_topc(sK0) | ~spl2_2),
% 2.04/0.68    inference(avatar_component_clause,[],[f67])).
% 2.04/0.68  fof(f67,plain,(
% 2.04/0.68    spl2_2 <=> l1_pre_topc(sK0)),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.04/0.68  fof(f75,plain,(
% 2.04/0.68    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0) | ~spl2_3),
% 2.04/0.68    inference(resolution,[],[f72,f48])).
% 2.04/0.68  fof(f48,plain,(
% 2.04/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f28])).
% 2.04/0.68  fof(f28,plain,(
% 2.04/0.68    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.04/0.68    inference(flattening,[],[f27])).
% 2.04/0.68  fof(f27,plain,(
% 2.04/0.68    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.04/0.68    inference(ennf_transformation,[],[f12])).
% 2.04/0.68  fof(f12,axiom,(
% 2.04/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.04/0.68  fof(f719,plain,(
% 2.04/0.68    ~r1_tarski(k2_pre_topc(sK0,sK1),sK1) | sK1 = k2_pre_topc(sK0,sK1) | ~spl2_60),
% 2.04/0.68    inference(resolution,[],[f703,f43])).
% 2.04/0.68  fof(f43,plain,(
% 2.04/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.04/0.68    inference(cnf_transformation,[],[f2])).
% 2.04/0.68  fof(f2,axiom,(
% 2.04/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.04/0.68  fof(f703,plain,(
% 2.04/0.68    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_60),
% 2.04/0.68    inference(avatar_component_clause,[],[f702])).
% 2.04/0.68  fof(f702,plain,(
% 2.04/0.68    spl2_60 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).
% 2.04/0.68  fof(f1647,plain,(
% 2.04/0.68    r1_tarski(k2_pre_topc(sK0,sK1),sK1) | (~spl2_72 | ~spl2_102)),
% 2.04/0.68    inference(forward_demodulation,[],[f1639,f895])).
% 2.04/0.68  fof(f895,plain,(
% 2.04/0.68    sK1 = k2_xboole_0(sK1,sK1) | ~spl2_72),
% 2.04/0.68    inference(avatar_component_clause,[],[f894])).
% 2.04/0.68  fof(f894,plain,(
% 2.04/0.68    spl2_72 <=> sK1 = k2_xboole_0(sK1,sK1)),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).
% 2.04/0.68  fof(f1639,plain,(
% 2.04/0.68    r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,sK1)) | ~spl2_102),
% 2.04/0.68    inference(resolution,[],[f1629,f50])).
% 2.04/0.68  fof(f50,plain,(
% 2.04/0.68    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.04/0.68    inference(cnf_transformation,[],[f29])).
% 2.04/0.68  fof(f29,plain,(
% 2.04/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.04/0.68    inference(ennf_transformation,[],[f8])).
% 2.04/0.68  fof(f8,axiom,(
% 2.04/0.68    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.04/0.68  fof(f1629,plain,(
% 2.04/0.68    r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1) | ~spl2_102),
% 2.04/0.68    inference(avatar_component_clause,[],[f1628])).
% 2.04/0.68  fof(f1628,plain,(
% 2.04/0.68    spl2_102 <=> r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1)),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_102])])).
% 2.04/0.68  fof(f1630,plain,(
% 2.04/0.68    spl2_102 | ~spl2_11 | ~spl2_72 | ~spl2_96),
% 2.04/0.68    inference(avatar_split_clause,[],[f1626,f1458,f894,f138,f1628])).
% 2.04/0.68  fof(f1458,plain,(
% 2.04/0.68    spl2_96 <=> k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).
% 2.04/0.68  fof(f1626,plain,(
% 2.04/0.68    r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1) | (~spl2_11 | ~spl2_72 | ~spl2_96)),
% 2.04/0.68    inference(forward_demodulation,[],[f1625,f895])).
% 2.04/0.68  fof(f1625,plain,(
% 2.04/0.68    r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,sK1)),sK1) | (~spl2_11 | ~spl2_72 | ~spl2_96)),
% 2.04/0.68    inference(forward_demodulation,[],[f1620,f54])).
% 2.04/0.68  fof(f54,plain,(
% 2.04/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.04/0.68    inference(cnf_transformation,[],[f6])).
% 2.04/0.68  fof(f6,axiom,(
% 2.04/0.68    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.04/0.68  fof(f1620,plain,(
% 2.04/0.68    r1_tarski(k4_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1),sK1) | (~spl2_11 | ~spl2_72 | ~spl2_96)),
% 2.04/0.68    inference(superposition,[],[f921,f1459])).
% 2.04/0.68  fof(f1459,plain,(
% 2.04/0.68    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | ~spl2_96),
% 2.04/0.68    inference(avatar_component_clause,[],[f1458])).
% 2.04/0.68  fof(f921,plain,(
% 2.04/0.68    ( ! [X5] : (r1_tarski(k4_xboole_0(k3_xboole_0(X5,k2_tops_1(sK0,sK1)),sK1),sK1)) ) | (~spl2_11 | ~spl2_72)),
% 2.04/0.68    inference(resolution,[],[f908,f418])).
% 2.04/0.68  fof(f418,plain,(
% 2.04/0.68    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k2_tops_1(sK0,sK1)),sK1)) ) | ~spl2_11),
% 2.04/0.68    inference(superposition,[],[f383,f58])).
% 2.04/0.68  fof(f383,plain,(
% 2.04/0.68    ( ! [X0] : (r1_tarski(k3_xboole_0(k2_tops_1(sK0,sK1),X0),sK1)) ) | ~spl2_11),
% 2.04/0.68    inference(superposition,[],[f374,f55])).
% 2.04/0.68  fof(f374,plain,(
% 2.04/0.68    ( ! [X2] : (r1_tarski(k4_xboole_0(k2_tops_1(sK0,sK1),X2),sK1)) ) | ~spl2_11),
% 2.04/0.68    inference(superposition,[],[f53,f204])).
% 2.04/0.68  fof(f204,plain,(
% 2.04/0.68    ( ! [X0] : (k4_xboole_0(k2_tops_1(sK0,sK1),X0) = k4_xboole_0(sK1,k2_xboole_0(k1_tops_1(sK0,sK1),X0))) ) | ~spl2_11),
% 2.04/0.68    inference(superposition,[],[f54,f139])).
% 2.04/0.68  fof(f139,plain,(
% 2.04/0.68    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_11),
% 2.04/0.68    inference(avatar_component_clause,[],[f138])).
% 2.04/0.68  fof(f53,plain,(
% 2.04/0.68    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f5])).
% 2.04/0.68  fof(f5,axiom,(
% 2.04/0.68    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.04/0.68  fof(f908,plain,(
% 2.04/0.68    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(k4_xboole_0(X0,sK1),sK1)) ) | ~spl2_72),
% 2.04/0.68    inference(superposition,[],[f51,f895])).
% 2.04/0.68  fof(f51,plain,(
% 2.04/0.68    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f30])).
% 2.04/0.68  fof(f30,plain,(
% 2.04/0.68    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.04/0.68    inference(ennf_transformation,[],[f7])).
% 2.04/0.68  fof(f7,axiom,(
% 2.04/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.04/0.68  fof(f1460,plain,(
% 2.04/0.68    spl2_96 | ~spl2_47),
% 2.04/0.68    inference(avatar_split_clause,[],[f532,f513,f1458])).
% 2.04/0.68  fof(f513,plain,(
% 2.04/0.68    spl2_47 <=> r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 2.04/0.68  fof(f532,plain,(
% 2.04/0.68    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | ~spl2_47),
% 2.04/0.68    inference(resolution,[],[f514,f57])).
% 2.04/0.68  fof(f57,plain,(
% 2.04/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.04/0.68    inference(cnf_transformation,[],[f33])).
% 2.04/0.68  fof(f33,plain,(
% 2.04/0.68    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.04/0.68    inference(ennf_transformation,[],[f4])).
% 2.04/0.68  fof(f4,axiom,(
% 2.04/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.04/0.68  fof(f514,plain,(
% 2.04/0.68    r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | ~spl2_47),
% 2.04/0.68    inference(avatar_component_clause,[],[f513])).
% 2.04/0.68  fof(f896,plain,(
% 2.04/0.68    spl2_72 | ~spl2_11 | ~spl2_17),
% 2.04/0.68    inference(avatar_split_clause,[],[f884,f218,f138,f894])).
% 2.04/0.68  fof(f884,plain,(
% 2.04/0.68    sK1 = k2_xboole_0(sK1,sK1) | (~spl2_11 | ~spl2_17)),
% 2.04/0.68    inference(superposition,[],[f437,f415])).
% 2.04/0.68  fof(f415,plain,(
% 2.04/0.68    ( ! [X2] : (sK1 = k2_xboole_0(k3_xboole_0(k2_tops_1(sK0,sK1),X2),sK1)) ) | ~spl2_11),
% 2.04/0.68    inference(resolution,[],[f383,f52])).
% 2.04/0.68  fof(f52,plain,(
% 2.04/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.04/0.68    inference(cnf_transformation,[],[f31])).
% 2.04/0.68  fof(f31,plain,(
% 2.04/0.68    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.04/0.68    inference(ennf_transformation,[],[f3])).
% 2.04/0.68  fof(f3,axiom,(
% 2.04/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.04/0.68  fof(f437,plain,(
% 2.04/0.68    ( ! [X2] : (k2_xboole_0(X2,sK1) = k2_xboole_0(sK1,k2_xboole_0(X2,sK1))) ) | (~spl2_11 | ~spl2_17)),
% 2.04/0.68    inference(resolution,[],[f432,f52])).
% 2.04/0.68  fof(f432,plain,(
% 2.04/0.68    ( ! [X0] : (r1_tarski(sK1,k2_xboole_0(X0,sK1))) ) | (~spl2_11 | ~spl2_17)),
% 2.04/0.68    inference(forward_demodulation,[],[f425,f405])).
% 2.04/0.68  fof(f405,plain,(
% 2.04/0.68    ( ! [X3] : (k2_xboole_0(X3,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k2_xboole_0(X3,sK1))) ) | ~spl2_11),
% 2.04/0.68    inference(resolution,[],[f378,f52])).
% 2.04/0.68  fof(f378,plain,(
% 2.04/0.68    ( ! [X0] : (r1_tarski(k2_tops_1(sK0,sK1),k2_xboole_0(X0,sK1))) ) | ~spl2_11),
% 2.04/0.68    inference(resolution,[],[f374,f50])).
% 2.04/0.68  fof(f425,plain,(
% 2.04/0.68    ( ! [X0] : (r1_tarski(sK1,k2_xboole_0(k2_tops_1(sK0,sK1),k2_xboole_0(X0,sK1)))) ) | ~spl2_17),
% 2.04/0.68    inference(resolution,[],[f391,f235])).
% 2.04/0.68  fof(f235,plain,(
% 2.04/0.68    ( ! [X1] : (~r1_tarski(k1_tops_1(sK0,sK1),X1) | r1_tarski(sK1,k2_xboole_0(k2_tops_1(sK0,sK1),X1))) ) | ~spl2_17),
% 2.04/0.68    inference(superposition,[],[f50,f219])).
% 2.04/0.68  fof(f391,plain,(
% 2.04/0.68    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(X0,sK1))) ) | ~spl2_17),
% 2.04/0.68    inference(resolution,[],[f387,f50])).
% 2.04/0.68  fof(f387,plain,(
% 2.04/0.68    ( ! [X2] : (r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),X2),sK1)) ) | ~spl2_17),
% 2.04/0.68    inference(superposition,[],[f53,f233])).
% 2.04/0.68  fof(f233,plain,(
% 2.04/0.68    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(k2_tops_1(sK0,sK1),X0)) = k4_xboole_0(k1_tops_1(sK0,sK1),X0)) ) | ~spl2_17),
% 2.04/0.68    inference(superposition,[],[f54,f219])).
% 2.04/0.68  fof(f704,plain,(
% 2.04/0.68    spl2_60 | ~spl2_19 | ~spl2_57),
% 2.04/0.68    inference(avatar_split_clause,[],[f696,f685,f226,f702])).
% 2.04/0.68  fof(f226,plain,(
% 2.04/0.68    spl2_19 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 2.04/0.68  fof(f685,plain,(
% 2.04/0.68    spl2_57 <=> r1_tarski(k4_xboole_0(sK1,sK1),k2_tops_1(sK0,sK1))),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 2.04/0.68  fof(f696,plain,(
% 2.04/0.68    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_19 | ~spl2_57)),
% 2.04/0.68    inference(forward_demodulation,[],[f692,f227])).
% 2.04/0.68  fof(f227,plain,(
% 2.04/0.68    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_19),
% 2.04/0.68    inference(avatar_component_clause,[],[f226])).
% 2.04/0.68  fof(f692,plain,(
% 2.04/0.68    r1_tarski(sK1,k2_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl2_57),
% 2.04/0.68    inference(resolution,[],[f686,f50])).
% 2.04/0.68  fof(f686,plain,(
% 2.04/0.68    r1_tarski(k4_xboole_0(sK1,sK1),k2_tops_1(sK0,sK1)) | ~spl2_57),
% 2.04/0.68    inference(avatar_component_clause,[],[f685])).
% 2.04/0.68  fof(f687,plain,(
% 2.04/0.68    spl2_57 | ~spl2_55),
% 2.04/0.68    inference(avatar_split_clause,[],[f667,f599,f685])).
% 2.04/0.68  fof(f599,plain,(
% 2.04/0.68    spl2_55 <=> k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_xboole_0(sK1,sK1)),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 2.04/0.68  fof(f667,plain,(
% 2.04/0.68    r1_tarski(k4_xboole_0(sK1,sK1),k2_tops_1(sK0,sK1)) | ~spl2_55),
% 2.04/0.68    inference(superposition,[],[f53,f600])).
% 2.04/0.68  fof(f600,plain,(
% 2.04/0.68    k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_xboole_0(sK1,sK1) | ~spl2_55),
% 2.04/0.68    inference(avatar_component_clause,[],[f599])).
% 2.04/0.68  fof(f601,plain,(
% 2.04/0.68    spl2_55 | ~spl2_11 | ~spl2_23),
% 2.04/0.68    inference(avatar_split_clause,[],[f372,f254,f138,f599])).
% 2.04/0.68  fof(f254,plain,(
% 2.04/0.68    spl2_23 <=> sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 2.04/0.68  fof(f372,plain,(
% 2.04/0.68    k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_xboole_0(sK1,sK1) | (~spl2_11 | ~spl2_23)),
% 2.04/0.68    inference(superposition,[],[f204,f255])).
% 2.04/0.68  fof(f255,plain,(
% 2.04/0.68    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) | ~spl2_23),
% 2.04/0.68    inference(avatar_component_clause,[],[f254])).
% 2.04/0.68  fof(f515,plain,(
% 2.04/0.68    spl2_47 | ~spl2_19),
% 2.04/0.68    inference(avatar_split_clause,[],[f364,f226,f513])).
% 2.04/0.68  fof(f364,plain,(
% 2.04/0.68    r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | ~spl2_19),
% 2.04/0.68    inference(resolution,[],[f242,f61])).
% 2.04/0.68  fof(f61,plain,(
% 2.04/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.04/0.68    inference(equality_resolution,[],[f41])).
% 2.04/0.68  fof(f41,plain,(
% 2.04/0.68    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.04/0.68    inference(cnf_transformation,[],[f2])).
% 2.04/0.68  fof(f242,plain,(
% 2.04/0.68    ( ! [X0] : (~r1_tarski(X0,k2_pre_topc(sK0,sK1)) | r1_tarski(k4_xboole_0(X0,sK1),k2_tops_1(sK0,sK1))) ) | ~spl2_19),
% 2.04/0.68    inference(superposition,[],[f51,f227])).
% 2.04/0.68  fof(f256,plain,(
% 2.04/0.68    spl2_23 | ~spl2_20),
% 2.04/0.68    inference(avatar_split_clause,[],[f244,f239,f254])).
% 2.04/0.68  fof(f239,plain,(
% 2.04/0.68    spl2_20 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 2.04/0.68  fof(f244,plain,(
% 2.04/0.68    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) | ~spl2_20),
% 2.04/0.68    inference(resolution,[],[f240,f52])).
% 2.04/0.68  fof(f240,plain,(
% 2.04/0.68    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_20),
% 2.04/0.68    inference(avatar_component_clause,[],[f239])).
% 2.04/0.68  fof(f241,plain,(
% 2.04/0.68    spl2_20 | ~spl2_17),
% 2.04/0.68    inference(avatar_split_clause,[],[f234,f218,f239])).
% 2.04/0.68  fof(f234,plain,(
% 2.04/0.68    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_17),
% 2.04/0.68    inference(superposition,[],[f53,f219])).
% 2.04/0.68  fof(f228,plain,(
% 2.04/0.68    spl2_19 | ~spl2_3 | ~spl2_4 | ~spl2_8),
% 2.04/0.68    inference(avatar_split_clause,[],[f191,f126,f90,f71,f226])).
% 2.04/0.68  fof(f90,plain,(
% 2.04/0.68    spl2_4 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.04/0.68  fof(f126,plain,(
% 2.04/0.68    spl2_8 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 2.04/0.68  fof(f191,plain,(
% 2.04/0.68    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_8)),
% 2.04/0.68    inference(forward_demodulation,[],[f189,f127])).
% 2.04/0.68  fof(f127,plain,(
% 2.04/0.68    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_8),
% 2.04/0.68    inference(avatar_component_clause,[],[f126])).
% 2.04/0.68  fof(f189,plain,(
% 2.04/0.68    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 2.04/0.68    inference(resolution,[],[f80,f91])).
% 2.04/0.68  fof(f91,plain,(
% 2.04/0.68    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_4),
% 2.04/0.68    inference(avatar_component_clause,[],[f90])).
% 2.04/0.68  fof(f80,plain,(
% 2.04/0.68    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(sK1,X0) = k4_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_3),
% 2.04/0.68    inference(resolution,[],[f72,f59])).
% 2.04/0.68  fof(f59,plain,(
% 2.04/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f35])).
% 2.04/0.68  fof(f35,plain,(
% 2.04/0.68    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.04/0.68    inference(flattening,[],[f34])).
% 2.04/0.68  fof(f34,plain,(
% 2.04/0.68    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.04/0.68    inference(ennf_transformation,[],[f10])).
% 2.04/0.68  fof(f10,axiom,(
% 2.04/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.04/0.68  fof(f220,plain,(
% 2.04/0.68    spl2_17 | ~spl2_3 | ~spl2_10),
% 2.04/0.68    inference(avatar_split_clause,[],[f184,f134,f71,f218])).
% 2.04/0.68  fof(f134,plain,(
% 2.04/0.68    spl2_10 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 2.04/0.68  fof(f184,plain,(
% 2.04/0.68    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_10)),
% 2.04/0.68    inference(superposition,[],[f135,f81])).
% 2.04/0.68  fof(f135,plain,(
% 2.04/0.68    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_10),
% 2.04/0.68    inference(avatar_component_clause,[],[f134])).
% 2.04/0.68  fof(f213,plain,(
% 2.04/0.68    spl2_13 | ~spl2_11),
% 2.04/0.68    inference(avatar_split_clause,[],[f205,f138,f152])).
% 2.04/0.68  fof(f152,plain,(
% 2.04/0.68    spl2_13 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 2.04/0.68  fof(f205,plain,(
% 2.04/0.68    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_11),
% 2.04/0.68    inference(superposition,[],[f53,f139])).
% 2.04/0.68  fof(f212,plain,(
% 2.04/0.68    spl2_16 | ~spl2_13),
% 2.04/0.68    inference(avatar_split_clause,[],[f159,f152,f210])).
% 2.04/0.68  fof(f159,plain,(
% 2.04/0.68    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_13),
% 2.04/0.68    inference(resolution,[],[f153,f57])).
% 2.04/0.68  fof(f153,plain,(
% 2.04/0.68    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_13),
% 2.04/0.68    inference(avatar_component_clause,[],[f152])).
% 2.04/0.68  fof(f154,plain,(
% 2.04/0.68    spl2_13 | ~spl2_2 | ~spl2_3 | ~spl2_5),
% 2.04/0.68    inference(avatar_split_clause,[],[f149,f94,f71,f67,f152])).
% 2.04/0.68  fof(f94,plain,(
% 2.04/0.68    spl2_5 <=> v4_pre_topc(sK1,sK0)),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.04/0.68  fof(f149,plain,(
% 2.04/0.68    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_3 | ~spl2_5)),
% 2.04/0.68    inference(subsumption_resolution,[],[f86,f95])).
% 2.04/0.68  fof(f95,plain,(
% 2.04/0.68    v4_pre_topc(sK1,sK0) | ~spl2_5),
% 2.04/0.68    inference(avatar_component_clause,[],[f94])).
% 2.04/0.68  fof(f86,plain,(
% 2.04/0.68    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_3)),
% 2.04/0.68    inference(subsumption_resolution,[],[f77,f68])).
% 2.04/0.68  fof(f77,plain,(
% 2.04/0.68    ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_3),
% 2.04/0.68    inference(resolution,[],[f72,f47])).
% 2.04/0.68  fof(f47,plain,(
% 2.04/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f26])).
% 2.04/0.68  fof(f26,plain,(
% 2.04/0.68    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.04/0.68    inference(flattening,[],[f25])).
% 2.04/0.68  fof(f25,plain,(
% 2.04/0.68    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.04/0.68    inference(ennf_transformation,[],[f15])).
% 2.04/0.68  fof(f15,axiom,(
% 2.04/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 2.04/0.68  fof(f140,plain,(
% 2.04/0.68    spl2_11 | ~spl2_3 | ~spl2_6),
% 2.04/0.68    inference(avatar_split_clause,[],[f123,f97,f71,f138])).
% 2.04/0.68  fof(f97,plain,(
% 2.04/0.68    spl2_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 2.04/0.68  fof(f123,plain,(
% 2.04/0.68    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6)),
% 2.04/0.68    inference(superposition,[],[f81,f98])).
% 2.04/0.68  fof(f98,plain,(
% 2.04/0.68    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 2.04/0.68    inference(avatar_component_clause,[],[f97])).
% 2.04/0.68  fof(f136,plain,(
% 2.04/0.68    spl2_10 | ~spl2_2 | ~spl2_3),
% 2.04/0.68    inference(avatar_split_clause,[],[f88,f71,f67,f134])).
% 2.04/0.68  fof(f88,plain,(
% 2.04/0.68    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 2.04/0.68    inference(subsumption_resolution,[],[f79,f68])).
% 2.04/0.68  fof(f79,plain,(
% 2.04/0.68    ~l1_pre_topc(sK0) | k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_3),
% 2.04/0.68    inference(resolution,[],[f72,f45])).
% 2.04/0.68  fof(f45,plain,(
% 2.04/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.04/0.68    inference(cnf_transformation,[],[f22])).
% 2.04/0.68  fof(f22,plain,(
% 2.04/0.68    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.04/0.68    inference(ennf_transformation,[],[f16])).
% 2.04/0.68  fof(f16,axiom,(
% 2.04/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 2.04/0.68  fof(f128,plain,(
% 2.04/0.68    spl2_8 | ~spl2_2 | ~spl2_3),
% 2.04/0.68    inference(avatar_split_clause,[],[f82,f71,f67,f126])).
% 2.04/0.68  fof(f82,plain,(
% 2.04/0.68    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 2.04/0.68    inference(subsumption_resolution,[],[f74,f68])).
% 2.04/0.68  fof(f74,plain,(
% 2.04/0.68    ~l1_pre_topc(sK0) | k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_3),
% 2.04/0.68    inference(resolution,[],[f72,f56])).
% 2.04/0.68  fof(f56,plain,(
% 2.04/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.04/0.68    inference(cnf_transformation,[],[f32])).
% 2.04/0.68  fof(f32,plain,(
% 2.04/0.68    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.04/0.68    inference(ennf_transformation,[],[f14])).
% 2.04/0.68  fof(f14,axiom,(
% 2.04/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 2.04/0.68  fof(f99,plain,(
% 2.04/0.68    spl2_5 | spl2_6),
% 2.04/0.68    inference(avatar_split_clause,[],[f36,f97,f94])).
% 2.04/0.68  fof(f36,plain,(
% 2.04/0.68    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.04/0.68    inference(cnf_transformation,[],[f20])).
% 2.04/0.68  fof(f92,plain,(
% 2.04/0.68    spl2_4 | ~spl2_2 | ~spl2_3),
% 2.04/0.68    inference(avatar_split_clause,[],[f87,f71,f67,f90])).
% 2.04/0.68  fof(f87,plain,(
% 2.04/0.68    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 2.04/0.68    inference(subsumption_resolution,[],[f78,f68])).
% 2.04/0.68  fof(f78,plain,(
% 2.04/0.68    ~l1_pre_topc(sK0) | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 2.04/0.68    inference(resolution,[],[f72,f46])).
% 2.04/0.68  fof(f46,plain,(
% 2.04/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.04/0.68    inference(cnf_transformation,[],[f24])).
% 2.04/0.68  fof(f24,plain,(
% 2.04/0.68    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.04/0.68    inference(flattening,[],[f23])).
% 2.04/0.68  fof(f23,plain,(
% 2.04/0.68    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.04/0.68    inference(ennf_transformation,[],[f13])).
% 2.04/0.68  fof(f13,axiom,(
% 2.04/0.68    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.04/0.68  fof(f73,plain,(
% 2.04/0.68    spl2_3),
% 2.04/0.68    inference(avatar_split_clause,[],[f38,f71])).
% 2.04/0.68  fof(f38,plain,(
% 2.04/0.68    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.04/0.68    inference(cnf_transformation,[],[f20])).
% 2.04/0.68  fof(f69,plain,(
% 2.04/0.68    spl2_2),
% 2.04/0.68    inference(avatar_split_clause,[],[f40,f67])).
% 2.04/0.68  fof(f40,plain,(
% 2.04/0.68    l1_pre_topc(sK0)),
% 2.04/0.68    inference(cnf_transformation,[],[f20])).
% 2.04/0.68  fof(f65,plain,(
% 2.04/0.68    spl2_1),
% 2.04/0.68    inference(avatar_split_clause,[],[f39,f63])).
% 2.04/0.68  fof(f39,plain,(
% 2.04/0.68    v2_pre_topc(sK0)),
% 2.04/0.68    inference(cnf_transformation,[],[f20])).
% 2.04/0.68  % SZS output end Proof for theBenchmark
% 2.04/0.68  % (2852)------------------------------
% 2.04/0.68  % (2852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.68  % (2852)Termination reason: Refutation
% 2.04/0.68  
% 2.04/0.68  % (2852)Memory used [KB]: 7675
% 2.04/0.68  % (2852)Time elapsed: 0.270 s
% 2.04/0.68  % (2852)------------------------------
% 2.04/0.68  % (2852)------------------------------
% 2.04/0.68  % (2824)Success in time 0.323 s
%------------------------------------------------------------------------------
