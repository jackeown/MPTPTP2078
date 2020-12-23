%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:50 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 262 expanded)
%              Number of leaves         :   31 ( 103 expanded)
%              Depth                    :   11
%              Number of atoms          :  400 ( 688 expanded)
%              Number of equality atoms :   78 ( 137 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1002,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f112,f125,f151,f175,f188,f244,f337,f453,f549,f593,f621,f827,f882,f899,f906,f1001])).

fof(f1001,plain,
    ( spl3_11
    | ~ spl3_26
    | ~ spl3_32 ),
    inference(avatar_contradiction_clause,[],[f1000])).

fof(f1000,plain,
    ( $false
    | spl3_11
    | ~ spl3_26
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f998,f165])).

fof(f165,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl3_11
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f998,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_26
    | ~ spl3_32 ),
    inference(resolution,[],[f923,f66])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f923,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k4_xboole_0(X0,sK1),k2_tops_1(sK0,sK1))
        | r1_tarski(X0,sK1) )
    | ~ spl3_26
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f576,f336])).

fof(f336,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl3_26
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f576,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_pre_topc(sK0,sK1))
        | ~ r1_tarski(k4_xboole_0(X0,sK1),k2_tops_1(sK0,sK1)) )
    | ~ spl3_32 ),
    inference(superposition,[],[f86,f452])).

fof(f452,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f450])).

fof(f450,plain,
    ( spl3_32
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f906,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_12
    | ~ spl3_46 ),
    inference(avatar_contradiction_clause,[],[f905])).

fof(f905,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_12
    | ~ spl3_46 ),
    inference(subsumption_resolution,[],[f641,f904])).

fof(f904,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_3
    | spl3_5 ),
    inference(subsumption_resolution,[],[f900,f111])).

fof(f111,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f900,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5 ),
    inference(superposition,[],[f123,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f123,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl3_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f641,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f639,f284])).

fof(f284,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f179,f279])).

fof(f279,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f202,f111])).

fof(f202,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_xboole_0(X1,k2_tops_1(sK0,X1)) = k1_tops_1(sK0,X1) )
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,
    ( ! [X1] :
        ( k4_xboole_0(X1,k2_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_2 ),
    inference(superposition,[],[f106,f84])).

fof(f106,plain,
    ( ! [X3] :
        ( k1_tops_1(sK0,X3) = k7_subset_1(u1_struct_0(sK0),X3,k2_tops_1(sK0,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_2 ),
    inference(resolution,[],[f97,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f97,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f179,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f177,f178])).

fof(f178,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_12 ),
    inference(resolution,[],[f174,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f174,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl3_12
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f177,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_12 ),
    inference(resolution,[],[f174,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f639,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_46 ),
    inference(resolution,[],[f620,f74])).

fof(f620,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f618])).

fof(f618,plain,
    ( spl3_46
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f899,plain,
    ( ~ spl3_5
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f895,f334,f109,f95,f90,f122])).

fof(f90,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f895,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f54,f894])).

fof(f894,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f885,f111])).

fof(f885,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_26 ),
    inference(superposition,[],[f101,f336])).

fof(f101,plain,
    ( ! [X0] :
        ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f99,f97])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f92,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f92,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f54,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f882,plain,
    ( spl3_26
    | ~ spl3_32
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f874,f824,f450,f334])).

fof(f824,plain,
    ( spl3_62
  <=> k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f874,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_32
    | ~ spl3_62 ),
    inference(backward_demodulation,[],[f452,f869])).

fof(f869,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_62 ),
    inference(superposition,[],[f68,f826])).

fof(f826,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f824])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f827,plain,
    ( spl3_62
    | ~ spl3_9
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f587,f546,f148,f824])).

fof(f148,plain,
    ( spl3_9
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f546,plain,
    ( spl3_38
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f587,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_9
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f585,f150])).

fof(f150,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f148])).

fof(f585,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_38 ),
    inference(superposition,[],[f71,f548])).

fof(f548,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f546])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f621,plain,
    ( spl3_46
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f601,f590,f618])).

fof(f590,plain,
    ( spl3_42
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f601,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl3_42 ),
    inference(resolution,[],[f592,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f592,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f590])).

fof(f593,plain,
    ( spl3_42
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f586,f546,f590])).

fof(f586,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_38 ),
    inference(superposition,[],[f66,f548])).

fof(f549,plain,
    ( spl3_38
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f279,f109,f95,f546])).

fof(f453,plain,
    ( spl3_32
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f259,f241,f185,f109,f450])).

fof(f185,plain,
    ( spl3_13
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f241,plain,
    ( spl3_18
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f259,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f258,f111])).

fof(f258,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f256,f187])).

fof(f187,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f185])).

fof(f256,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_18 ),
    inference(superposition,[],[f243,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f243,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f241])).

fof(f337,plain,
    ( spl3_26
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f330,f118,f109,f95,f334])).

fof(f118,plain,
    ( spl3_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f330,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f329,f111])).

fof(f329,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f120,f104])).

fof(f104,plain,
    ( ! [X1] :
        ( ~ v4_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X1) = X1 )
    | ~ spl3_2 ),
    inference(resolution,[],[f97,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f120,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f244,plain,
    ( spl3_18
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f190,f109,f95,f241])).

fof(f190,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f105,f111])).

fof(f105,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X2) = k4_subset_1(u1_struct_0(sK0),X2,k2_tops_1(sK0,X2)) )
    | ~ spl3_2 ),
    inference(resolution,[],[f97,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f188,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f170,f109,f95,f185])).

fof(f170,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f103,f111])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_2 ),
    inference(resolution,[],[f97,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f175,plain,
    ( spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f168,f164,f172])).

fof(f168,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl3_11 ),
    inference(resolution,[],[f166,f82])).

fof(f166,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f164])).

fof(f151,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f130,f122,f109,f148])).

fof(f130,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f128,f111])).

fof(f128,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(superposition,[],[f124,f84])).

fof(f124,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f125,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f53,f122,f118])).

fof(f53,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f112,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f55,f109])).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f98,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f57,f95])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f93,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f56,f90])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:09:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.52  % (25236)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.53  % (25233)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.53  % (25241)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.53  % (25229)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.54  % (25251)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.54  % (25250)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.54  % (25231)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.54  % (25230)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.54  % (25243)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.54  % (25254)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.54  % (25246)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.54  % (25234)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.54  % (25253)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.54  % (25246)Refutation not found, incomplete strategy% (25246)------------------------------
% 0.23/0.54  % (25246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (25232)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.55  % (25244)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.55  % (25235)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.55  % (25251)Refutation not found, incomplete strategy% (25251)------------------------------
% 0.23/0.55  % (25251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (25251)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (25251)Memory used [KB]: 10746
% 0.23/0.55  % (25251)Time elapsed: 0.093 s
% 0.23/0.55  % (25251)------------------------------
% 0.23/0.55  % (25251)------------------------------
% 0.23/0.55  % (25248)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.55  % (25257)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.23/0.55  % (25238)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.55  % (25255)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.55  % (25245)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.55  % (25256)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.55  % (25239)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.55  % (25249)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.55  % (25252)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.56  % (25247)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.56  % (25240)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.31/0.56  % (25237)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.31/0.56  % (25246)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (25246)Memory used [KB]: 10618
% 1.31/0.56  % (25246)Time elapsed: 0.132 s
% 1.31/0.56  % (25246)------------------------------
% 1.31/0.56  % (25246)------------------------------
% 1.31/0.57  % (25242)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.31/0.57  % (25258)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.70/0.60  % (25249)Refutation found. Thanks to Tanya!
% 1.70/0.60  % SZS status Theorem for theBenchmark
% 1.70/0.62  % SZS output start Proof for theBenchmark
% 1.70/0.62  fof(f1002,plain,(
% 1.70/0.62    $false),
% 1.70/0.62    inference(avatar_sat_refutation,[],[f93,f98,f112,f125,f151,f175,f188,f244,f337,f453,f549,f593,f621,f827,f882,f899,f906,f1001])).
% 1.70/0.62  fof(f1001,plain,(
% 1.70/0.62    spl3_11 | ~spl3_26 | ~spl3_32),
% 1.70/0.62    inference(avatar_contradiction_clause,[],[f1000])).
% 1.70/0.62  fof(f1000,plain,(
% 1.70/0.62    $false | (spl3_11 | ~spl3_26 | ~spl3_32)),
% 1.70/0.62    inference(subsumption_resolution,[],[f998,f165])).
% 1.70/0.62  fof(f165,plain,(
% 1.70/0.62    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl3_11),
% 1.70/0.62    inference(avatar_component_clause,[],[f164])).
% 1.70/0.62  fof(f164,plain,(
% 1.70/0.62    spl3_11 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.70/0.62  fof(f998,plain,(
% 1.70/0.62    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl3_26 | ~spl3_32)),
% 1.70/0.62    inference(resolution,[],[f923,f66])).
% 1.70/0.62  fof(f66,plain,(
% 1.70/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.70/0.62    inference(cnf_transformation,[],[f6])).
% 1.70/0.62  fof(f6,axiom,(
% 1.70/0.62    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.70/0.62  fof(f923,plain,(
% 1.70/0.62    ( ! [X0] : (~r1_tarski(k4_xboole_0(X0,sK1),k2_tops_1(sK0,sK1)) | r1_tarski(X0,sK1)) ) | (~spl3_26 | ~spl3_32)),
% 1.70/0.62    inference(forward_demodulation,[],[f576,f336])).
% 1.70/0.62  fof(f336,plain,(
% 1.70/0.62    sK1 = k2_pre_topc(sK0,sK1) | ~spl3_26),
% 1.70/0.62    inference(avatar_component_clause,[],[f334])).
% 1.70/0.62  fof(f334,plain,(
% 1.70/0.62    spl3_26 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.70/0.62  fof(f576,plain,(
% 1.70/0.62    ( ! [X0] : (r1_tarski(X0,k2_pre_topc(sK0,sK1)) | ~r1_tarski(k4_xboole_0(X0,sK1),k2_tops_1(sK0,sK1))) ) | ~spl3_32),
% 1.70/0.62    inference(superposition,[],[f86,f452])).
% 1.70/0.62  fof(f452,plain,(
% 1.70/0.62    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_32),
% 1.70/0.62    inference(avatar_component_clause,[],[f450])).
% 1.70/0.62  fof(f450,plain,(
% 1.70/0.62    spl3_32 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.70/0.62  fof(f86,plain,(
% 1.70/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.70/0.62    inference(cnf_transformation,[],[f48])).
% 1.70/0.62  fof(f48,plain,(
% 1.70/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.70/0.62    inference(ennf_transformation,[],[f10])).
% 1.70/0.62  fof(f10,axiom,(
% 1.70/0.62    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.70/0.62  fof(f906,plain,(
% 1.70/0.62    ~spl3_2 | ~spl3_3 | spl3_5 | ~spl3_12 | ~spl3_46),
% 1.70/0.62    inference(avatar_contradiction_clause,[],[f905])).
% 1.70/0.62  fof(f905,plain,(
% 1.70/0.62    $false | (~spl3_2 | ~spl3_3 | spl3_5 | ~spl3_12 | ~spl3_46)),
% 1.70/0.62    inference(subsumption_resolution,[],[f641,f904])).
% 1.70/0.62  fof(f904,plain,(
% 1.70/0.62    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl3_3 | spl3_5)),
% 1.70/0.62    inference(subsumption_resolution,[],[f900,f111])).
% 1.70/0.62  fof(f111,plain,(
% 1.70/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 1.70/0.62    inference(avatar_component_clause,[],[f109])).
% 1.70/0.62  fof(f109,plain,(
% 1.70/0.62    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.70/0.62  fof(f900,plain,(
% 1.70/0.62    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_5),
% 1.70/0.62    inference(superposition,[],[f123,f84])).
% 1.70/0.62  fof(f84,plain,(
% 1.70/0.62    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.70/0.62    inference(cnf_transformation,[],[f46])).
% 1.70/0.62  fof(f46,plain,(
% 1.70/0.62    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.70/0.62    inference(ennf_transformation,[],[f19])).
% 1.70/0.62  fof(f19,axiom,(
% 1.70/0.62    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.70/0.62  fof(f123,plain,(
% 1.70/0.62    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl3_5),
% 1.70/0.62    inference(avatar_component_clause,[],[f122])).
% 1.70/0.62  fof(f122,plain,(
% 1.70/0.62    spl3_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.70/0.62  fof(f641,plain,(
% 1.70/0.62    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_12 | ~spl3_46)),
% 1.70/0.62    inference(forward_demodulation,[],[f639,f284])).
% 1.70/0.62  fof(f284,plain,(
% 1.70/0.62    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_12)),
% 1.70/0.62    inference(backward_demodulation,[],[f179,f279])).
% 1.70/0.62  fof(f279,plain,(
% 1.70/0.62    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_3)),
% 1.70/0.62    inference(resolution,[],[f202,f111])).
% 1.70/0.62  fof(f202,plain,(
% 1.70/0.62    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_xboole_0(X1,k2_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)) ) | ~spl3_2),
% 1.70/0.62    inference(duplicate_literal_removal,[],[f199])).
% 1.70/0.62  fof(f199,plain,(
% 1.70/0.62    ( ! [X1] : (k4_xboole_0(X1,k2_tops_1(sK0,X1)) = k1_tops_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_2),
% 1.70/0.62    inference(superposition,[],[f106,f84])).
% 1.70/0.62  fof(f106,plain,(
% 1.70/0.62    ( ! [X3] : (k1_tops_1(sK0,X3) = k7_subset_1(u1_struct_0(sK0),X3,k2_tops_1(sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_2),
% 1.70/0.62    inference(resolution,[],[f97,f61])).
% 1.70/0.62  fof(f61,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 1.70/0.62    inference(cnf_transformation,[],[f33])).
% 1.70/0.62  fof(f33,plain,(
% 1.70/0.62    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.62    inference(ennf_transformation,[],[f27])).
% 1.70/0.62  fof(f27,axiom,(
% 1.70/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 1.70/0.62  fof(f97,plain,(
% 1.70/0.62    l1_pre_topc(sK0) | ~spl3_2),
% 1.70/0.62    inference(avatar_component_clause,[],[f95])).
% 1.70/0.62  fof(f95,plain,(
% 1.70/0.62    spl3_2 <=> l1_pre_topc(sK0)),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.70/0.62  fof(f179,plain,(
% 1.70/0.62    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl3_12),
% 1.70/0.62    inference(backward_demodulation,[],[f177,f178])).
% 1.70/0.62  fof(f178,plain,(
% 1.70/0.62    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl3_12),
% 1.70/0.62    inference(resolution,[],[f174,f74])).
% 1.70/0.62  fof(f74,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.70/0.62    inference(cnf_transformation,[],[f38])).
% 1.70/0.62  fof(f38,plain,(
% 1.70/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.70/0.62    inference(ennf_transformation,[],[f15])).
% 1.70/0.62  fof(f15,axiom,(
% 1.70/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.70/0.62  fof(f174,plain,(
% 1.70/0.62    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl3_12),
% 1.70/0.62    inference(avatar_component_clause,[],[f172])).
% 1.70/0.62  fof(f172,plain,(
% 1.70/0.62    spl3_12 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.70/0.62  fof(f177,plain,(
% 1.70/0.62    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl3_12),
% 1.70/0.62    inference(resolution,[],[f174,f75])).
% 1.70/0.62  fof(f75,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.70/0.62    inference(cnf_transformation,[],[f39])).
% 1.70/0.62  fof(f39,plain,(
% 1.70/0.62    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.70/0.62    inference(ennf_transformation,[],[f17])).
% 1.70/0.62  fof(f17,axiom,(
% 1.70/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.70/0.62  fof(f639,plain,(
% 1.70/0.62    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl3_46),
% 1.70/0.62    inference(resolution,[],[f620,f74])).
% 1.70/0.62  fof(f620,plain,(
% 1.70/0.62    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl3_46),
% 1.70/0.62    inference(avatar_component_clause,[],[f618])).
% 1.70/0.62  fof(f618,plain,(
% 1.70/0.62    spl3_46 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 1.70/0.62  fof(f899,plain,(
% 1.70/0.62    ~spl3_5 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_26),
% 1.70/0.62    inference(avatar_split_clause,[],[f895,f334,f109,f95,f90,f122])).
% 1.70/0.62  fof(f90,plain,(
% 1.70/0.62    spl3_1 <=> v2_pre_topc(sK0)),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.70/0.62  fof(f895,plain,(
% 1.70/0.62    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_26)),
% 1.70/0.62    inference(subsumption_resolution,[],[f54,f894])).
% 1.70/0.62  fof(f894,plain,(
% 1.70/0.62    v4_pre_topc(sK1,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_26)),
% 1.70/0.62    inference(subsumption_resolution,[],[f885,f111])).
% 1.70/0.62  fof(f885,plain,(
% 1.70/0.62    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_2 | ~spl3_26)),
% 1.70/0.62    inference(superposition,[],[f101,f336])).
% 1.70/0.62  fof(f101,plain,(
% 1.70/0.62    ( ! [X0] : (v4_pre_topc(k2_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_1 | ~spl3_2)),
% 1.70/0.62    inference(subsumption_resolution,[],[f99,f97])).
% 1.70/0.62  fof(f99,plain,(
% 1.70/0.62    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k2_pre_topc(sK0,X0),sK0)) ) | ~spl3_1),
% 1.70/0.62    inference(resolution,[],[f92,f77])).
% 1.70/0.62  fof(f77,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0)) )),
% 1.70/0.62    inference(cnf_transformation,[],[f42])).
% 1.70/0.62  fof(f42,plain,(
% 1.70/0.62    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.70/0.62    inference(flattening,[],[f41])).
% 1.70/0.62  fof(f41,plain,(
% 1.70/0.62    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.70/0.62    inference(ennf_transformation,[],[f24])).
% 1.70/0.62  fof(f24,axiom,(
% 1.70/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 1.70/0.62  fof(f92,plain,(
% 1.70/0.62    v2_pre_topc(sK0) | ~spl3_1),
% 1.70/0.62    inference(avatar_component_clause,[],[f90])).
% 1.70/0.62  fof(f54,plain,(
% 1.70/0.62    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 1.70/0.62    inference(cnf_transformation,[],[f31])).
% 1.70/0.62  fof(f31,plain,(
% 1.70/0.62    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.70/0.62    inference(flattening,[],[f30])).
% 1.70/0.62  fof(f30,plain,(
% 1.70/0.62    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.70/0.62    inference(ennf_transformation,[],[f29])).
% 1.70/0.62  fof(f29,negated_conjecture,(
% 1.70/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.70/0.62    inference(negated_conjecture,[],[f28])).
% 1.70/0.62  fof(f28,conjecture,(
% 1.70/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 1.70/0.62  fof(f882,plain,(
% 1.70/0.62    spl3_26 | ~spl3_32 | ~spl3_62),
% 1.70/0.62    inference(avatar_split_clause,[],[f874,f824,f450,f334])).
% 1.70/0.62  fof(f824,plain,(
% 1.70/0.62    spl3_62 <=> k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 1.70/0.62  fof(f874,plain,(
% 1.70/0.62    sK1 = k2_pre_topc(sK0,sK1) | (~spl3_32 | ~spl3_62)),
% 1.70/0.62    inference(backward_demodulation,[],[f452,f869])).
% 1.70/0.62  fof(f869,plain,(
% 1.70/0.62    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_62),
% 1.70/0.62    inference(superposition,[],[f68,f826])).
% 1.70/0.62  fof(f826,plain,(
% 1.70/0.62    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_62),
% 1.70/0.62    inference(avatar_component_clause,[],[f824])).
% 1.70/0.62  fof(f68,plain,(
% 1.70/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.70/0.62    inference(cnf_transformation,[],[f4])).
% 1.70/0.62  fof(f4,axiom,(
% 1.70/0.62    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.70/0.62  fof(f827,plain,(
% 1.70/0.62    spl3_62 | ~spl3_9 | ~spl3_38),
% 1.70/0.62    inference(avatar_split_clause,[],[f587,f546,f148,f824])).
% 1.70/0.62  fof(f148,plain,(
% 1.70/0.62    spl3_9 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.70/0.62  fof(f546,plain,(
% 1.70/0.62    spl3_38 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 1.70/0.62  fof(f587,plain,(
% 1.70/0.62    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl3_9 | ~spl3_38)),
% 1.70/0.62    inference(forward_demodulation,[],[f585,f150])).
% 1.70/0.62  fof(f150,plain,(
% 1.70/0.62    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl3_9),
% 1.70/0.62    inference(avatar_component_clause,[],[f148])).
% 1.70/0.62  fof(f585,plain,(
% 1.70/0.62    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_38),
% 1.70/0.62    inference(superposition,[],[f71,f548])).
% 1.70/0.62  fof(f548,plain,(
% 1.70/0.62    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_38),
% 1.70/0.62    inference(avatar_component_clause,[],[f546])).
% 1.70/0.62  fof(f71,plain,(
% 1.70/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.70/0.62    inference(cnf_transformation,[],[f11])).
% 1.70/0.62  fof(f11,axiom,(
% 1.70/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.70/0.62  fof(f621,plain,(
% 1.70/0.62    spl3_46 | ~spl3_42),
% 1.70/0.62    inference(avatar_split_clause,[],[f601,f590,f618])).
% 1.70/0.62  fof(f590,plain,(
% 1.70/0.62    spl3_42 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 1.70/0.62  fof(f601,plain,(
% 1.70/0.62    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl3_42),
% 1.70/0.62    inference(resolution,[],[f592,f82])).
% 1.70/0.62  fof(f82,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.70/0.62    inference(cnf_transformation,[],[f21])).
% 1.70/0.62  fof(f21,axiom,(
% 1.70/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.70/0.62  fof(f592,plain,(
% 1.70/0.62    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_42),
% 1.70/0.62    inference(avatar_component_clause,[],[f590])).
% 1.70/0.62  fof(f593,plain,(
% 1.70/0.62    spl3_42 | ~spl3_38),
% 1.70/0.62    inference(avatar_split_clause,[],[f586,f546,f590])).
% 1.70/0.62  fof(f586,plain,(
% 1.70/0.62    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_38),
% 1.70/0.62    inference(superposition,[],[f66,f548])).
% 1.70/0.62  fof(f549,plain,(
% 1.70/0.62    spl3_38 | ~spl3_2 | ~spl3_3),
% 1.70/0.62    inference(avatar_split_clause,[],[f279,f109,f95,f546])).
% 1.70/0.62  fof(f453,plain,(
% 1.70/0.62    spl3_32 | ~spl3_3 | ~spl3_13 | ~spl3_18),
% 1.70/0.62    inference(avatar_split_clause,[],[f259,f241,f185,f109,f450])).
% 1.70/0.62  fof(f185,plain,(
% 1.70/0.62    spl3_13 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.70/0.62  fof(f241,plain,(
% 1.70/0.62    spl3_18 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.70/0.62  fof(f259,plain,(
% 1.70/0.62    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_13 | ~spl3_18)),
% 1.70/0.62    inference(subsumption_resolution,[],[f258,f111])).
% 1.70/0.62  fof(f258,plain,(
% 1.70/0.62    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_13 | ~spl3_18)),
% 1.70/0.62    inference(subsumption_resolution,[],[f256,f187])).
% 1.70/0.62  fof(f187,plain,(
% 1.70/0.62    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_13),
% 1.70/0.62    inference(avatar_component_clause,[],[f185])).
% 1.70/0.62  fof(f256,plain,(
% 1.70/0.62    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_18),
% 1.70/0.62    inference(superposition,[],[f243,f88])).
% 1.70/0.62  fof(f88,plain,(
% 1.70/0.62    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.70/0.62    inference(cnf_transformation,[],[f52])).
% 1.70/0.62  fof(f52,plain,(
% 1.70/0.62    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.70/0.62    inference(flattening,[],[f51])).
% 1.70/0.62  fof(f51,plain,(
% 1.70/0.62    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.70/0.62    inference(ennf_transformation,[],[f18])).
% 1.70/0.62  fof(f18,axiom,(
% 1.70/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.70/0.62  fof(f243,plain,(
% 1.70/0.62    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl3_18),
% 1.70/0.62    inference(avatar_component_clause,[],[f241])).
% 1.70/0.62  fof(f337,plain,(
% 1.70/0.62    spl3_26 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 1.70/0.62    inference(avatar_split_clause,[],[f330,f118,f109,f95,f334])).
% 1.70/0.62  fof(f118,plain,(
% 1.70/0.62    spl3_4 <=> v4_pre_topc(sK1,sK0)),
% 1.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.70/0.62  fof(f330,plain,(
% 1.70/0.62    sK1 = k2_pre_topc(sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 1.70/0.62    inference(subsumption_resolution,[],[f329,f111])).
% 1.70/0.62  fof(f329,plain,(
% 1.70/0.62    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | (~spl3_2 | ~spl3_4)),
% 1.70/0.62    inference(resolution,[],[f120,f104])).
% 1.70/0.62  fof(f104,plain,(
% 1.70/0.62    ( ! [X1] : (~v4_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X1) = X1) ) | ~spl3_2),
% 1.70/0.62    inference(resolution,[],[f97,f64])).
% 1.70/0.62  fof(f64,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.70/0.62    inference(cnf_transformation,[],[f36])).
% 1.70/0.62  fof(f36,plain,(
% 1.70/0.62    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.62    inference(flattening,[],[f35])).
% 1.70/0.62  fof(f35,plain,(
% 1.70/0.62    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.62    inference(ennf_transformation,[],[f22])).
% 1.70/0.62  fof(f22,axiom,(
% 1.70/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.70/0.62  fof(f120,plain,(
% 1.70/0.62    v4_pre_topc(sK1,sK0) | ~spl3_4),
% 1.70/0.62    inference(avatar_component_clause,[],[f118])).
% 1.70/0.62  fof(f244,plain,(
% 1.70/0.62    spl3_18 | ~spl3_2 | ~spl3_3),
% 1.70/0.62    inference(avatar_split_clause,[],[f190,f109,f95,f241])).
% 1.70/0.62  fof(f190,plain,(
% 1.70/0.62    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_3)),
% 1.70/0.62    inference(resolution,[],[f105,f111])).
% 1.70/0.62  fof(f105,plain,(
% 1.70/0.62    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X2) = k4_subset_1(u1_struct_0(sK0),X2,k2_tops_1(sK0,X2))) ) | ~spl3_2),
% 1.70/0.62    inference(resolution,[],[f97,f62])).
% 1.70/0.62  fof(f62,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 1.70/0.62    inference(cnf_transformation,[],[f34])).
% 1.70/0.62  fof(f34,plain,(
% 1.70/0.62    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.62    inference(ennf_transformation,[],[f26])).
% 1.70/0.62  fof(f26,axiom,(
% 1.70/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 1.70/0.62  fof(f188,plain,(
% 1.70/0.62    spl3_13 | ~spl3_2 | ~spl3_3),
% 1.70/0.62    inference(avatar_split_clause,[],[f170,f109,f95,f185])).
% 1.70/0.62  fof(f170,plain,(
% 1.70/0.62    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3)),
% 1.70/0.62    inference(resolution,[],[f103,f111])).
% 1.70/0.62  fof(f103,plain,(
% 1.70/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_2),
% 1.70/0.62    inference(resolution,[],[f97,f78])).
% 1.70/0.62  fof(f78,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.70/0.62    inference(cnf_transformation,[],[f44])).
% 1.70/0.62  fof(f44,plain,(
% 1.70/0.62    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.70/0.62    inference(flattening,[],[f43])).
% 1.70/0.62  fof(f43,plain,(
% 1.70/0.62    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.70/0.62    inference(ennf_transformation,[],[f23])).
% 1.70/0.62  fof(f23,axiom,(
% 1.70/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.70/0.62  fof(f175,plain,(
% 1.70/0.62    spl3_12 | ~spl3_11),
% 1.70/0.62    inference(avatar_split_clause,[],[f168,f164,f172])).
% 1.70/0.62  fof(f168,plain,(
% 1.70/0.62    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl3_11),
% 1.70/0.62    inference(resolution,[],[f166,f82])).
% 1.70/0.62  fof(f166,plain,(
% 1.70/0.62    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl3_11),
% 1.70/0.62    inference(avatar_component_clause,[],[f164])).
% 1.70/0.62  fof(f151,plain,(
% 1.70/0.62    spl3_9 | ~spl3_3 | ~spl3_5),
% 1.70/0.62    inference(avatar_split_clause,[],[f130,f122,f109,f148])).
% 1.70/0.62  fof(f130,plain,(
% 1.70/0.62    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_5)),
% 1.70/0.62    inference(subsumption_resolution,[],[f128,f111])).
% 1.70/0.62  fof(f128,plain,(
% 1.70/0.62    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 1.70/0.62    inference(superposition,[],[f124,f84])).
% 1.70/0.62  fof(f124,plain,(
% 1.70/0.62    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl3_5),
% 1.70/0.62    inference(avatar_component_clause,[],[f122])).
% 1.70/0.62  fof(f125,plain,(
% 1.70/0.62    spl3_4 | spl3_5),
% 1.70/0.62    inference(avatar_split_clause,[],[f53,f122,f118])).
% 1.70/0.62  fof(f53,plain,(
% 1.70/0.62    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.70/0.62    inference(cnf_transformation,[],[f31])).
% 1.70/0.62  fof(f112,plain,(
% 1.70/0.62    spl3_3),
% 1.70/0.62    inference(avatar_split_clause,[],[f55,f109])).
% 1.70/0.62  fof(f55,plain,(
% 1.70/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.70/0.62    inference(cnf_transformation,[],[f31])).
% 1.70/0.62  fof(f98,plain,(
% 1.70/0.62    spl3_2),
% 1.70/0.62    inference(avatar_split_clause,[],[f57,f95])).
% 1.70/0.62  fof(f57,plain,(
% 1.70/0.62    l1_pre_topc(sK0)),
% 1.70/0.62    inference(cnf_transformation,[],[f31])).
% 1.70/0.62  fof(f93,plain,(
% 1.70/0.62    spl3_1),
% 1.70/0.62    inference(avatar_split_clause,[],[f56,f90])).
% 1.70/0.62  fof(f56,plain,(
% 1.70/0.62    v2_pre_topc(sK0)),
% 1.70/0.62    inference(cnf_transformation,[],[f31])).
% 1.70/0.62  % SZS output end Proof for theBenchmark
% 1.70/0.62  % (25249)------------------------------
% 1.70/0.62  % (25249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.62  % (25249)Termination reason: Refutation
% 1.70/0.62  
% 1.70/0.62  % (25249)Memory used [KB]: 11513
% 1.70/0.62  % (25249)Time elapsed: 0.171 s
% 1.70/0.62  % (25249)------------------------------
% 1.70/0.62  % (25249)------------------------------
% 1.70/0.63  % (25228)Success in time 0.257 s
%------------------------------------------------------------------------------
