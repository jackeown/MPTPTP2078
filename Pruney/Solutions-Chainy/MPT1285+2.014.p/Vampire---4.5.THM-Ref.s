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
% DateTime   : Thu Dec  3 13:13:07 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 335 expanded)
%              Number of leaves         :   32 ( 155 expanded)
%              Depth                    :   13
%              Number of atoms          :  574 (2072 expanded)
%              Number of equality atoms :   40 (  55 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f310,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f87,f96,f101,f106,f115,f116,f117,f137,f169,f174,f182,f187,f192,f231,f257,f283,f304,f309])).

fof(f309,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_23
    | spl4_24 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_23
    | spl4_24 ),
    inference(subsumption_resolution,[],[f307,f303])).

fof(f303,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl4_24
  <=> sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f307,plain,
    ( sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f306,f249])).

fof(f249,plain,
    ( r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f76,f91,f86,f168,f186,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f186,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl4_18
  <=> m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f168,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl4_15
  <=> r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f86,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f91,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_6
  <=> v3_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f76,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f306,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ spl4_23 ),
    inference(resolution,[],[f256,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f256,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl4_23
  <=> r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f304,plain,
    ( ~ spl4_24
    | ~ spl4_3
    | ~ spl4_5
    | spl4_9 ),
    inference(avatar_split_clause,[],[f208,f103,f84,f74,f301])).

fof(f103,plain,
    ( spl4_9
  <=> v6_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f208,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ spl4_3
    | ~ spl4_5
    | spl4_9 ),
    inference(unit_resulting_resolution,[],[f76,f86,f105,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

fof(f105,plain,
    ( ~ v6_tops_1(sK3,sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f283,plain,
    ( ~ spl4_2
    | ~ spl4_4
    | spl4_11
    | ~ spl4_12
    | ~ spl4_16
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_4
    | spl4_11
    | ~ spl4_12
    | ~ spl4_16
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f281,f136])).

fof(f136,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_12
  <=> r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f281,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl4_2
    | ~ spl4_4
    | spl4_11
    | ~ spl4_16
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f280,f172])).

fof(f172,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl4_16
  <=> sK2 = k1_tops_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f280,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ spl4_2
    | ~ spl4_4
    | spl4_11
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f279,f71])).

fof(f71,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f279,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_4
    | spl4_11
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f278,f81])).

fof(f81,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f278,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_11
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f277,f114])).

fof(f114,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_11
  <=> v4_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f277,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f273,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f273,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_19 ),
    inference(superposition,[],[f50,f191])).

fof(f191,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl4_19
  <=> sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

fof(f257,plain,
    ( spl4_23
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f201,f98,f84,f74,f254])).

fof(f98,plain,
    ( spl4_8
  <=> v4_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f201,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f76,f86,f100,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v4_tops_1(X1,X0)
      | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f100,plain,
    ( v4_tops_1(sK3,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f231,plain,
    ( ~ spl4_2
    | spl4_16
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl4_2
    | spl4_16
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f229,f173])).

fof(f173,plain,
    ( sK2 != k1_tops_1(sK0,sK2)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f171])).

fof(f229,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl4_2
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f228,f191])).

fof(f228,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2)))
    | ~ spl4_2
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f71,f181,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f181,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl4_17
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f192,plain,
    ( spl4_19
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f130,f93,f79,f69,f189])).

fof(f93,plain,
    ( spl4_7
  <=> v6_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f130,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f71,f95,f81,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f187,plain,
    ( spl4_18
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f125,f84,f74,f184])).

fof(f125,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f76,f86,f54])).

% (6769)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f182,plain,
    ( spl4_17
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f124,f79,f69,f179])).

fof(f124,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f71,f81,f54])).

fof(f174,plain,
    ( ~ spl4_16
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_10 ),
    inference(avatar_split_clause,[],[f132,f108,f79,f69,f64,f171])).

fof(f64,plain,
    ( spl4_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f108,plain,
    ( spl4_10
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f132,plain,
    ( sK2 != k1_tops_1(sK0,sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f66,f71,f110,f81,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X1,X0) != X0
      | v3_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v3_pre_topc(X0,X1)
      | k1_tops_1(X1,X0) != X0
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(condensation,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f110,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f66,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f169,plain,
    ( spl4_15
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f121,f84,f74,f166])).

fof(f121,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f76,f86,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f137,plain,
    ( spl4_12
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f120,f79,f69,f134])).

fof(f120,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f71,f81,f45])).

fof(f117,plain,
    ( ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f44,f112,f108,f103])).

fof(f44,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ( ( ~ v4_tops_1(sK2,sK0)
          | ~ v3_pre_topc(sK2,sK0) )
        & v6_tops_1(sK2,sK0) )
      | ( ~ v6_tops_1(sK3,sK1)
        & v4_tops_1(sK3,sK1)
        & v3_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f27,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ v4_tops_1(X2,X0)
                          | ~ v3_pre_topc(X2,X0) )
                        & v6_tops_1(X2,X0) )
                      | ( ~ v6_tops_1(X3,X1)
                        & v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK0)
                        | ~ v3_pre_topc(X2,sK0) )
                      & v6_tops_1(X2,sK0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,sK0)
                      | ~ v3_pre_topc(X2,sK0) )
                    & v6_tops_1(X2,sK0) )
                  | ( ~ v6_tops_1(X3,X1)
                    & v4_tops_1(X3,X1)
                    & v3_pre_topc(X3,X1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,sK0)
                    | ~ v3_pre_topc(X2,sK0) )
                  & v6_tops_1(X2,sK0) )
                | ( ~ v6_tops_1(X3,sK1)
                  & v4_tops_1(X3,sK1)
                  & v3_pre_topc(X3,sK1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(X2,sK0)
                  | ~ v3_pre_topc(X2,sK0) )
                & v6_tops_1(X2,sK0) )
              | ( ~ v6_tops_1(X3,sK1)
                & v4_tops_1(X3,sK1)
                & v3_pre_topc(X3,sK1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(sK2,sK0)
                | ~ v3_pre_topc(sK2,sK0) )
              & v6_tops_1(sK2,sK0) )
            | ( ~ v6_tops_1(X3,sK1)
              & v4_tops_1(X3,sK1)
              & v3_pre_topc(X3,sK1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ( ( ( ~ v4_tops_1(sK2,sK0)
              | ~ v3_pre_topc(sK2,sK0) )
            & v6_tops_1(sK2,sK0) )
          | ( ~ v6_tops_1(X3,sK1)
            & v4_tops_1(X3,sK1)
            & v3_pre_topc(X3,sK1) ) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ( ( ~ v4_tops_1(sK2,sK0)
            | ~ v3_pre_topc(sK2,sK0) )
          & v6_tops_1(sK2,sK0) )
        | ( ~ v6_tops_1(sK3,sK1)
          & v4_tops_1(sK3,sK1)
          & v3_pre_topc(sK3,sK1) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v6_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v3_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v3_pre_topc(X3,X1) )
                       => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v6_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v3_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) )
                     => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).

fof(f116,plain,
    ( spl4_8
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f43,f112,f108,f98])).

fof(f43,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f115,plain,
    ( spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f42,f112,f108,f89])).

fof(f42,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f106,plain,
    ( ~ spl4_9
    | spl4_7 ),
    inference(avatar_split_clause,[],[f41,f93,f103])).

fof(f41,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f101,plain,
    ( spl4_8
    | spl4_7 ),
    inference(avatar_split_clause,[],[f40,f93,f98])).

fof(f40,plain,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f96,plain,
    ( spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f39,f93,f89])).

fof(f39,plain,
    ( v6_tops_1(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f87,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f38,f84])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f37,f79])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f36,f74])).

fof(f36,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f35,f69])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f34,f64])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 14:17:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.50  % (6754)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.50  % (6757)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.51  % (6773)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.51  % (6761)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.51  % (6755)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.52  % (6762)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.52  % (6752)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.52  % (6773)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.52  % SZS output start Proof for theBenchmark
% 0.23/0.52  fof(f310,plain,(
% 0.23/0.52    $false),
% 0.23/0.52    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f87,f96,f101,f106,f115,f116,f117,f137,f169,f174,f182,f187,f192,f231,f257,f283,f304,f309])).
% 0.23/0.52  fof(f309,plain,(
% 0.23/0.52    ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_15 | ~spl4_18 | ~spl4_23 | spl4_24),
% 0.23/0.52    inference(avatar_contradiction_clause,[],[f308])).
% 0.23/0.52  fof(f308,plain,(
% 0.23/0.52    $false | (~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_15 | ~spl4_18 | ~spl4_23 | spl4_24)),
% 0.23/0.52    inference(subsumption_resolution,[],[f307,f303])).
% 0.23/0.52  fof(f303,plain,(
% 0.23/0.52    sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | spl4_24),
% 0.23/0.52    inference(avatar_component_clause,[],[f301])).
% 0.23/0.52  fof(f301,plain,(
% 0.23/0.52    spl4_24 <=> sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.23/0.52  fof(f307,plain,(
% 0.23/0.52    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | (~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_15 | ~spl4_18 | ~spl4_23)),
% 0.23/0.52    inference(subsumption_resolution,[],[f306,f249])).
% 0.23/0.52  fof(f249,plain,(
% 0.23/0.52    r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | (~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_15 | ~spl4_18)),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f76,f91,f86,f168,f186,f51])).
% 0.23/0.52  fof(f51,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f17])).
% 0.23/0.52  fof(f17,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.52    inference(flattening,[],[f16])).
% 0.23/0.52  fof(f16,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.52    inference(ennf_transformation,[],[f8])).
% 0.23/0.52  fof(f8,axiom,(
% 0.23/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 0.23/0.52  fof(f186,plain,(
% 0.23/0.52    m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl4_18),
% 0.23/0.52    inference(avatar_component_clause,[],[f184])).
% 0.23/0.52  fof(f184,plain,(
% 0.23/0.52    spl4_18 <=> m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.23/0.52  fof(f168,plain,(
% 0.23/0.52    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | ~spl4_15),
% 0.23/0.52    inference(avatar_component_clause,[],[f166])).
% 0.23/0.52  fof(f166,plain,(
% 0.23/0.52    spl4_15 <=> r1_tarski(sK3,k2_pre_topc(sK1,sK3))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.23/0.52  fof(f86,plain,(
% 0.23/0.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl4_5),
% 0.23/0.52    inference(avatar_component_clause,[],[f84])).
% 0.23/0.52  fof(f84,plain,(
% 0.23/0.52    spl4_5 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.23/0.52  fof(f91,plain,(
% 0.23/0.52    v3_pre_topc(sK3,sK1) | ~spl4_6),
% 0.23/0.52    inference(avatar_component_clause,[],[f89])).
% 0.23/0.52  fof(f89,plain,(
% 0.23/0.52    spl4_6 <=> v3_pre_topc(sK3,sK1)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.23/0.52  fof(f76,plain,(
% 0.23/0.52    l1_pre_topc(sK1) | ~spl4_3),
% 0.23/0.52    inference(avatar_component_clause,[],[f74])).
% 0.23/0.52  fof(f74,plain,(
% 0.23/0.52    spl4_3 <=> l1_pre_topc(sK1)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.23/0.52  fof(f306,plain,(
% 0.23/0.52    ~r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~spl4_23),
% 0.23/0.52    inference(resolution,[],[f256,f58])).
% 0.23/0.52  fof(f58,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.23/0.52    inference(cnf_transformation,[],[f33])).
% 0.23/0.52  fof(f33,plain,(
% 0.23/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.52    inference(flattening,[],[f32])).
% 0.23/0.52  fof(f32,plain,(
% 0.23/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.52    inference(nnf_transformation,[],[f1])).
% 0.23/0.52  fof(f1,axiom,(
% 0.23/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.52  fof(f256,plain,(
% 0.23/0.52    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~spl4_23),
% 0.23/0.52    inference(avatar_component_clause,[],[f254])).
% 0.23/0.52  fof(f254,plain,(
% 0.23/0.52    spl4_23 <=> r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.23/0.52  fof(f304,plain,(
% 0.23/0.52    ~spl4_24 | ~spl4_3 | ~spl4_5 | spl4_9),
% 0.23/0.52    inference(avatar_split_clause,[],[f208,f103,f84,f74,f301])).
% 0.23/0.52  fof(f103,plain,(
% 0.23/0.52    spl4_9 <=> v6_tops_1(sK3,sK1)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.23/0.52  fof(f208,plain,(
% 0.23/0.52    sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | (~spl4_3 | ~spl4_5 | spl4_9)),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f76,f86,f105,f47])).
% 0.23/0.52  fof(f47,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f29])).
% 0.23/0.52  fof(f29,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.52    inference(nnf_transformation,[],[f14])).
% 0.23/0.52  fof(f14,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.52    inference(ennf_transformation,[],[f5])).
% 0.23/0.52  fof(f5,axiom,(
% 0.23/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).
% 0.23/0.52  fof(f105,plain,(
% 0.23/0.52    ~v6_tops_1(sK3,sK1) | spl4_9),
% 0.23/0.52    inference(avatar_component_clause,[],[f103])).
% 0.23/0.52  fof(f283,plain,(
% 0.23/0.52    ~spl4_2 | ~spl4_4 | spl4_11 | ~spl4_12 | ~spl4_16 | ~spl4_19),
% 0.23/0.52    inference(avatar_contradiction_clause,[],[f282])).
% 0.23/0.52  fof(f282,plain,(
% 0.23/0.52    $false | (~spl4_2 | ~spl4_4 | spl4_11 | ~spl4_12 | ~spl4_16 | ~spl4_19)),
% 0.23/0.52    inference(subsumption_resolution,[],[f281,f136])).
% 0.23/0.52  fof(f136,plain,(
% 0.23/0.52    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | ~spl4_12),
% 0.23/0.52    inference(avatar_component_clause,[],[f134])).
% 0.23/0.52  fof(f134,plain,(
% 0.23/0.52    spl4_12 <=> r1_tarski(sK2,k2_pre_topc(sK0,sK2))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.23/0.52  fof(f281,plain,(
% 0.23/0.52    ~r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | (~spl4_2 | ~spl4_4 | spl4_11 | ~spl4_16 | ~spl4_19)),
% 0.23/0.52    inference(forward_demodulation,[],[f280,f172])).
% 0.23/0.52  fof(f172,plain,(
% 0.23/0.52    sK2 = k1_tops_1(sK0,sK2) | ~spl4_16),
% 0.23/0.52    inference(avatar_component_clause,[],[f171])).
% 0.23/0.52  fof(f171,plain,(
% 0.23/0.52    spl4_16 <=> sK2 = k1_tops_1(sK0,sK2)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.23/0.52  fof(f280,plain,(
% 0.23/0.52    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | (~spl4_2 | ~spl4_4 | spl4_11 | ~spl4_19)),
% 0.23/0.52    inference(subsumption_resolution,[],[f279,f71])).
% 0.23/0.52  fof(f71,plain,(
% 0.23/0.52    l1_pre_topc(sK0) | ~spl4_2),
% 0.23/0.52    inference(avatar_component_clause,[],[f69])).
% 0.23/0.52  fof(f69,plain,(
% 0.23/0.52    spl4_2 <=> l1_pre_topc(sK0)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.23/0.52  fof(f279,plain,(
% 0.23/0.52    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | ~l1_pre_topc(sK0) | (~spl4_4 | spl4_11 | ~spl4_19)),
% 0.23/0.52    inference(subsumption_resolution,[],[f278,f81])).
% 0.23/0.52  fof(f81,plain,(
% 0.23/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_4),
% 0.23/0.52    inference(avatar_component_clause,[],[f79])).
% 0.23/0.52  fof(f79,plain,(
% 0.23/0.52    spl4_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.23/0.52  fof(f278,plain,(
% 0.23/0.52    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl4_11 | ~spl4_19)),
% 0.23/0.52    inference(subsumption_resolution,[],[f277,f114])).
% 0.23/0.52  fof(f114,plain,(
% 0.23/0.52    ~v4_tops_1(sK2,sK0) | spl4_11),
% 0.23/0.52    inference(avatar_component_clause,[],[f112])).
% 0.23/0.52  fof(f112,plain,(
% 0.23/0.52    spl4_11 <=> v4_tops_1(sK2,sK0)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.23/0.52  fof(f277,plain,(
% 0.23/0.52    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_19),
% 0.23/0.52    inference(subsumption_resolution,[],[f273,f59])).
% 0.23/0.52  fof(f59,plain,(
% 0.23/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.52    inference(equality_resolution,[],[f57])).
% 0.23/0.52  fof(f57,plain,(
% 0.23/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.52    inference(cnf_transformation,[],[f33])).
% 0.23/0.52  fof(f273,plain,(
% 0.23/0.52    ~r1_tarski(sK2,sK2) | ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_19),
% 0.23/0.52    inference(superposition,[],[f50,f191])).
% 0.23/0.52  fof(f191,plain,(
% 0.23/0.52    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~spl4_19),
% 0.23/0.52    inference(avatar_component_clause,[],[f189])).
% 0.23/0.52  fof(f189,plain,(
% 0.23/0.52    spl4_19 <=> sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.23/0.52  fof(f50,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f31])).
% 0.23/0.52  fof(f31,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.52    inference(flattening,[],[f30])).
% 0.23/0.52  fof(f30,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.52    inference(nnf_transformation,[],[f15])).
% 0.23/0.52  fof(f15,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.52    inference(ennf_transformation,[],[f4])).
% 0.23/0.52  fof(f4,axiom,(
% 0.23/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).
% 0.23/0.52  fof(f257,plain,(
% 0.23/0.52    spl4_23 | ~spl4_3 | ~spl4_5 | ~spl4_8),
% 0.23/0.52    inference(avatar_split_clause,[],[f201,f98,f84,f74,f254])).
% 0.23/0.52  fof(f98,plain,(
% 0.23/0.52    spl4_8 <=> v4_tops_1(sK3,sK1)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.23/0.52  fof(f201,plain,(
% 0.23/0.52    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | (~spl4_3 | ~spl4_5 | ~spl4_8)),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f76,f86,f100,f48])).
% 0.23/0.52  fof(f48,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~v4_tops_1(X1,X0) | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f31])).
% 0.23/0.52  fof(f100,plain,(
% 0.23/0.52    v4_tops_1(sK3,sK1) | ~spl4_8),
% 0.23/0.52    inference(avatar_component_clause,[],[f98])).
% 0.23/0.52  fof(f231,plain,(
% 0.23/0.52    ~spl4_2 | spl4_16 | ~spl4_17 | ~spl4_19),
% 0.23/0.52    inference(avatar_contradiction_clause,[],[f230])).
% 0.23/0.52  fof(f230,plain,(
% 0.23/0.52    $false | (~spl4_2 | spl4_16 | ~spl4_17 | ~spl4_19)),
% 0.23/0.52    inference(subsumption_resolution,[],[f229,f173])).
% 0.23/0.52  fof(f173,plain,(
% 0.23/0.52    sK2 != k1_tops_1(sK0,sK2) | spl4_16),
% 0.23/0.52    inference(avatar_component_clause,[],[f171])).
% 0.23/0.52  fof(f229,plain,(
% 0.23/0.52    sK2 = k1_tops_1(sK0,sK2) | (~spl4_2 | ~spl4_17 | ~spl4_19)),
% 0.23/0.52    inference(forward_demodulation,[],[f228,f191])).
% 0.23/0.52  fof(f228,plain,(
% 0.23/0.52    k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) | (~spl4_2 | ~spl4_17)),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f71,f181,f55])).
% 0.23/0.52  fof(f55,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f23])).
% 0.23/0.52  fof(f23,plain,(
% 0.23/0.52    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.23/0.52    inference(flattening,[],[f22])).
% 0.23/0.52  fof(f22,plain,(
% 0.23/0.52    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.23/0.52    inference(ennf_transformation,[],[f6])).
% 0.23/0.52  fof(f6,axiom,(
% 0.23/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 0.23/0.52  fof(f181,plain,(
% 0.23/0.52    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_17),
% 0.23/0.52    inference(avatar_component_clause,[],[f179])).
% 0.23/0.52  fof(f179,plain,(
% 0.23/0.52    spl4_17 <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.23/0.52  fof(f192,plain,(
% 0.23/0.52    spl4_19 | ~spl4_2 | ~spl4_4 | ~spl4_7),
% 0.23/0.52    inference(avatar_split_clause,[],[f130,f93,f79,f69,f189])).
% 0.23/0.52  fof(f93,plain,(
% 0.23/0.52    spl4_7 <=> v6_tops_1(sK2,sK0)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.23/0.52  fof(f130,plain,(
% 0.23/0.52    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | (~spl4_2 | ~spl4_4 | ~spl4_7)),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f71,f95,f81,f46])).
% 0.23/0.52  fof(f46,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f29])).
% 0.23/0.52  fof(f95,plain,(
% 0.23/0.52    v6_tops_1(sK2,sK0) | ~spl4_7),
% 0.23/0.52    inference(avatar_component_clause,[],[f93])).
% 0.23/0.52  fof(f187,plain,(
% 0.23/0.52    spl4_18 | ~spl4_3 | ~spl4_5),
% 0.23/0.52    inference(avatar_split_clause,[],[f125,f84,f74,f184])).
% 0.23/0.52  fof(f125,plain,(
% 0.23/0.52    m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl4_3 | ~spl4_5)),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f76,f86,f54])).
% 0.23/0.52  % (6769)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.52  fof(f54,plain,(
% 0.23/0.52    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f21])).
% 0.23/0.52  fof(f21,plain,(
% 0.23/0.52    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.23/0.52    inference(flattening,[],[f20])).
% 0.23/0.52  fof(f20,plain,(
% 0.23/0.52    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.23/0.52    inference(ennf_transformation,[],[f2])).
% 0.23/0.52  fof(f2,axiom,(
% 0.23/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.23/0.52  fof(f182,plain,(
% 0.23/0.52    spl4_17 | ~spl4_2 | ~spl4_4),
% 0.23/0.52    inference(avatar_split_clause,[],[f124,f79,f69,f179])).
% 0.23/0.52  fof(f124,plain,(
% 0.23/0.52    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_4)),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f71,f81,f54])).
% 0.23/0.52  fof(f174,plain,(
% 0.23/0.52    ~spl4_16 | ~spl4_1 | ~spl4_2 | ~spl4_4 | spl4_10),
% 0.23/0.52    inference(avatar_split_clause,[],[f132,f108,f79,f69,f64,f171])).
% 0.23/0.52  fof(f64,plain,(
% 0.23/0.52    spl4_1 <=> v2_pre_topc(sK0)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.23/0.52  fof(f108,plain,(
% 0.23/0.52    spl4_10 <=> v3_pre_topc(sK2,sK0)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.23/0.52  fof(f132,plain,(
% 0.23/0.52    sK2 != k1_tops_1(sK0,sK2) | (~spl4_1 | ~spl4_2 | ~spl4_4 | spl4_10)),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f66,f71,f110,f81,f62])).
% 0.23/0.52  fof(f62,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k1_tops_1(X1,X0) != X0 | v3_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.23/0.52    inference(duplicate_literal_removal,[],[f61])).
% 0.23/0.52  fof(f61,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v3_pre_topc(X0,X1) | k1_tops_1(X1,X0) != X0 | ~l1_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.23/0.52    inference(condensation,[],[f53])).
% 0.23/0.52  fof(f53,plain,(
% 0.23/0.52    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f19])).
% 0.23/0.52  fof(f19,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.52    inference(flattening,[],[f18])).
% 0.23/0.52  fof(f18,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.52    inference(ennf_transformation,[],[f7])).
% 0.23/0.52  fof(f7,axiom,(
% 0.23/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 0.23/0.52  fof(f110,plain,(
% 0.23/0.52    ~v3_pre_topc(sK2,sK0) | spl4_10),
% 0.23/0.52    inference(avatar_component_clause,[],[f108])).
% 0.23/0.52  fof(f66,plain,(
% 0.23/0.52    v2_pre_topc(sK0) | ~spl4_1),
% 0.23/0.52    inference(avatar_component_clause,[],[f64])).
% 0.23/0.52  fof(f169,plain,(
% 0.23/0.52    spl4_15 | ~spl4_3 | ~spl4_5),
% 0.23/0.52    inference(avatar_split_clause,[],[f121,f84,f74,f166])).
% 0.23/0.52  fof(f121,plain,(
% 0.23/0.52    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | (~spl4_3 | ~spl4_5)),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f76,f86,f45])).
% 0.23/0.52  fof(f45,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f13])).
% 0.23/0.52  fof(f13,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.52    inference(ennf_transformation,[],[f3])).
% 0.23/0.52  fof(f3,axiom,(
% 0.23/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.23/0.52  fof(f137,plain,(
% 0.23/0.52    spl4_12 | ~spl4_2 | ~spl4_4),
% 0.23/0.52    inference(avatar_split_clause,[],[f120,f79,f69,f134])).
% 0.23/0.52  fof(f120,plain,(
% 0.23/0.52    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | (~spl4_2 | ~spl4_4)),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f71,f81,f45])).
% 0.23/0.52  fof(f117,plain,(
% 0.23/0.52    ~spl4_9 | ~spl4_10 | ~spl4_11),
% 0.23/0.52    inference(avatar_split_clause,[],[f44,f112,f108,f103])).
% 0.23/0.52  fof(f44,plain,(
% 0.23/0.52    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 0.23/0.52    inference(cnf_transformation,[],[f28])).
% 0.23/0.52  fof(f28,plain,(
% 0.23/0.52    ((((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f27,f26,f25,f24])).
% 0.23/0.52  fof(f24,plain,(
% 0.23/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f25,plain,(
% 0.23/0.52    ? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f26,plain,(
% 0.23/0.52    ? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f27,plain,(
% 0.23/0.52    ? [X3] : ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f12,plain,(
% 0.23/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.52    inference(flattening,[],[f11])).
% 0.23/0.52  fof(f11,plain,(
% 0.23/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.23/0.52    inference(ennf_transformation,[],[f10])).
% 0.23/0.52  fof(f10,negated_conjecture,(
% 0.23/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 0.23/0.52    inference(negated_conjecture,[],[f9])).
% 0.23/0.52  fof(f9,conjecture,(
% 0.23/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).
% 0.23/0.52  fof(f116,plain,(
% 0.23/0.52    spl4_8 | ~spl4_10 | ~spl4_11),
% 0.23/0.52    inference(avatar_split_clause,[],[f43,f112,f108,f98])).
% 0.23/0.52  fof(f43,plain,(
% 0.23/0.52    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 0.23/0.52    inference(cnf_transformation,[],[f28])).
% 0.23/0.52  fof(f115,plain,(
% 0.23/0.52    spl4_6 | ~spl4_10 | ~spl4_11),
% 0.23/0.52    inference(avatar_split_clause,[],[f42,f112,f108,f89])).
% 0.23/0.52  fof(f42,plain,(
% 0.23/0.52    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 0.23/0.52    inference(cnf_transformation,[],[f28])).
% 0.23/0.52  fof(f106,plain,(
% 0.23/0.52    ~spl4_9 | spl4_7),
% 0.23/0.52    inference(avatar_split_clause,[],[f41,f93,f103])).
% 0.23/0.52  fof(f41,plain,(
% 0.23/0.52    v6_tops_1(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 0.23/0.52    inference(cnf_transformation,[],[f28])).
% 0.23/0.52  fof(f101,plain,(
% 0.23/0.52    spl4_8 | spl4_7),
% 0.23/0.52    inference(avatar_split_clause,[],[f40,f93,f98])).
% 0.23/0.52  fof(f40,plain,(
% 0.23/0.52    v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 0.23/0.52    inference(cnf_transformation,[],[f28])).
% 0.23/0.53  fof(f96,plain,(
% 0.23/0.53    spl4_6 | spl4_7),
% 0.23/0.53    inference(avatar_split_clause,[],[f39,f93,f89])).
% 0.23/0.53  fof(f39,plain,(
% 0.23/0.53    v6_tops_1(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 0.23/0.53    inference(cnf_transformation,[],[f28])).
% 0.23/0.53  fof(f87,plain,(
% 0.23/0.53    spl4_5),
% 0.23/0.53    inference(avatar_split_clause,[],[f38,f84])).
% 0.23/0.53  fof(f38,plain,(
% 0.23/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.23/0.53    inference(cnf_transformation,[],[f28])).
% 0.23/0.53  fof(f82,plain,(
% 0.23/0.53    spl4_4),
% 0.23/0.53    inference(avatar_split_clause,[],[f37,f79])).
% 0.23/0.53  fof(f37,plain,(
% 0.23/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.53    inference(cnf_transformation,[],[f28])).
% 0.23/0.53  fof(f77,plain,(
% 0.23/0.53    spl4_3),
% 0.23/0.53    inference(avatar_split_clause,[],[f36,f74])).
% 0.23/0.53  fof(f36,plain,(
% 0.23/0.53    l1_pre_topc(sK1)),
% 0.23/0.53    inference(cnf_transformation,[],[f28])).
% 0.23/0.53  fof(f72,plain,(
% 0.23/0.53    spl4_2),
% 0.23/0.53    inference(avatar_split_clause,[],[f35,f69])).
% 0.23/0.53  fof(f35,plain,(
% 0.23/0.53    l1_pre_topc(sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f28])).
% 0.23/0.53  fof(f67,plain,(
% 0.23/0.53    spl4_1),
% 0.23/0.53    inference(avatar_split_clause,[],[f34,f64])).
% 0.23/0.53  fof(f34,plain,(
% 0.23/0.53    v2_pre_topc(sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f28])).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (6773)------------------------------
% 0.23/0.53  % (6773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (6773)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (6773)Memory used [KB]: 10746
% 0.23/0.53  % (6773)Time elapsed: 0.087 s
% 0.23/0.53  % (6773)------------------------------
% 0.23/0.53  % (6773)------------------------------
% 1.20/0.53  % (6749)Success in time 0.15 s
%------------------------------------------------------------------------------
