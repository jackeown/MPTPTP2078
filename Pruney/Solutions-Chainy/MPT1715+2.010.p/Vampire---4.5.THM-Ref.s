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
% DateTime   : Thu Dec  3 13:17:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 341 expanded)
%              Number of leaves         :   30 ( 133 expanded)
%              Depth                    :    9
%              Number of atoms          :  459 (1184 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f426,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f64,f69,f73,f88,f105,f112,f116,f124,f135,f136,f140,f148,f162,f171,f195,f218,f234,f238,f284,f401,f416,f425])).

fof(f425,plain,
    ( spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f419,f138,f133,f122,f119])).

fof(f119,plain,
    ( spl7_12
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f122,plain,
    ( spl7_13
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f133,plain,
    ( spl7_14
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f138,plain,
    ( spl7_15
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f419,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f418,f139])).

fof(f139,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f138])).

fof(f418,plain,
    ( ~ l1_struct_0(sK2)
    | r1_tsep_1(sK3,sK2)
    | ~ spl7_13
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f142,f134])).

fof(f134,plain,
    ( l1_struct_0(sK3)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f142,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | r1_tsep_1(sK3,sK2)
    | ~ spl7_13 ),
    inference(resolution,[],[f123,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f123,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f416,plain,
    ( ~ spl7_9
    | spl7_10
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | ~ spl7_9
    | spl7_10
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f414,f111])).

fof(f111,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl7_10
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f414,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f413,f134])).

fof(f413,plain,
    ( ~ l1_struct_0(sK3)
    | r1_tsep_1(sK1,sK3)
    | ~ spl7_9
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f408,f147])).

fof(f147,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl7_16
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f408,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK1,sK3)
    | ~ spl7_9 ),
    inference(resolution,[],[f400,f31])).

fof(f400,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl7_9
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f401,plain,
    ( spl7_9
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f391,f282,f232,f216,f146,f133,f107])).

fof(f216,plain,
    ( spl7_26
  <=> k2_struct_0(sK3) = u1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f232,plain,
    ( spl7_30
  <=> k2_struct_0(sK1) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f282,plain,
    ( spl7_33
  <=> r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f391,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f390,f147])).

fof(f390,plain,
    ( ~ l1_struct_0(sK1)
    | r1_tsep_1(sK3,sK1)
    | ~ spl7_14
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f387,f283])).

fof(f283,plain,
    ( r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f282])).

fof(f387,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | r1_tsep_1(sK3,sK1)
    | ~ spl7_14
    | ~ spl7_26
    | ~ spl7_30 ),
    inference(superposition,[],[f247,f233])).

fof(f233,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f232])).

fof(f247,plain,
    ( ! [X7] :
        ( ~ r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X7))
        | ~ l1_struct_0(X7)
        | r1_tsep_1(sK3,X7) )
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f243,f134])).

fof(f243,plain,
    ( ! [X7] :
        ( ~ r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X7))
        | ~ l1_struct_0(X7)
        | ~ l1_struct_0(sK3)
        | r1_tsep_1(sK3,X7) )
    | ~ spl7_26 ),
    inference(superposition,[],[f32,f217])).

fof(f217,plain,
    ( k2_struct_0(sK3) = u1_struct_0(sK3)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f216])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f284,plain,
    ( spl7_33
    | ~ spl7_23
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f280,f236,f193,f282])).

fof(f193,plain,
    ( spl7_23
  <=> r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f236,plain,
    ( spl7_31
  <=> k2_struct_0(sK2) = k2_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f280,plain,
    ( r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_31 ),
    inference(resolution,[],[f274,f194])).

fof(f194,plain,
    ( r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f193])).

fof(f274,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k2_struct_0(sK2))
        | r1_xboole_0(X0,k2_struct_0(sK1)) )
    | ~ spl7_31 ),
    inference(superposition,[],[f37,f237])).

fof(f237,plain,
    ( k2_struct_0(sK2) = k2_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f236])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f238,plain,
    ( spl7_31
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f188,f160,f236])).

fof(f160,plain,
    ( spl7_19
  <=> r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f188,plain,
    ( k2_struct_0(sK2) = k2_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ spl7_19 ),
    inference(resolution,[],[f161,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f161,plain,
    ( r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f160])).

fof(f234,plain,
    ( spl7_30
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f163,f146,f232])).

fof(f163,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl7_16 ),
    inference(resolution,[],[f147,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f218,plain,
    ( spl7_26
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f153,f133,f216])).

fof(f153,plain,
    ( k2_struct_0(sK3) = u1_struct_0(sK3)
    | ~ spl7_14 ),
    inference(resolution,[],[f134,f36])).

fof(f195,plain,
    ( spl7_23
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f173,f169,f138,f133,f193])).

fof(f169,plain,
    ( spl7_21
  <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f173,plain,
    ( r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f172,f153])).

fof(f172,plain,
    ( r1_xboole_0(u1_struct_0(sK3),k2_struct_0(sK2))
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f170,f158])).

fof(f158,plain,
    ( k2_struct_0(sK2) = u1_struct_0(sK2)
    | ~ spl7_15 ),
    inference(resolution,[],[f139,f36])).

fof(f170,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f169])).

fof(f171,plain,
    ( spl7_21
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f129,f119,f103,f86,f169])).

fof(f86,plain,
    ( spl7_7
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f103,plain,
    ( spl7_8
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f129,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f128,f97])).

fof(f97,plain,
    ( l1_struct_0(sK3)
    | ~ spl7_7 ),
    inference(resolution,[],[f87,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f87,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f128,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK3)
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f126,f117])).

fof(f117,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f104,f35])).

fof(f104,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f126,plain,
    ( ~ l1_struct_0(sK2)
    | r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK3)
    | ~ spl7_12 ),
    inference(resolution,[],[f120,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f120,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f162,plain,
    ( spl7_19
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f96,f71,f67,f53,f160])).

fof(f53,plain,
    ( spl7_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f67,plain,
    ( spl7_4
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f71,plain,
    ( spl7_5
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f96,plain,
    ( r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f95,f94])).

fof(f94,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f84,f92])).

fof(f92,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f90,f54])).

fof(f54,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f90,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl7_5 ),
    inference(resolution,[],[f72,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f72,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f84,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK1)
    | ~ spl7_4 ),
    inference(resolution,[],[f68,f34])).

fof(f68,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f95,plain,
    ( ~ l1_pre_topc(sK1)
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f83,f92])).

fof(f83,plain,
    ( ~ l1_pre_topc(sK1)
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ spl7_4 ),
    inference(resolution,[],[f68,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f148,plain,
    ( spl7_16
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f125,f114,f146])).

fof(f114,plain,
    ( spl7_11
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f125,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_11 ),
    inference(resolution,[],[f115,f35])).

fof(f115,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f140,plain,
    ( spl7_15
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f117,f103,f138])).

fof(f136,plain,
    ( spl7_13
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f131,f119,f103,f86,f122])).

fof(f131,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f130,f97])).

fof(f130,plain,
    ( ~ l1_struct_0(sK3)
    | r1_tsep_1(sK2,sK3)
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f127,f117])).

fof(f127,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK2,sK3)
    | ~ spl7_12 ),
    inference(resolution,[],[f120,f31])).

fof(f135,plain,
    ( spl7_14
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f97,f86,f133])).

fof(f124,plain,
    ( spl7_12
    | spl7_13 ),
    inference(avatar_split_clause,[],[f25,f122,f119])).

fof(f25,plain,
    ( r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f116,plain,
    ( spl7_11
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f94,f71,f67,f53,f114])).

fof(f112,plain,
    ( ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f24,f110,f107])).

fof(f24,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | ~ r1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f105,plain,
    ( spl7_8
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f92,f71,f53,f103])).

fof(f88,plain,
    ( spl7_7
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f81,f62,f53,f86])).

fof(f62,plain,
    ( spl7_3
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f81,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f79,f54])).

fof(f79,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f63,f34])).

fof(f63,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f73,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f28,f71])).

fof(f28,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f26,f62])).

fof(f26,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f30,f53])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:31:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (17922)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (17914)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (17921)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (17915)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (17915)Refutation not found, incomplete strategy% (17915)------------------------------
% 0.22/0.48  % (17915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (17915)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (17915)Memory used [KB]: 10618
% 0.22/0.48  % (17915)Time elapsed: 0.061 s
% 0.22/0.48  % (17915)------------------------------
% 0.22/0.48  % (17915)------------------------------
% 0.22/0.48  % (17929)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (17919)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (17920)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (17914)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f426,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f55,f64,f69,f73,f88,f105,f112,f116,f124,f135,f136,f140,f148,f162,f171,f195,f218,f234,f238,f284,f401,f416,f425])).
% 0.22/0.50  fof(f425,plain,(
% 0.22/0.50    spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f419,f138,f133,f122,f119])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    spl7_12 <=> r1_tsep_1(sK3,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    spl7_13 <=> r1_tsep_1(sK2,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl7_14 <=> l1_struct_0(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    spl7_15 <=> l1_struct_0(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.50  fof(f419,plain,(
% 0.22/0.50    r1_tsep_1(sK3,sK2) | (~spl7_13 | ~spl7_14 | ~spl7_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f418,f139])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    l1_struct_0(sK2) | ~spl7_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f138])).
% 0.22/0.50  fof(f418,plain,(
% 0.22/0.50    ~l1_struct_0(sK2) | r1_tsep_1(sK3,sK2) | (~spl7_13 | ~spl7_14)),
% 0.22/0.50    inference(subsumption_resolution,[],[f142,f134])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    l1_struct_0(sK3) | ~spl7_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f133])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | r1_tsep_1(sK3,sK2) | ~spl7_13),
% 0.22/0.50    inference(resolution,[],[f123,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    r1_tsep_1(sK2,sK3) | ~spl7_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f122])).
% 0.22/0.50  fof(f416,plain,(
% 0.22/0.50    ~spl7_9 | spl7_10 | ~spl7_14 | ~spl7_16),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f415])).
% 0.22/0.50  fof(f415,plain,(
% 0.22/0.50    $false | (~spl7_9 | spl7_10 | ~spl7_14 | ~spl7_16)),
% 0.22/0.50    inference(subsumption_resolution,[],[f414,f111])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    ~r1_tsep_1(sK1,sK3) | spl7_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f110])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    spl7_10 <=> r1_tsep_1(sK1,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.50  fof(f414,plain,(
% 0.22/0.50    r1_tsep_1(sK1,sK3) | (~spl7_9 | ~spl7_14 | ~spl7_16)),
% 0.22/0.50    inference(subsumption_resolution,[],[f413,f134])).
% 0.22/0.50  fof(f413,plain,(
% 0.22/0.50    ~l1_struct_0(sK3) | r1_tsep_1(sK1,sK3) | (~spl7_9 | ~spl7_16)),
% 0.22/0.50    inference(subsumption_resolution,[],[f408,f147])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    l1_struct_0(sK1) | ~spl7_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f146])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    spl7_16 <=> l1_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.22/0.50  fof(f408,plain,(
% 0.22/0.50    ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | r1_tsep_1(sK1,sK3) | ~spl7_9),
% 0.22/0.50    inference(resolution,[],[f400,f31])).
% 0.22/0.50  fof(f400,plain,(
% 0.22/0.50    r1_tsep_1(sK3,sK1) | ~spl7_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f107])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    spl7_9 <=> r1_tsep_1(sK3,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.50  fof(f401,plain,(
% 0.22/0.50    spl7_9 | ~spl7_14 | ~spl7_16 | ~spl7_26 | ~spl7_30 | ~spl7_33),
% 0.22/0.50    inference(avatar_split_clause,[],[f391,f282,f232,f216,f146,f133,f107])).
% 0.22/0.50  fof(f216,plain,(
% 0.22/0.50    spl7_26 <=> k2_struct_0(sK3) = u1_struct_0(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.50  fof(f232,plain,(
% 0.22/0.50    spl7_30 <=> k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.22/0.50  fof(f282,plain,(
% 0.22/0.50    spl7_33 <=> r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.22/0.50  fof(f391,plain,(
% 0.22/0.50    r1_tsep_1(sK3,sK1) | (~spl7_14 | ~spl7_16 | ~spl7_26 | ~spl7_30 | ~spl7_33)),
% 0.22/0.50    inference(subsumption_resolution,[],[f390,f147])).
% 0.22/0.50  fof(f390,plain,(
% 0.22/0.50    ~l1_struct_0(sK1) | r1_tsep_1(sK3,sK1) | (~spl7_14 | ~spl7_26 | ~spl7_30 | ~spl7_33)),
% 0.22/0.50    inference(subsumption_resolution,[],[f387,f283])).
% 0.22/0.50  fof(f283,plain,(
% 0.22/0.50    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | ~spl7_33),
% 0.22/0.50    inference(avatar_component_clause,[],[f282])).
% 0.22/0.50  fof(f387,plain,(
% 0.22/0.50    ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | ~l1_struct_0(sK1) | r1_tsep_1(sK3,sK1) | (~spl7_14 | ~spl7_26 | ~spl7_30)),
% 0.22/0.50    inference(superposition,[],[f247,f233])).
% 0.22/0.50  fof(f233,plain,(
% 0.22/0.50    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl7_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f232])).
% 0.22/0.50  fof(f247,plain,(
% 0.22/0.50    ( ! [X7] : (~r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X7)) | ~l1_struct_0(X7) | r1_tsep_1(sK3,X7)) ) | (~spl7_14 | ~spl7_26)),
% 0.22/0.50    inference(subsumption_resolution,[],[f243,f134])).
% 0.22/0.50  fof(f243,plain,(
% 0.22/0.50    ( ! [X7] : (~r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X7)) | ~l1_struct_0(X7) | ~l1_struct_0(sK3) | r1_tsep_1(sK3,X7)) ) | ~spl7_26),
% 0.22/0.50    inference(superposition,[],[f32,f217])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    k2_struct_0(sK3) = u1_struct_0(sK3) | ~spl7_26),
% 0.22/0.50    inference(avatar_component_clause,[],[f216])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.22/0.50  fof(f284,plain,(
% 0.22/0.50    spl7_33 | ~spl7_23 | ~spl7_31),
% 0.22/0.50    inference(avatar_split_clause,[],[f280,f236,f193,f282])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    spl7_23 <=> r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    spl7_31 <=> k2_struct_0(sK2) = k2_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.22/0.50  fof(f280,plain,(
% 0.22/0.50    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | (~spl7_23 | ~spl7_31)),
% 0.22/0.50    inference(resolution,[],[f274,f194])).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2)) | ~spl7_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f193])).
% 0.22/0.50  fof(f274,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_xboole_0(X0,k2_struct_0(sK2)) | r1_xboole_0(X0,k2_struct_0(sK1))) ) | ~spl7_31),
% 0.22/0.50    inference(superposition,[],[f37,f237])).
% 0.22/0.50  fof(f237,plain,(
% 0.22/0.50    k2_struct_0(sK2) = k2_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2)) | ~spl7_31),
% 0.22/0.50    inference(avatar_component_clause,[],[f236])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    spl7_31 | ~spl7_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f188,f160,f236])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    spl7_19 <=> r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    k2_struct_0(sK2) = k2_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2)) | ~spl7_19),
% 0.22/0.50    inference(resolution,[],[f161,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) | ~spl7_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f160])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    spl7_30 | ~spl7_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f163,f146,f232])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl7_16),
% 0.22/0.50    inference(resolution,[],[f147,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    spl7_26 | ~spl7_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f153,f133,f216])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    k2_struct_0(sK3) = u1_struct_0(sK3) | ~spl7_14),
% 0.22/0.50    inference(resolution,[],[f134,f36])).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    spl7_23 | ~spl7_14 | ~spl7_15 | ~spl7_21),
% 0.22/0.50    inference(avatar_split_clause,[],[f173,f169,f138,f133,f193])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    spl7_21 <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2)) | (~spl7_14 | ~spl7_15 | ~spl7_21)),
% 0.22/0.50    inference(forward_demodulation,[],[f172,f153])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    r1_xboole_0(u1_struct_0(sK3),k2_struct_0(sK2)) | (~spl7_15 | ~spl7_21)),
% 0.22/0.50    inference(forward_demodulation,[],[f170,f158])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    k2_struct_0(sK2) = u1_struct_0(sK2) | ~spl7_15),
% 0.22/0.50    inference(resolution,[],[f139,f36])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~spl7_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f169])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    spl7_21 | ~spl7_7 | ~spl7_8 | ~spl7_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f129,f119,f103,f86,f169])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    spl7_7 <=> l1_pre_topc(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    spl7_8 <=> l1_pre_topc(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | (~spl7_7 | ~spl7_8 | ~spl7_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f128,f97])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    l1_struct_0(sK3) | ~spl7_7),
% 0.22/0.50    inference(resolution,[],[f87,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    l1_pre_topc(sK3) | ~spl7_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f86])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~l1_struct_0(sK3) | (~spl7_8 | ~spl7_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f126,f117])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    l1_struct_0(sK2) | ~spl7_8),
% 0.22/0.50    inference(resolution,[],[f104,f35])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    l1_pre_topc(sK2) | ~spl7_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f103])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ~l1_struct_0(sK2) | r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~l1_struct_0(sK3) | ~spl7_12),
% 0.22/0.50    inference(resolution,[],[f120,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    r1_tsep_1(sK3,sK2) | ~spl7_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f119])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    spl7_19 | ~spl7_1 | ~spl7_4 | ~spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f96,f71,f67,f53,f160])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    spl7_1 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    spl7_4 <=> m1_pre_topc(sK1,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    spl7_5 <=> m1_pre_topc(sK2,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) | (~spl7_1 | ~spl7_4 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f95,f94])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    l1_pre_topc(sK1) | (~spl7_1 | ~spl7_4 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f84,f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    l1_pre_topc(sK2) | (~spl7_1 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f90,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    l1_pre_topc(sK0) | ~spl7_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f53])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | l1_pre_topc(sK2) | ~spl7_5),
% 0.22/0.50    inference(resolution,[],[f72,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    m1_pre_topc(sK2,sK0) | ~spl7_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f71])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ~l1_pre_topc(sK2) | l1_pre_topc(sK1) | ~spl7_4),
% 0.22/0.50    inference(resolution,[],[f68,f34])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    m1_pre_topc(sK1,sK2) | ~spl7_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f67])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ~l1_pre_topc(sK1) | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) | (~spl7_1 | ~spl7_4 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f83,f92])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ~l1_pre_topc(sK1) | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~spl7_4),
% 0.22/0.50    inference(resolution,[],[f68,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    spl7_16 | ~spl7_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f125,f114,f146])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    spl7_11 <=> l1_pre_topc(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    l1_struct_0(sK1) | ~spl7_11),
% 0.22/0.50    inference(resolution,[],[f115,f35])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    l1_pre_topc(sK1) | ~spl7_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f114])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    spl7_15 | ~spl7_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f117,f103,f138])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    spl7_13 | ~spl7_7 | ~spl7_8 | ~spl7_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f131,f119,f103,f86,f122])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    r1_tsep_1(sK2,sK3) | (~spl7_7 | ~spl7_8 | ~spl7_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f130,f97])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    ~l1_struct_0(sK3) | r1_tsep_1(sK2,sK3) | (~spl7_8 | ~spl7_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f127,f117])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    ~l1_struct_0(sK2) | ~l1_struct_0(sK3) | r1_tsep_1(sK2,sK3) | ~spl7_12),
% 0.22/0.50    inference(resolution,[],[f120,f31])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    spl7_14 | ~spl7_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f97,f86,f133])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    spl7_12 | spl7_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f25,f122,f119])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    r1_tsep_1(sK2,sK3) | r1_tsep_1(sK3,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.50  fof(f10,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f9])).
% 0.22/0.50  fof(f9,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    spl7_11 | ~spl7_1 | ~spl7_4 | ~spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f94,f71,f67,f53,f114])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ~spl7_9 | ~spl7_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f24,f110,f107])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ~r1_tsep_1(sK1,sK3) | ~r1_tsep_1(sK3,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl7_8 | ~spl7_1 | ~spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f92,f71,f53,f103])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl7_7 | ~spl7_1 | ~spl7_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f81,f62,f53,f86])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    spl7_3 <=> m1_pre_topc(sK3,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    l1_pre_topc(sK3) | (~spl7_1 | ~spl7_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f79,f54])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | l1_pre_topc(sK3) | ~spl7_3),
% 0.22/0.50    inference(resolution,[],[f63,f34])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    m1_pre_topc(sK3,sK0) | ~spl7_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f62])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f71])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    m1_pre_topc(sK2,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl7_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f27,f67])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    m1_pre_topc(sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    spl7_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f62])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    m1_pre_topc(sK3,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    spl7_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f53])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (17914)------------------------------
% 0.22/0.50  % (17914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (17914)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (17914)Memory used [KB]: 6396
% 0.22/0.50  % (17918)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (17914)Time elapsed: 0.076 s
% 0.22/0.50  % (17914)------------------------------
% 0.22/0.50  % (17914)------------------------------
% 0.22/0.50  % (17933)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (17932)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (17928)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (17913)Success in time 0.135 s
%------------------------------------------------------------------------------
