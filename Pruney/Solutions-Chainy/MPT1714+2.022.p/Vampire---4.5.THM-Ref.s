%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 314 expanded)
%              Number of leaves         :   30 ( 123 expanded)
%              Depth                    :    9
%              Number of atoms          :  432 (1105 expanded)
%              Number of equality atoms :   17 (  33 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f378,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f62,f67,f71,f86,f103,f110,f114,f128,f133,f134,f138,f146,f160,f175,f197,f216,f226,f263,f272,f361,f377])).

fof(f377,plain,
    ( spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f375,f124])).

fof(f124,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_12
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f375,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f374,f145])).

fof(f145,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl7_16
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f374,plain,
    ( ~ l1_struct_0(sK1)
    | r1_tsep_1(sK3,sK1)
    | ~ spl7_13
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f369,f132])).

fof(f132,plain,
    ( l1_struct_0(sK3)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl7_14
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f369,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | r1_tsep_1(sK3,sK1)
    | ~ spl7_13 ),
    inference(resolution,[],[f360,f30])).

fof(f30,plain,(
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

fof(f360,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl7_13
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f361,plain,
    ( spl7_13
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f358,f270,f224,f214,f144,f131,f126])).

fof(f214,plain,
    ( spl7_26
  <=> k2_struct_0(sK3) = u1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f224,plain,
    ( spl7_28
  <=> k2_struct_0(sK1) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f270,plain,
    ( spl7_31
  <=> r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f358,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f357,f145])).

fof(f357,plain,
    ( ~ l1_struct_0(sK1)
    | r1_tsep_1(sK1,sK3)
    | ~ spl7_14
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f354,f271])).

fof(f271,plain,
    ( r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f270])).

fof(f354,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | ~ l1_struct_0(sK1)
    | r1_tsep_1(sK1,sK3)
    | ~ spl7_14
    | ~ spl7_26
    | ~ spl7_28 ),
    inference(superposition,[],[f235,f225])).

fof(f225,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f224])).

fof(f235,plain,
    ( ! [X6] :
        ( ~ r1_xboole_0(u1_struct_0(X6),k2_struct_0(sK3))
        | ~ l1_struct_0(X6)
        | r1_tsep_1(X6,sK3) )
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f231,f132])).

fof(f231,plain,
    ( ! [X6] :
        ( ~ r1_xboole_0(u1_struct_0(X6),k2_struct_0(sK3))
        | ~ l1_struct_0(sK3)
        | ~ l1_struct_0(X6)
        | r1_tsep_1(X6,sK3) )
    | ~ spl7_26 ),
    inference(superposition,[],[f31,f215])).

fof(f215,plain,
    ( k2_struct_0(sK3) = u1_struct_0(sK3)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f214])).

fof(f31,plain,(
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

fof(f272,plain,
    ( spl7_31
    | ~ spl7_19
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f266,f261,f158,f270])).

fof(f158,plain,
    ( spl7_19
  <=> r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f261,plain,
    ( spl7_30
  <=> k2_struct_0(sK3) = k4_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f266,plain,
    ( r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | ~ spl7_19
    | ~ spl7_30 ),
    inference(superposition,[],[f186,f262])).

fof(f262,plain,
    ( k2_struct_0(sK3) = k4_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f261])).

fof(f186,plain,
    ( ! [X0] : r1_xboole_0(k2_struct_0(sK1),k4_xboole_0(X0,k2_struct_0(sK2)))
    | ~ spl7_19 ),
    inference(resolution,[],[f159,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f159,plain,
    ( r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f158])).

fof(f263,plain,
    ( spl7_30
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f199,f195,f261])).

fof(f195,plain,
    ( spl7_24
  <=> r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f199,plain,
    ( k2_struct_0(sK3) = k4_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ spl7_24 ),
    inference(resolution,[],[f196,f38])).

% (21128)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f196,plain,
    ( r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f195])).

fof(f226,plain,
    ( spl7_28
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f161,f144,f224])).

fof(f161,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl7_16 ),
    inference(resolution,[],[f145,f35])).

fof(f35,plain,(
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

fof(f216,plain,
    ( spl7_26
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f151,f131,f214])).

fof(f151,plain,
    ( k2_struct_0(sK3) = u1_struct_0(sK3)
    | ~ spl7_14 ),
    inference(resolution,[],[f132,f35])).

fof(f197,plain,
    ( spl7_24
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f177,f173,f136,f131,f195])).

fof(f136,plain,
    ( spl7_15
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f173,plain,
    ( spl7_22
  <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f177,plain,
    ( r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f176,f151])).

fof(f176,plain,
    ( r1_xboole_0(u1_struct_0(sK3),k2_struct_0(sK2))
    | ~ spl7_15
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f174,f156])).

fof(f156,plain,
    ( k2_struct_0(sK2) = u1_struct_0(sK2)
    | ~ spl7_15 ),
    inference(resolution,[],[f137,f35])).

fof(f137,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f136])).

fof(f174,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f173])).

fof(f175,plain,
    ( spl7_22
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f142,f136,f131,f105,f173])).

fof(f105,plain,
    ( spl7_9
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f142,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f141,f132])).

fof(f141,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK3)
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f139,f137])).

fof(f139,plain,
    ( ~ l1_struct_0(sK2)
    | r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK3)
    | ~ spl7_9 ),
    inference(resolution,[],[f106,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f106,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f160,plain,
    ( spl7_19
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f94,f69,f65,f51,f158])).

fof(f51,plain,
    ( spl7_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f65,plain,
    ( spl7_4
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f69,plain,
    ( spl7_5
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f94,plain,
    ( r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f93,f92])).

fof(f92,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f82,f90])).

fof(f90,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f88,f52])).

fof(f52,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f88,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl7_5 ),
    inference(resolution,[],[f70,f33])).

fof(f33,plain,(
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

fof(f70,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f82,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK1)
    | ~ spl7_4 ),
    inference(resolution,[],[f66,f33])).

fof(f66,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f93,plain,
    ( ~ l1_pre_topc(sK1)
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f81,f90])).

fof(f81,plain,
    ( ~ l1_pre_topc(sK1)
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ spl7_4 ),
    inference(resolution,[],[f66,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f146,plain,
    ( spl7_16
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f129,f112,f144])).

fof(f112,plain,
    ( spl7_11
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f129,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_11 ),
    inference(resolution,[],[f113,f34])).

fof(f34,plain,(
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

fof(f113,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f138,plain,
    ( spl7_15
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f119,f101,f136])).

fof(f101,plain,
    ( spl7_8
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f119,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f102,f34])).

fof(f102,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f134,plain,
    ( spl7_9
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f120,f108,f101,f84,f105])).

fof(f84,plain,
    ( spl7_7
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f108,plain,
    ( spl7_10
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f120,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f118,f119])).

fof(f118,plain,
    ( ~ l1_struct_0(sK2)
    | r1_tsep_1(sK3,sK2)
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f116,f95])).

fof(f95,plain,
    ( l1_struct_0(sK3)
    | ~ spl7_7 ),
    inference(resolution,[],[f85,f34])).

fof(f85,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f116,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | r1_tsep_1(sK3,sK2)
    | ~ spl7_10 ),
    inference(resolution,[],[f109,f30])).

fof(f109,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f133,plain,
    ( spl7_14
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f95,f84,f131])).

fof(f128,plain,
    ( ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f24,f126,f123])).

fof(f24,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | ~ r1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
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
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
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
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
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
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
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
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
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
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f114,plain,
    ( spl7_11
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f92,f69,f65,f51,f112])).

fof(f110,plain,
    ( spl7_9
    | spl7_10 ),
    inference(avatar_split_clause,[],[f23,f108,f105])).

fof(f23,plain,
    ( r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f103,plain,
    ( spl7_8
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f90,f69,f51,f101])).

fof(f86,plain,
    ( spl7_7
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f79,f60,f51,f84])).

fof(f60,plain,
    ( spl7_3
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f79,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f77,f52])).

fof(f77,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f61,f33])).

% (21131)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (21117)Refutation not found, incomplete strategy% (21117)------------------------------
% (21117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21117)Termination reason: Refutation not found, incomplete strategy

% (21117)Memory used [KB]: 10874
% (21117)Time elapsed: 0.065 s
% (21117)------------------------------
% (21117)------------------------------
% (21121)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (21122)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (21130)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% (21129)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (21116)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (21133)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (21118)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (21119)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (21132)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (21127)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f61,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f71,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f27,f69])).

fof(f27,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f67,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f26,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f29,f51])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 21:10:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (21120)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (21117)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (21125)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (21114)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (21115)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (21115)Refutation not found, incomplete strategy% (21115)------------------------------
% 0.22/0.49  % (21115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (21115)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (21115)Memory used [KB]: 10618
% 0.22/0.49  % (21115)Time elapsed: 0.081 s
% 0.22/0.49  % (21115)------------------------------
% 0.22/0.49  % (21115)------------------------------
% 0.22/0.50  % (21114)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f378,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f53,f62,f67,f71,f86,f103,f110,f114,f128,f133,f134,f138,f146,f160,f175,f197,f216,f226,f263,f272,f361,f377])).
% 0.22/0.50  fof(f377,plain,(
% 0.22/0.50    spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f376])).
% 0.22/0.50  fof(f376,plain,(
% 0.22/0.50    $false | (spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16)),
% 0.22/0.50    inference(subsumption_resolution,[],[f375,f124])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    ~r1_tsep_1(sK3,sK1) | spl7_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f123])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    spl7_12 <=> r1_tsep_1(sK3,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.50  fof(f375,plain,(
% 0.22/0.50    r1_tsep_1(sK3,sK1) | (~spl7_13 | ~spl7_14 | ~spl7_16)),
% 0.22/0.50    inference(subsumption_resolution,[],[f374,f145])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    l1_struct_0(sK1) | ~spl7_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f144])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    spl7_16 <=> l1_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.22/0.50  fof(f374,plain,(
% 0.22/0.50    ~l1_struct_0(sK1) | r1_tsep_1(sK3,sK1) | (~spl7_13 | ~spl7_14)),
% 0.22/0.50    inference(subsumption_resolution,[],[f369,f132])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    l1_struct_0(sK3) | ~spl7_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f131])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    spl7_14 <=> l1_struct_0(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.50  fof(f369,plain,(
% 0.22/0.50    ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | r1_tsep_1(sK3,sK1) | ~spl7_13),
% 0.22/0.50    inference(resolution,[],[f360,f30])).
% 0.22/0.50  fof(f30,plain,(
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
% 0.22/0.50  fof(f360,plain,(
% 0.22/0.50    r1_tsep_1(sK1,sK3) | ~spl7_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f126])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    spl7_13 <=> r1_tsep_1(sK1,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.50  fof(f361,plain,(
% 0.22/0.50    spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_26 | ~spl7_28 | ~spl7_31),
% 0.22/0.50    inference(avatar_split_clause,[],[f358,f270,f224,f214,f144,f131,f126])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    spl7_26 <=> k2_struct_0(sK3) = u1_struct_0(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    spl7_28 <=> k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.22/0.50  fof(f270,plain,(
% 0.22/0.50    spl7_31 <=> r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.22/0.50  fof(f358,plain,(
% 0.22/0.50    r1_tsep_1(sK1,sK3) | (~spl7_14 | ~spl7_16 | ~spl7_26 | ~spl7_28 | ~spl7_31)),
% 0.22/0.50    inference(subsumption_resolution,[],[f357,f145])).
% 0.22/0.50  fof(f357,plain,(
% 0.22/0.50    ~l1_struct_0(sK1) | r1_tsep_1(sK1,sK3) | (~spl7_14 | ~spl7_26 | ~spl7_28 | ~spl7_31)),
% 0.22/0.50    inference(subsumption_resolution,[],[f354,f271])).
% 0.22/0.50  fof(f271,plain,(
% 0.22/0.50    r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | ~spl7_31),
% 0.22/0.50    inference(avatar_component_clause,[],[f270])).
% 0.22/0.50  fof(f354,plain,(
% 0.22/0.50    ~r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | ~l1_struct_0(sK1) | r1_tsep_1(sK1,sK3) | (~spl7_14 | ~spl7_26 | ~spl7_28)),
% 0.22/0.50    inference(superposition,[],[f235,f225])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl7_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f224])).
% 0.22/0.50  fof(f235,plain,(
% 0.22/0.50    ( ! [X6] : (~r1_xboole_0(u1_struct_0(X6),k2_struct_0(sK3)) | ~l1_struct_0(X6) | r1_tsep_1(X6,sK3)) ) | (~spl7_14 | ~spl7_26)),
% 0.22/0.50    inference(subsumption_resolution,[],[f231,f132])).
% 0.22/0.50  fof(f231,plain,(
% 0.22/0.50    ( ! [X6] : (~r1_xboole_0(u1_struct_0(X6),k2_struct_0(sK3)) | ~l1_struct_0(sK3) | ~l1_struct_0(X6) | r1_tsep_1(X6,sK3)) ) | ~spl7_26),
% 0.22/0.50    inference(superposition,[],[f31,f215])).
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    k2_struct_0(sK3) = u1_struct_0(sK3) | ~spl7_26),
% 0.22/0.50    inference(avatar_component_clause,[],[f214])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.22/0.50  fof(f272,plain,(
% 0.22/0.50    spl7_31 | ~spl7_19 | ~spl7_30),
% 0.22/0.50    inference(avatar_split_clause,[],[f266,f261,f158,f270])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    spl7_19 <=> r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.22/0.50  fof(f261,plain,(
% 0.22/0.50    spl7_30 <=> k2_struct_0(sK3) = k4_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.22/0.50  fof(f266,plain,(
% 0.22/0.50    r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | (~spl7_19 | ~spl7_30)),
% 0.22/0.50    inference(superposition,[],[f186,f262])).
% 0.22/0.50  fof(f262,plain,(
% 0.22/0.50    k2_struct_0(sK3) = k4_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2)) | ~spl7_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f261])).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    ( ! [X0] : (r1_xboole_0(k2_struct_0(sK1),k4_xboole_0(X0,k2_struct_0(sK2)))) ) | ~spl7_19),
% 0.22/0.50    inference(resolution,[],[f159,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) | ~spl7_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f158])).
% 0.22/0.50  fof(f263,plain,(
% 0.22/0.50    spl7_30 | ~spl7_24),
% 0.22/0.50    inference(avatar_split_clause,[],[f199,f195,f261])).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    spl7_24 <=> r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    k2_struct_0(sK3) = k4_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2)) | ~spl7_24),
% 0.22/0.50    inference(resolution,[],[f196,f38])).
% 0.22/0.50  % (21128)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2)) | ~spl7_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f195])).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    spl7_28 | ~spl7_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f161,f144,f224])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl7_16),
% 0.22/0.50    inference(resolution,[],[f145,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f216,plain,(
% 0.22/0.50    spl7_26 | ~spl7_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f151,f131,f214])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    k2_struct_0(sK3) = u1_struct_0(sK3) | ~spl7_14),
% 0.22/0.50    inference(resolution,[],[f132,f35])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    spl7_24 | ~spl7_14 | ~spl7_15 | ~spl7_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f177,f173,f136,f131,f195])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    spl7_15 <=> l1_struct_0(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    spl7_22 <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2)) | (~spl7_14 | ~spl7_15 | ~spl7_22)),
% 0.22/0.50    inference(forward_demodulation,[],[f176,f151])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    r1_xboole_0(u1_struct_0(sK3),k2_struct_0(sK2)) | (~spl7_15 | ~spl7_22)),
% 0.22/0.50    inference(forward_demodulation,[],[f174,f156])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    k2_struct_0(sK2) = u1_struct_0(sK2) | ~spl7_15),
% 0.22/0.50    inference(resolution,[],[f137,f35])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    l1_struct_0(sK2) | ~spl7_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f136])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~spl7_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f173])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    spl7_22 | ~spl7_9 | ~spl7_14 | ~spl7_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f142,f136,f131,f105,f173])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl7_9 <=> r1_tsep_1(sK3,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | (~spl7_9 | ~spl7_14 | ~spl7_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f141,f132])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~l1_struct_0(sK3) | (~spl7_9 | ~spl7_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f139,f137])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    ~l1_struct_0(sK2) | r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~l1_struct_0(sK3) | ~spl7_9),
% 0.22/0.50    inference(resolution,[],[f106,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    r1_tsep_1(sK3,sK2) | ~spl7_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f105])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    spl7_19 | ~spl7_1 | ~spl7_4 | ~spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f94,f69,f65,f51,f158])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    spl7_1 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl7_4 <=> m1_pre_topc(sK1,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl7_5 <=> m1_pre_topc(sK2,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) | (~spl7_1 | ~spl7_4 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f93,f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    l1_pre_topc(sK1) | (~spl7_1 | ~spl7_4 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f82,f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    l1_pre_topc(sK2) | (~spl7_1 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f88,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    l1_pre_topc(sK0) | ~spl7_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f51])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | l1_pre_topc(sK2) | ~spl7_5),
% 0.22/0.50    inference(resolution,[],[f70,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    m1_pre_topc(sK2,sK0) | ~spl7_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f69])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ~l1_pre_topc(sK2) | l1_pre_topc(sK1) | ~spl7_4),
% 0.22/0.50    inference(resolution,[],[f66,f33])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    m1_pre_topc(sK1,sK2) | ~spl7_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f65])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ~l1_pre_topc(sK1) | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) | (~spl7_1 | ~spl7_4 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f81,f90])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ~l1_pre_topc(sK1) | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~spl7_4),
% 0.22/0.50    inference(resolution,[],[f66,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    spl7_16 | ~spl7_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f129,f112,f144])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    spl7_11 <=> l1_pre_topc(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    l1_struct_0(sK1) | ~spl7_11),
% 0.22/0.50    inference(resolution,[],[f113,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    l1_pre_topc(sK1) | ~spl7_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f112])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    spl7_15 | ~spl7_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f119,f101,f136])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl7_8 <=> l1_pre_topc(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    l1_struct_0(sK2) | ~spl7_8),
% 0.22/0.50    inference(resolution,[],[f102,f34])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    l1_pre_topc(sK2) | ~spl7_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f101])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    spl7_9 | ~spl7_7 | ~spl7_8 | ~spl7_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f120,f108,f101,f84,f105])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl7_7 <=> l1_pre_topc(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    spl7_10 <=> r1_tsep_1(sK2,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    r1_tsep_1(sK3,sK2) | (~spl7_7 | ~spl7_8 | ~spl7_10)),
% 0.22/0.50    inference(subsumption_resolution,[],[f118,f119])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    ~l1_struct_0(sK2) | r1_tsep_1(sK3,sK2) | (~spl7_7 | ~spl7_10)),
% 0.22/0.50    inference(subsumption_resolution,[],[f116,f95])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    l1_struct_0(sK3) | ~spl7_7),
% 0.22/0.50    inference(resolution,[],[f85,f34])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    l1_pre_topc(sK3) | ~spl7_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f84])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | r1_tsep_1(sK3,sK2) | ~spl7_10),
% 0.22/0.50    inference(resolution,[],[f109,f30])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    r1_tsep_1(sK2,sK3) | ~spl7_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f108])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl7_14 | ~spl7_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f95,f84,f131])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ~spl7_12 | ~spl7_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f24,f126,f123])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ~r1_tsep_1(sK1,sK3) | ~r1_tsep_1(sK3,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.50  fof(f10,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f9])).
% 0.22/0.50  fof(f9,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    spl7_11 | ~spl7_1 | ~spl7_4 | ~spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f92,f69,f65,f51,f112])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    spl7_9 | spl7_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f23,f108,f105])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    r1_tsep_1(sK2,sK3) | r1_tsep_1(sK3,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    spl7_8 | ~spl7_1 | ~spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f90,f69,f51,f101])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    spl7_7 | ~spl7_1 | ~spl7_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f79,f60,f51,f84])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl7_3 <=> m1_pre_topc(sK3,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    l1_pre_topc(sK3) | (~spl7_1 | ~spl7_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f77,f52])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | l1_pre_topc(sK3) | ~spl7_3),
% 0.22/0.50    inference(resolution,[],[f61,f33])).
% 0.22/0.50  % (21131)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (21117)Refutation not found, incomplete strategy% (21117)------------------------------
% 0.22/0.50  % (21117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (21117)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (21117)Memory used [KB]: 10874
% 0.22/0.50  % (21117)Time elapsed: 0.065 s
% 0.22/0.50  % (21117)------------------------------
% 0.22/0.50  % (21117)------------------------------
% 0.22/0.50  % (21121)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (21122)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (21130)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (21129)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (21116)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (21133)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (21118)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (21119)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (21132)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.52  % (21127)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    m1_pre_topc(sK3,sK0) | ~spl7_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f60])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    spl7_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f27,f69])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    m1_pre_topc(sK2,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    spl7_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f26,f65])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    m1_pre_topc(sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    spl7_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f25,f60])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    m1_pre_topc(sK3,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    spl7_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f29,f51])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    l1_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (21114)------------------------------
% 0.22/0.52  % (21114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21114)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (21114)Memory used [KB]: 6396
% 0.22/0.52  % (21114)Time elapsed: 0.078 s
% 0.22/0.52  % (21114)------------------------------
% 0.22/0.52  % (21114)------------------------------
% 0.22/0.52  % (21113)Success in time 0.156 s
%------------------------------------------------------------------------------
