%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 337 expanded)
%              Number of leaves         :   43 ( 160 expanded)
%              Depth                    :    9
%              Number of atoms          :  535 (1264 expanded)
%              Number of equality atoms :   31 ( 130 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f487,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f94,f99,f104,f109,f114,f119,f125,f139,f155,f156,f167,f172,f214,f215,f226,f260,f267,f321,f343,f395,f405,f428,f449,f486])).

fof(f486,plain,
    ( ~ spl4_24
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_14
    | ~ spl4_36
    | ~ spl4_50
    | spl4_53 ),
    inference(avatar_split_clause,[],[f483,f446,f425,f318,f164,f111,f101,f242])).

fof(f242,plain,
    ( spl4_24
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f101,plain,
    ( spl4_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f111,plain,
    ( spl4_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f164,plain,
    ( spl4_14
  <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f318,plain,
    ( spl4_36
  <=> v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f425,plain,
    ( spl4_50
  <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f446,plain,
    ( spl4_53
  <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f483,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_14
    | ~ spl4_36
    | ~ spl4_50
    | spl4_53 ),
    inference(unit_resulting_resolution,[],[f113,f103,f320,f166,f448,f427,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X1,X0)
                  & r1_xboole_0(X1,X2) )
               => r1_xboole_0(X1,k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).

fof(f427,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f425])).

fof(f448,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | spl4_53 ),
    inference(avatar_component_clause,[],[f446])).

fof(f166,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f164])).

fof(f320,plain,
    ( v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f318])).

fof(f103,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f113,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f449,plain,
    ( ~ spl4_53
    | ~ spl4_20
    | spl4_46 ),
    inference(avatar_split_clause,[],[f432,f402,f210,f446])).

fof(f210,plain,
    ( spl4_20
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f402,plain,
    ( spl4_46
  <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f432,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl4_20
    | spl4_46 ),
    inference(backward_demodulation,[],[f404,f212])).

fof(f212,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f404,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl4_46 ),
    inference(avatar_component_clause,[],[f402])).

fof(f428,plain,
    ( spl4_50
    | spl4_44 ),
    inference(avatar_split_clause,[],[f417,f392,f425])).

fof(f392,plain,
    ( spl4_44
  <=> r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f417,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))
    | spl4_44 ),
    inference(unit_resulting_resolution,[],[f394,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,k2_tarski(X0,X0))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f77,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f60])).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f394,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | spl4_44 ),
    inference(avatar_component_clause,[],[f392])).

fof(f405,plain,
    ( ~ spl4_46
    | spl4_2
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f388,f205,f86,f402])).

fof(f86,plain,
    ( spl4_2
  <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f205,plain,
    ( spl4_19
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f388,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl4_2
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f88,f207])).

fof(f207,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f205])).

fof(f88,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f395,plain,
    ( ~ spl4_44
    | ~ spl4_19
    | spl4_28 ),
    inference(avatar_split_clause,[],[f386,f264,f205,f392])).

fof(f264,plain,
    ( spl4_28
  <=> r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f386,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | ~ spl4_19
    | spl4_28 ),
    inference(backward_demodulation,[],[f266,f207])).

fof(f266,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f264])).

fof(f343,plain,
    ( spl4_24
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f338,f169,f101,f242])).

fof(f169,plain,
    ( spl4_15
  <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f338,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f171,f240])).

fof(f240,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_5 ),
    inference(resolution,[],[f75,f103])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f171,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f169])).

fof(f321,plain,
    ( ~ spl4_24
    | spl4_36
    | ~ spl4_21
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f313,f258,f223,f318,f242])).

fof(f223,plain,
    ( spl4_21
  <=> v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f258,plain,
    ( spl4_27
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f313,plain,
    ( v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_21
    | ~ spl4_27 ),
    inference(resolution,[],[f259,f225])).

fof(f225,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f223])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f258])).

fof(f267,plain,
    ( ~ spl4_28
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f262,f116,f111,f106,f101,f96,f91,f81,f264])).

fof(f81,plain,
    ( spl4_1
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f91,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f96,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f106,plain,
    ( spl4_6
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f116,plain,
    ( spl4_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f262,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f118,f113,f108,f103,f93,f98,f83,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
               => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).

fof(f83,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f98,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f93,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f108,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f118,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f260,plain,
    ( ~ spl4_7
    | ~ spl4_5
    | spl4_27
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f256,f106,f258,f101,f111])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f64,f108])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ v3_tdlat_3(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK3(X0),X0)
            & v4_pre_topc(sK3(X0),X0)
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & v4_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f226,plain,
    ( spl4_21
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f221,f169,f111,f101,f223])).

fof(f221,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f113,f103,f171,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f215,plain,
    ( spl4_11
    | spl4_19
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f199,f96,f205,f136])).

fof(f136,plain,
    ( spl4_11
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f199,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f79,f98])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f73,f60])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f214,plain,
    ( spl4_11
    | spl4_20
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f198,f91,f210,f136])).

% (31728)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f198,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f79,f93])).

fof(f172,plain,
    ( spl4_15
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f160,f146,f169])).

fof(f146,plain,
    ( spl4_12
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f160,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f148,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f60])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f148,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f167,plain,
    ( spl4_14
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f161,f151,f164])).

fof(f151,plain,
    ( spl4_13
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f161,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f153,f78])).

fof(f153,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f151])).

fof(f156,plain,
    ( spl4_12
    | spl4_11
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f143,f96,f136,f146])).

fof(f143,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f72,f98])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f155,plain,
    ( spl4_13
    | spl4_11
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f142,f91,f136,f151])).

fof(f142,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f72,f93])).

fof(f139,plain,
    ( ~ spl4_11
    | spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f134,f122,f116,f136])).

fof(f122,plain,
    ( spl4_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f134,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_8
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f118,f124,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f124,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f125,plain,
    ( spl4_9
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f120,f101,f122])).

fof(f120,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f103,f61])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f119,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f50,f116])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
              & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
            & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
          & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
      & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                  | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).

fof(f114,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f51,f111])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f109,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f52,f106])).

fof(f52,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f104,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f53,f101])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f99,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f54,f96])).

fof(f54,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f55,f91])).

fof(f55,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f89,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f56,f86])).

fof(f56,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f84,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f57,f81])).

fof(f57,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:36:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (31739)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (31738)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (31732)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (31742)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (31738)Refutation not found, incomplete strategy% (31738)------------------------------
% 0.22/0.47  % (31738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (31730)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (31731)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (31734)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (31733)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (31729)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (31738)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (31738)Memory used [KB]: 10618
% 0.22/0.49  % (31738)Time elapsed: 0.062 s
% 0.22/0.49  % (31738)------------------------------
% 0.22/0.49  % (31738)------------------------------
% 0.22/0.49  % (31727)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (31740)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (31733)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f487,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f84,f89,f94,f99,f104,f109,f114,f119,f125,f139,f155,f156,f167,f172,f214,f215,f226,f260,f267,f321,f343,f395,f405,f428,f449,f486])).
% 0.22/0.50  fof(f486,plain,(
% 0.22/0.50    ~spl4_24 | ~spl4_5 | ~spl4_7 | ~spl4_14 | ~spl4_36 | ~spl4_50 | spl4_53),
% 0.22/0.50    inference(avatar_split_clause,[],[f483,f446,f425,f318,f164,f111,f101,f242])).
% 0.22/0.50  fof(f242,plain,(
% 0.22/0.50    spl4_24 <=> m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl4_5 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    spl4_7 <=> v2_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    spl4_14 <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.50  fof(f318,plain,(
% 0.22/0.50    spl4_36 <=> v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.50  fof(f425,plain,(
% 0.22/0.50    spl4_50 <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.22/0.50  fof(f446,plain,(
% 0.22/0.50    spl4_53 <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.22/0.50  fof(f483,plain,(
% 0.22/0.50    ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_5 | ~spl4_7 | ~spl4_14 | ~spl4_36 | ~spl4_50 | spl4_53)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f113,f103,f320,f166,f448,f427,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,X0) | r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).
% 0.22/0.50  fof(f427,plain,(
% 0.22/0.50    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) | ~spl4_50),
% 0.22/0.50    inference(avatar_component_clause,[],[f425])).
% 0.22/0.50  fof(f448,plain,(
% 0.22/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | spl4_53),
% 0.22/0.50    inference(avatar_component_clause,[],[f446])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f164])).
% 0.22/0.50  fof(f320,plain,(
% 0.22/0.50    v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~spl4_36),
% 0.22/0.50    inference(avatar_component_clause,[],[f318])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    l1_pre_topc(sK0) | ~spl4_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f101])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    v2_pre_topc(sK0) | ~spl4_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f111])).
% 0.22/0.50  fof(f449,plain,(
% 0.22/0.50    ~spl4_53 | ~spl4_20 | spl4_46),
% 0.22/0.50    inference(avatar_split_clause,[],[f432,f402,f210,f446])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    spl4_20 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.50  fof(f402,plain,(
% 0.22/0.50    spl4_46 <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.22/0.50  fof(f432,plain,(
% 0.22/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl4_20 | spl4_46)),
% 0.22/0.50    inference(backward_demodulation,[],[f404,f212])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | ~spl4_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f210])).
% 0.22/0.50  fof(f404,plain,(
% 0.22/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl4_46),
% 0.22/0.50    inference(avatar_component_clause,[],[f402])).
% 0.22/0.50  fof(f428,plain,(
% 0.22/0.50    spl4_50 | spl4_44),
% 0.22/0.50    inference(avatar_split_clause,[],[f417,f392,f425])).
% 0.22/0.50  fof(f392,plain,(
% 0.22/0.50    spl4_44 <=> r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.22/0.50  fof(f417,plain,(
% 0.22/0.50    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) | spl4_44),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f394,f157])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(X1,k2_tarski(X0,X0)) | r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(resolution,[],[f77,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f69,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.22/0.50  fof(f394,plain,(
% 0.22/0.50    ~r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | spl4_44),
% 0.22/0.50    inference(avatar_component_clause,[],[f392])).
% 0.22/0.50  fof(f405,plain,(
% 0.22/0.50    ~spl4_46 | spl4_2 | ~spl4_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f388,f205,f86,f402])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    spl4_2 <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    spl4_19 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.50  fof(f388,plain,(
% 0.22/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | (spl4_2 | ~spl4_19)),
% 0.22/0.50    inference(backward_demodulation,[],[f88,f207])).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | ~spl4_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f205])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl4_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f86])).
% 0.22/0.50  fof(f395,plain,(
% 0.22/0.50    ~spl4_44 | ~spl4_19 | spl4_28),
% 0.22/0.50    inference(avatar_split_clause,[],[f386,f264,f205,f392])).
% 0.22/0.50  fof(f264,plain,(
% 0.22/0.50    spl4_28 <=> r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.50  fof(f386,plain,(
% 0.22/0.50    ~r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | (~spl4_19 | spl4_28)),
% 0.22/0.50    inference(backward_demodulation,[],[f266,f207])).
% 0.22/0.50  fof(f266,plain,(
% 0.22/0.50    ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | spl4_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f264])).
% 0.22/0.50  fof(f343,plain,(
% 0.22/0.50    spl4_24 | ~spl4_5 | ~spl4_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f338,f169,f101,f242])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    spl4_15 <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.50  fof(f338,plain,(
% 0.22/0.50    m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_5 | ~spl4_15)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f171,f240])).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_5),
% 0.22/0.50    inference(resolution,[],[f75,f103])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f169])).
% 0.22/0.50  fof(f321,plain,(
% 0.22/0.50    ~spl4_24 | spl4_36 | ~spl4_21 | ~spl4_27),
% 0.22/0.50    inference(avatar_split_clause,[],[f313,f258,f223,f318,f242])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    spl4_21 <=> v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.50  fof(f258,plain,(
% 0.22/0.50    spl4_27 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.22/0.50  fof(f313,plain,(
% 0.22/0.50    v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_21 | ~spl4_27)),
% 0.22/0.50    inference(resolution,[],[f259,f225])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~spl4_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f223])).
% 0.22/0.50  fof(f259,plain,(
% 0.22/0.50    ( ! [X0] : (~v4_pre_topc(X0,sK0) | v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_27),
% 0.22/0.50    inference(avatar_component_clause,[],[f258])).
% 0.22/0.50  fof(f267,plain,(
% 0.22/0.50    ~spl4_28 | spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | spl4_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f262,f116,f111,f106,f101,f96,f91,f81,f264])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    spl4_1 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    spl4_3 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    spl4_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    spl4_6 <=> v3_tdlat_3(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    spl4_8 <=> v2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.50  fof(f262,plain,(
% 0.22/0.50    ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | spl4_8)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f118,f113,f108,f103,f93,f98,f83,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) | spl4_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f81])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f96])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl4_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f91])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    v3_tdlat_3(sK0) | ~spl4_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f106])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    ~v2_struct_0(sK0) | spl4_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f116])).
% 0.22/0.50  fof(f260,plain,(
% 0.22/0.50    ~spl4_7 | ~spl4_5 | spl4_27 | ~spl4_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f256,f106,f258,f101,f111])).
% 0.22/0.50  fof(f256,plain,(
% 0.22/0.50    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl4_6),
% 0.22/0.50    inference(resolution,[],[f64,f108])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X2,X0] : (~v3_tdlat_3(X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(rectify,[],[f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    spl4_21 | ~spl4_5 | ~spl4_7 | ~spl4_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f221,f169,f111,f101,f223])).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | (~spl4_5 | ~spl4_7 | ~spl4_15)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f113,f103,f171,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    spl4_11 | spl4_19 | ~spl4_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f199,f96,f205,f136])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    spl4_11 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | v1_xboole_0(u1_struct_0(sK0)) | ~spl4_4),
% 0.22/0.50    inference(resolution,[],[f79,f98])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f73,f60])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    spl4_11 | spl4_20 | ~spl4_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f198,f91,f210,f136])).
% 0.22/0.50  % (31728)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | v1_xboole_0(u1_struct_0(sK0)) | ~spl4_3),
% 0.22/0.50    inference(resolution,[],[f79,f93])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    spl4_15 | ~spl4_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f160,f146,f169])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    spl4_12 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_12),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f148,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f70,f60])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    r2_hidden(sK1,u1_struct_0(sK0)) | ~spl4_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f146])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    spl4_14 | ~spl4_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f161,f151,f164])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    spl4_13 <=> r2_hidden(sK2,u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_13),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f153,f78])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    r2_hidden(sK2,u1_struct_0(sK0)) | ~spl4_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f151])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    spl4_12 | spl4_11 | ~spl4_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f143,f96,f136,f146])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0)) | ~spl4_4),
% 0.22/0.50    inference(resolution,[],[f72,f98])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    spl4_13 | spl4_11 | ~spl4_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f142,f91,f136,f151])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK2,u1_struct_0(sK0)) | ~spl4_3),
% 0.22/0.50    inference(resolution,[],[f72,f93])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    ~spl4_11 | spl4_8 | ~spl4_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f134,f122,f116,f136])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    spl4_9 <=> l1_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    ~v1_xboole_0(u1_struct_0(sK0)) | (spl4_8 | ~spl4_9)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f118,f124,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    l1_struct_0(sK0) | ~spl4_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f122])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    spl4_9 | ~spl4_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f120,f101,f122])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    l1_struct_0(sK0) | ~spl4_5),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f103,f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ~spl4_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f50,f116])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ((k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f44,f43,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) => (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f17])).
% 0.22/0.50  fof(f17,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    spl4_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f51,f111])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    v2_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    spl4_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f52,f106])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    v3_tdlat_3(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    spl4_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f53,f101])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl4_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f54,f96])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    spl4_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f55,f91])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ~spl4_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f56,f86])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ~spl4_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f57,f81])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (31733)------------------------------
% 0.22/0.50  % (31733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (31733)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (31733)Memory used [KB]: 6396
% 0.22/0.50  % (31733)Time elapsed: 0.057 s
% 0.22/0.50  % (31733)------------------------------
% 0.22/0.50  % (31733)------------------------------
% 0.22/0.50  % (31726)Success in time 0.144 s
%------------------------------------------------------------------------------
