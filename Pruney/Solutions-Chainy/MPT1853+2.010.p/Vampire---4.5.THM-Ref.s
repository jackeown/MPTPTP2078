%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 350 expanded)
%              Number of leaves         :   35 ( 139 expanded)
%              Depth                    :   12
%              Number of atoms          :  597 (1083 expanded)
%              Number of equality atoms :   25 (  51 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f269,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f76,f81,f85,f102,f109,f114,f125,f129,f141,f148,f161,f169,f176,f181,f190,f198,f204,f206,f229,f267,f268])).

fof(f268,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f267,plain,
    ( spl4_27
    | ~ spl4_2
    | spl4_6
    | ~ spl4_10
    | ~ spl4_19
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f235,f227,f179,f127,f104,f74,f265])).

fof(f265,plain,
    ( spl4_27
  <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f74,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f104,plain,
    ( spl4_6
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f127,plain,
    ( spl4_10
  <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f179,plain,
    ( spl4_19
  <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f227,plain,
    ( spl4_20
  <=> u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f235,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | spl4_6
    | ~ spl4_10
    | ~ spl4_19
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f214,f234])).

fof(f234,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_2
    | spl4_6
    | ~ spl4_10
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f233,f115])).

fof(f115,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f233,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f232,f75])).

fof(f75,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f232,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_10
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f231,f128])).

fof(f128,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f231,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_20 ),
    inference(superposition,[],[f52,f228])).

fof(f228,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f227])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f214,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_19 ),
    inference(resolution,[],[f180,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f180,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f179])).

fof(f229,plain,
    ( spl4_20
    | ~ spl4_2
    | ~ spl4_10
    | spl4_13
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f205,f156,f146,f127,f74,f227])).

fof(f146,plain,
    ( spl4_13
  <=> u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f156,plain,
    ( spl4_15
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f205,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_10
    | spl4_13
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f136,f183])).

fof(f183,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | spl4_13
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f42,f182])).

fof(f182,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl4_13
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f162,f147])).

fof(f147,plain,
    ( u1_struct_0(sK0) != k6_domain_1(u1_struct_0(sK0),sK1)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f162,plain,
    ( u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_15 ),
    inference(resolution,[],[f157,f46])).

fof(f157,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f42,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f136,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f132,f75])).

fof(f132,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_10 ),
    inference(resolution,[],[f128,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f206,plain,
    ( ~ spl4_6
    | spl4_13
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f183,f156,f146,f104])).

fof(f204,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f202,f71])).

fof(f71,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f202,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f201,f101])).

fof(f101,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_5
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f201,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f200,f128])).

fof(f200,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f199,f75])).

fof(f199,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f189,f196])).

fof(f196,plain,
    ( v7_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f193,f80])).

fof(f80,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f193,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ spl4_12 ),
    inference(resolution,[],[f144,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f144,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_12
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f189,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f105,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | ~ v7_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

fof(f105,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f198,plain,
    ( ~ spl4_3
    | spl4_9
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl4_3
    | spl4_9
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f196,f124])).

fof(f124,plain,
    ( ~ v7_struct_0(sK0)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_9
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f190,plain,
    ( spl4_12
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f188,f159,f143])).

fof(f159,plain,
    ( spl4_16
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f188,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl4_16 ),
    inference(resolution,[],[f160,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f160,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f159])).

fof(f181,plain,
    ( spl4_19
    | ~ spl4_2
    | spl4_6
    | ~ spl4_10
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f177,f174,f127,f104,f74,f179])).

fof(f174,plain,
    ( spl4_18
  <=> m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f177,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | spl4_6
    | ~ spl4_10
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f175,f137])).

fof(f137,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f136,f115])).

fof(f175,plain,
    ( m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f174])).

fof(f176,plain,
    ( spl4_18
    | ~ spl4_2
    | spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f135,f127,f104,f74,f174])).

fof(f135,plain,
    ( m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f134,f115])).

fof(f134,plain,
    ( m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f131,f75])).

fof(f131,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_10 ),
    inference(resolution,[],[f128,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f169,plain,
    ( spl4_17
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f150,f139,f112,f167])).

fof(f167,plain,
    ( spl4_17
  <=> v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f112,plain,
    ( spl4_8
  <=> v7_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f139,plain,
    ( spl4_11
  <=> l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f150,plain,
    ( v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f117,f149])).

fof(f149,plain,
    ( l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_11 ),
    inference(resolution,[],[f140,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f140,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f139])).

fof(f117,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl4_8 ),
    inference(resolution,[],[f113,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f113,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f161,plain,
    ( spl4_15
    | spl4_16
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f91,f83,f159,f156])).

fof(f83,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f91,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(resolution,[],[f84,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f84,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f148,plain,
    ( spl4_12
    | ~ spl4_13
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f98,f83,f146,f143])).

fof(f98,plain,
    ( u1_struct_0(sK0) != k6_domain_1(u1_struct_0(sK0),sK1)
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f90,f66])).

fof(f90,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | u1_struct_0(sK0) != k6_domain_1(u1_struct_0(sK0),sK1)
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f84,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) != X0
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f141,plain,
    ( spl4_11
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f133,f127,f74,f139])).

fof(f133,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f130,f75])).

fof(f130,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f128,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f129,plain,
    ( spl4_10
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f95,f83,f74,f70,f127])).

fof(f95,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f94,f71])).

fof(f94,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f87,f75])).

fof(f87,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f84,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f125,plain,
    ( ~ spl4_9
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f121,f107,f83,f79,f70,f123])).

fof(f107,plain,
    ( spl4_7
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f121,plain,
    ( ~ v7_struct_0(sK0)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f120,f71])).

fof(f120,plain,
    ( v2_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f119,f84])).

fof(f119,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f118,f80])).

fof(f118,plain,
    ( ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f108,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(f108,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f114,plain,
    ( spl4_8
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f97,f83,f74,f70,f112])).

fof(f97,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f96,f71])).

fof(f96,plain,
    ( v2_struct_0(sK0)
    | v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f89,f75])).

fof(f89,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f84,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v7_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

% (13301)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f30,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f109,plain,
    ( spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f41,f107,f104])).

fof(f41,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f102,plain,
    ( ~ spl4_5
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f93,f83,f74,f70,f100])).

fof(f93,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f92,f71])).

fof(f92,plain,
    ( v2_struct_0(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f86,f75])).

fof(f86,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f84,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f43,f83])).

fof(f43,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f77,f74,f79])).

fof(f77,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f75,f65])).

fof(f76,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f45,f74])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f44,f70])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:12:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (13290)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (13309)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.47  % (13290)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (13298)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f269,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f72,f76,f81,f85,f102,f109,f114,f125,f129,f141,f148,f161,f169,f176,f181,f190,f198,f204,f206,f229,f267,f268])).
% 0.21/0.48  fof(f268,plain,(
% 0.21/0.48    u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK0)) | ~v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f267,plain,(
% 0.21/0.48    spl4_27 | ~spl4_2 | spl4_6 | ~spl4_10 | ~spl4_19 | ~spl4_20),
% 0.21/0.48    inference(avatar_split_clause,[],[f235,f227,f179,f127,f104,f74,f265])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    spl4_27 <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl4_2 <=> l1_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl4_6 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    spl4_10 <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    spl4_19 <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    spl4_20 <=> u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | (~spl4_2 | spl4_6 | ~spl4_10 | ~spl4_19 | ~spl4_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f214,f234])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | (~spl4_2 | spl4_6 | ~spl4_10 | ~spl4_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f233,f115])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_2 | ~spl4_10 | ~spl4_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f232,f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    l1_pre_topc(sK0) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_10 | ~spl4_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f231,f128])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl4_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f127])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_20),
% 0.21/0.48    inference(superposition,[],[f52,f228])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | ~spl4_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f227])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~spl4_19),
% 0.21/0.48    inference(resolution,[],[f180,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f179])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    spl4_20 | ~spl4_2 | ~spl4_10 | spl4_13 | ~spl4_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f205,f156,f146,f127,f74,f227])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    spl4_13 <=> u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    spl4_15 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | (~spl4_2 | ~spl4_10 | spl4_13 | ~spl4_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f136,f183])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (spl4_13 | ~spl4_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f42,f182])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (spl4_13 | ~spl4_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f162,f147])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    u1_struct_0(sK0) != k6_domain_1(u1_struct_0(sK0),sK1) | spl4_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f146])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl4_15),
% 0.21/0.48    inference(resolution,[],[f157,f46])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f156])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f14])).
% 0.21/0.48  fof(f14,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_2 | ~spl4_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f132,f75])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_10),
% 0.21/0.48    inference(resolution,[],[f128,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | u1_struct_0(X1) = sK2(X0,X1) | v1_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    ~spl4_6 | spl4_13 | ~spl4_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f183,f156,f146,f104])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    spl4_1 | ~spl4_2 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_10 | ~spl4_12),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f203])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_10 | ~spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f202,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ~v2_struct_0(sK0) | spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl4_1 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_10 | ~spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f201,f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ~v2_struct_0(k1_tex_2(sK0,sK1)) | spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl4_5 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f200,f128])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f199,f75])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | (~spl4_3 | ~spl4_6 | ~spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f189,f196])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    v7_struct_0(sK0) | (~spl4_3 | ~spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f193,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    l1_struct_0(sK0) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl4_3 <=> l1_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    ~l1_struct_0(sK0) | v7_struct_0(sK0) | ~spl4_12),
% 0.21/0.48    inference(resolution,[],[f144,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    v1_zfmisc_1(u1_struct_0(sK0)) | ~spl4_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f143])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    spl4_12 <=> v1_zfmisc_1(u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ~v7_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | ~spl4_6),
% 0.21/0.48    inference(resolution,[],[f105,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | ~v7_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ~spl4_3 | spl4_9 | ~spl4_12),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f197])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    $false | (~spl4_3 | spl4_9 | ~spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f196,f124])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ~v7_struct_0(sK0) | spl4_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f123])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    spl4_9 <=> v7_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    spl4_12 | ~spl4_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f188,f159,f143])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    spl4_16 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    v1_zfmisc_1(u1_struct_0(sK0)) | ~spl4_16),
% 0.21/0.48    inference(resolution,[],[f160,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | v1_zfmisc_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f159])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    spl4_19 | ~spl4_2 | spl4_6 | ~spl4_10 | ~spl4_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f177,f174,f127,f104,f74,f179])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    spl4_18 <=> m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | spl4_6 | ~spl4_10 | ~spl4_18)),
% 0.21/0.48    inference(forward_demodulation,[],[f175,f137])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | (~spl4_2 | spl4_6 | ~spl4_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f136,f115])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f174])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    spl4_18 | ~spl4_2 | spl4_6 | ~spl4_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f135,f127,f104,f74,f174])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | spl4_6 | ~spl4_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f134,f115])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_2 | ~spl4_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f131,f75])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_10),
% 0.21/0.48    inference(resolution,[],[f128,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    spl4_17 | ~spl4_8 | ~spl4_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f150,f139,f112,f167])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    spl4_17 <=> v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    spl4_8 <=> v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    spl4_11 <=> l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) | (~spl4_8 | ~spl4_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f117,f149])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    l1_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_11),
% 0.21/0.48    inference(resolution,[],[f140,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    l1_pre_topc(k1_tex_2(sK0,sK1)) | ~spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f139])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ~l1_struct_0(k1_tex_2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl4_8),
% 0.21/0.48    inference(resolution,[],[f113,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    v7_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f112])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    spl4_15 | spl4_16 | ~spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f91,f83,f159,f156])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl4_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK0)) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_4),
% 0.21/0.48    inference(resolution,[],[f84,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    spl4_12 | ~spl4_13 | ~spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f98,f83,f146,f143])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    u1_struct_0(sK0) != k6_domain_1(u1_struct_0(sK0),sK1) | v1_zfmisc_1(u1_struct_0(sK0)) | ~spl4_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f90,f66])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK0)) | u1_struct_0(sK0) != k6_domain_1(u1_struct_0(sK0),sK1) | v1_zfmisc_1(u1_struct_0(sK0)) | ~spl4_4),
% 0.21/0.48    inference(resolution,[],[f84,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) != X0 | v1_zfmisc_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    spl4_11 | ~spl4_2 | ~spl4_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f133,f127,f74,f139])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    l1_pre_topc(k1_tex_2(sK0,sK1)) | (~spl4_2 | ~spl4_10)),
% 0.21/0.49    inference(subsumption_resolution,[],[f130,f75])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | l1_pre_topc(k1_tex_2(sK0,sK1)) | ~spl4_10),
% 0.21/0.49    inference(resolution,[],[f128,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    spl4_10 | spl4_1 | ~spl4_2 | ~spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f95,f83,f74,f70,f127])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f94,f71])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (~spl4_2 | ~spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f87,f75])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl4_4),
% 0.21/0.49    inference(resolution,[],[f84,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ~spl4_9 | spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f121,f107,f83,f79,f70,f123])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl4_7 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ~v7_struct_0(sK0) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f120,f71])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~v7_struct_0(sK0) | (~spl4_3 | ~spl4_4 | ~spl4_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f119,f84])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v7_struct_0(sK0) | (~spl4_3 | ~spl4_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f118,f80])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ~l1_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v7_struct_0(sK0) | ~spl4_7),
% 0.21/0.49    inference(resolution,[],[f108,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl4_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f107])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl4_8 | spl4_1 | ~spl4_2 | ~spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f97,f83,f74,f70,f112])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    v7_struct_0(k1_tex_2(sK0,sK1)) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f96,f71])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    v2_struct_0(sK0) | v7_struct_0(k1_tex_2(sK0,sK1)) | (~spl4_2 | ~spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f89,f75])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v7_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_4),
% 0.21/0.49    inference(resolution,[],[f84,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v7_struct_0(k1_tex_2(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  % (13301)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    spl4_6 | spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f41,f107,f104])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ~spl4_5 | spl4_1 | ~spl4_2 | ~spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f93,f83,f74,f70,f100])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ~v2_struct_0(k1_tex_2(sK0,sK1)) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f92,f71])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK1)) | (~spl4_2 | ~spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f86,f75])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_4),
% 0.21/0.49    inference(resolution,[],[f84,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_struct_0(k1_tex_2(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f43,f83])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl4_3 | ~spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f77,f74,f79])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    l1_struct_0(sK0) | ~spl4_2),
% 0.21/0.49    inference(resolution,[],[f75,f65])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f74])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ~spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f44,f70])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (13290)------------------------------
% 0.21/0.49  % (13290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13290)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (13290)Memory used [KB]: 6268
% 0.21/0.49  % (13290)Time elapsed: 0.069 s
% 0.21/0.49  % (13290)------------------------------
% 0.21/0.49  % (13290)------------------------------
% 0.21/0.50  % (13293)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (13289)Success in time 0.137 s
%------------------------------------------------------------------------------
