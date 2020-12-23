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
% DateTime   : Thu Dec  3 13:21:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 405 expanded)
%              Number of leaves         :   45 ( 183 expanded)
%              Depth                    :   12
%              Number of atoms          :  698 (1829 expanded)
%              Number of equality atoms :   30 (  55 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f629,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f97,f102,f107,f112,f117,f122,f127,f142,f192,f205,f224,f319,f325,f326,f401,f407,f485,f508,f510,f519,f553,f570,f624,f627,f628])).

fof(f628,plain,
    ( sK1 != k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | v2_tex_2(sK1,sK0)
    | ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f627,plain,
    ( spl5_48
    | spl5_17
    | ~ spl5_22
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f626,f398,f268,f227,f616])).

fof(f616,plain,
    ( spl5_48
  <=> sK1 = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f227,plain,
    ( spl5_17
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f268,plain,
    ( spl5_22
  <=> sK1 = k1_tarski(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f398,plain,
    ( spl5_35
  <=> m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f626,plain,
    ( sK1 = k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | spl5_17
    | ~ spl5_22
    | ~ spl5_35 ),
    inference(forward_demodulation,[],[f625,f270])).

fof(f270,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f268])).

fof(f625,plain,
    ( k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | spl5_17
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f613,f228])).

fof(f228,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f227])).

fof(f613,plain,
    ( k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_35 ),
    inference(resolution,[],[f400,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f400,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f398])).

fof(f624,plain,
    ( spl5_49
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f610,f398,f124,f119,f109,f621])).

fof(f621,plain,
    ( spl5_49
  <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f109,plain,
    ( spl5_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f119,plain,
    ( spl5_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f124,plain,
    ( spl5_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f610,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8
    | ~ spl5_35 ),
    inference(unit_resulting_resolution,[],[f126,f121,f111,f400,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f111,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f121,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f126,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f570,plain,
    ( spl5_22
    | ~ spl5_2
    | spl5_4
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f569,f189,f104,f93,f268])).

fof(f93,plain,
    ( spl5_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f104,plain,
    ( spl5_4
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f189,plain,
    ( spl5_12
  <=> r1_tarski(k1_tarski(sK3(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f569,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | ~ spl5_2
    | spl5_4
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f568,f64])).

fof(f64,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f568,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | v1_xboole_0(k1_tarski(sK3(sK1)))
    | ~ spl5_2
    | spl5_4
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f567,f106])).

fof(f106,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f567,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | v1_xboole_0(sK1)
    | v1_xboole_0(k1_tarski(sK3(sK1)))
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f564,f94])).

fof(f94,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f564,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | v1_xboole_0(k1_tarski(sK3(sK1)))
    | ~ spl5_12 ),
    inference(resolution,[],[f191,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f191,plain,
    ( r1_tarski(k1_tarski(sK3(sK1)),sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f189])).

fof(f553,plain,
    ( spl5_43
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f541,f356,f482])).

fof(f482,plain,
    ( spl5_43
  <=> l1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f356,plain,
    ( spl5_29
  <=> l1_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f541,plain,
    ( l1_struct_0(sK2(sK0,sK1))
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f357,f66])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f357,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f356])).

fof(f519,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8
    | spl5_27 ),
    inference(avatar_split_clause,[],[f387,f321,f124,f119,f109,f104,f99,f89])).

fof(f89,plain,
    ( spl5_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f99,plain,
    ( spl5_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f321,plain,
    ( spl5_27
  <=> m1_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f387,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8
    | spl5_27 ),
    inference(unit_resulting_resolution,[],[f126,f121,f111,f106,f101,f322,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & v1_tdlat_3(sK2(X0,X1))
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & v1_tdlat_3(sK2(X0,X1))
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

fof(f322,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | spl5_27 ),
    inference(avatar_component_clause,[],[f321])).

fof(f101,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f510,plain,
    ( spl5_29
    | ~ spl5_5
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f509,f321,f109,f356])).

fof(f509,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl5_5
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f499,f111])).

fof(f499,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_27 ),
    inference(resolution,[],[f323,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f323,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f321])).

fof(f508,plain,
    ( spl5_42
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_8
    | ~ spl5_25
    | spl5_26
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f507,f321,f304,f295,f124,f119,f114,f109,f478])).

fof(f478,plain,
    ( spl5_42
  <=> v7_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f114,plain,
    ( spl5_6
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f295,plain,
    ( spl5_25
  <=> v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f304,plain,
    ( spl5_26
  <=> v2_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f507,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_8
    | ~ spl5_25
    | spl5_26
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f506,f126])).

fof(f506,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_25
    | spl5_26
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f505,f121])).

fof(f505,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_25
    | spl5_26
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f504,f116])).

fof(f116,plain,
    ( v2_tdlat_3(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f114])).

fof(f504,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5
    | ~ spl5_25
    | spl5_26
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f503,f111])).

fof(f503,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_25
    | spl5_26
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f502,f306])).

fof(f306,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f304])).

fof(f502,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_25
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f498,f297])).

fof(f297,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f295])).

fof(f498,plain,
    ( ~ v1_tdlat_3(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_27 ),
    inference(resolution,[],[f323,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( ~ v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).

fof(f485,plain,
    ( ~ spl5_42
    | ~ spl5_43
    | spl5_2
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f349,f286,f93,f482,f478])).

fof(f286,plain,
    ( spl5_24
  <=> sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f349,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1))
    | ~ spl5_24 ),
    inference(superposition,[],[f76,f288])).

fof(f288,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f286])).

fof(f76,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f407,plain,
    ( ~ spl5_17
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f395,f221,f227])).

fof(f221,plain,
    ( spl5_16
  <=> r2_hidden(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f395,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_16 ),
    inference(resolution,[],[f223,f77])).

fof(f77,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f223,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f221])).

fof(f401,plain,
    ( spl5_35
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f390,f221,f398])).

fof(f390,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f223,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f326,plain,
    ( ~ spl5_26
    | ~ spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f311,f124,f119,f109,f104,f99,f89,f304])).

fof(f311,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f126,f121,f111,f106,f101,f90,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f325,plain,
    ( spl5_25
    | ~ spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f312,f124,f119,f109,f104,f99,f89,f295])).

fof(f312,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f126,f121,f111,f106,f101,f90,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f319,plain,
    ( spl5_24
    | ~ spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f314,f124,f119,f109,f104,f99,f89,f286])).

fof(f314,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f126,f121,f111,f106,f101,f90,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f224,plain,
    ( spl5_16
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f216,f201,f139,f221])).

fof(f139,plain,
    ( spl5_9
  <=> r2_hidden(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f201,plain,
    ( spl5_13
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f216,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f141,f203,f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f203,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f201])).

fof(f141,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f205,plain,
    ( spl5_13
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f198,f99,f201])).

fof(f198,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(resolution,[],[f101,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f192,plain,
    ( spl5_12
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f176,f139,f189])).

fof(f176,plain,
    ( r1_tarski(k1_tarski(sK3(sK1)),sK1)
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f141,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f142,plain,
    ( spl5_9
    | spl5_4 ),
    inference(avatar_split_clause,[],[f129,f104,f139])).

fof(f129,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f106,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f127,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f56,f124])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v2_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

% (26226)Refutation not found, incomplete strategy% (26226)------------------------------
% (26226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26226)Termination reason: Refutation not found, incomplete strategy

% (26226)Memory used [KB]: 10618
% (26226)Time elapsed: 0.130 s
% (26226)------------------------------
% (26226)------------------------------
fof(f42,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v2_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v2_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v2_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f122,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f57,f119])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f117,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f58,f114])).

fof(f58,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f112,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f59,f109])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f107,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f60,f104])).

fof(f60,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f102,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f61,f99])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f62,f93,f89])).

fof(f62,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f63,f93,f89])).

fof(f63,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (26224)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (26215)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (26240)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.51  % (26230)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (26232)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.51  % (26222)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (26237)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (26220)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (26219)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (26223)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (26225)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (26218)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (26229)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (26237)Refutation not found, incomplete strategy% (26237)------------------------------
% 0.22/0.53  % (26237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (26237)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (26237)Memory used [KB]: 10746
% 0.22/0.53  % (26237)Time elapsed: 0.072 s
% 0.22/0.53  % (26237)------------------------------
% 0.22/0.53  % (26237)------------------------------
% 0.22/0.53  % (26221)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (26236)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (26240)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (26217)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (26217)Refutation not found, incomplete strategy% (26217)------------------------------
% 0.22/0.53  % (26217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (26228)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (26217)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (26217)Memory used [KB]: 10746
% 0.22/0.53  % (26217)Time elapsed: 0.126 s
% 0.22/0.53  % (26217)------------------------------
% 0.22/0.53  % (26217)------------------------------
% 0.22/0.53  % (26225)Refutation not found, incomplete strategy% (26225)------------------------------
% 0.22/0.53  % (26225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (26225)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.54  % (26225)Memory used [KB]: 10618
% 0.22/0.54  % (26225)Time elapsed: 0.126 s
% 0.22/0.54  % (26225)------------------------------
% 0.22/0.54  % (26225)------------------------------
% 0.22/0.54  % (26244)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (26226)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (26243)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (26216)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (26238)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (26242)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (26223)Refutation not found, incomplete strategy% (26223)------------------------------
% 0.22/0.54  % (26223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26223)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (26223)Memory used [KB]: 10746
% 0.22/0.54  % (26223)Time elapsed: 0.108 s
% 0.22/0.54  % (26223)------------------------------
% 0.22/0.54  % (26223)------------------------------
% 0.22/0.54  % (26233)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (26235)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (26241)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (26239)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (26227)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (26231)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (26234)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f629,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f96,f97,f102,f107,f112,f117,f122,f127,f142,f192,f205,f224,f319,f325,f326,f401,f407,f485,f508,f510,f519,f553,f570,f624,f627,f628])).
% 0.22/0.56  fof(f628,plain,(
% 0.22/0.56    sK1 != k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | v2_tex_2(sK1,sK0) | ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)),
% 0.22/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.56  fof(f627,plain,(
% 0.22/0.56    spl5_48 | spl5_17 | ~spl5_22 | ~spl5_35),
% 0.22/0.56    inference(avatar_split_clause,[],[f626,f398,f268,f227,f616])).
% 0.22/0.56  fof(f616,plain,(
% 0.22/0.56    spl5_48 <=> sK1 = k6_domain_1(u1_struct_0(sK0),sK3(sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 0.22/0.56  fof(f227,plain,(
% 0.22/0.56    spl5_17 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.56  fof(f268,plain,(
% 0.22/0.56    spl5_22 <=> sK1 = k1_tarski(sK3(sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.22/0.56  fof(f398,plain,(
% 0.22/0.56    spl5_35 <=> m1_subset_1(sK3(sK1),u1_struct_0(sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.22/0.56  fof(f626,plain,(
% 0.22/0.56    sK1 = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | (spl5_17 | ~spl5_22 | ~spl5_35)),
% 0.22/0.56    inference(forward_demodulation,[],[f625,f270])).
% 0.22/0.56  fof(f270,plain,(
% 0.22/0.56    sK1 = k1_tarski(sK3(sK1)) | ~spl5_22),
% 0.22/0.56    inference(avatar_component_clause,[],[f268])).
% 0.22/0.56  fof(f625,plain,(
% 0.22/0.56    k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | (spl5_17 | ~spl5_35)),
% 0.22/0.56    inference(subsumption_resolution,[],[f613,f228])).
% 0.22/0.56  fof(f228,plain,(
% 0.22/0.56    ~v1_xboole_0(u1_struct_0(sK0)) | spl5_17),
% 0.22/0.56    inference(avatar_component_clause,[],[f227])).
% 0.22/0.56  fof(f613,plain,(
% 0.22/0.56    k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_35),
% 0.22/0.56    inference(resolution,[],[f400,f80])).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.56    inference(flattening,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.56  fof(f400,plain,(
% 0.22/0.56    m1_subset_1(sK3(sK1),u1_struct_0(sK0)) | ~spl5_35),
% 0.22/0.56    inference(avatar_component_clause,[],[f398])).
% 0.22/0.56  fof(f624,plain,(
% 0.22/0.56    spl5_49 | ~spl5_5 | ~spl5_7 | spl5_8 | ~spl5_35),
% 0.22/0.56    inference(avatar_split_clause,[],[f610,f398,f124,f119,f109,f621])).
% 0.22/0.56  fof(f621,plain,(
% 0.22/0.56    spl5_49 <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    spl5_5 <=> l1_pre_topc(sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.56  fof(f119,plain,(
% 0.22/0.56    spl5_7 <=> v2_pre_topc(sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.56  fof(f124,plain,(
% 0.22/0.56    spl5_8 <=> v2_struct_0(sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.56  fof(f610,plain,(
% 0.22/0.56    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0) | (~spl5_5 | ~spl5_7 | spl5_8 | ~spl5_35)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f126,f121,f111,f400,f71])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    l1_pre_topc(sK0) | ~spl5_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f109])).
% 0.22/0.56  fof(f121,plain,(
% 0.22/0.56    v2_pre_topc(sK0) | ~spl5_7),
% 0.22/0.56    inference(avatar_component_clause,[],[f119])).
% 0.22/0.56  fof(f126,plain,(
% 0.22/0.56    ~v2_struct_0(sK0) | spl5_8),
% 0.22/0.56    inference(avatar_component_clause,[],[f124])).
% 0.22/0.56  fof(f570,plain,(
% 0.22/0.56    spl5_22 | ~spl5_2 | spl5_4 | ~spl5_12),
% 0.22/0.56    inference(avatar_split_clause,[],[f569,f189,f104,f93,f268])).
% 0.22/0.56  fof(f93,plain,(
% 0.22/0.56    spl5_2 <=> v1_zfmisc_1(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    spl5_4 <=> v1_xboole_0(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.56  fof(f189,plain,(
% 0.22/0.56    spl5_12 <=> r1_tarski(k1_tarski(sK3(sK1)),sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.56  fof(f569,plain,(
% 0.22/0.56    sK1 = k1_tarski(sK3(sK1)) | (~spl5_2 | spl5_4 | ~spl5_12)),
% 0.22/0.56    inference(subsumption_resolution,[],[f568,f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.22/0.56  fof(f568,plain,(
% 0.22/0.56    sK1 = k1_tarski(sK3(sK1)) | v1_xboole_0(k1_tarski(sK3(sK1))) | (~spl5_2 | spl5_4 | ~spl5_12)),
% 0.22/0.56    inference(subsumption_resolution,[],[f567,f106])).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    ~v1_xboole_0(sK1) | spl5_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f104])).
% 0.22/0.56  fof(f567,plain,(
% 0.22/0.56    sK1 = k1_tarski(sK3(sK1)) | v1_xboole_0(sK1) | v1_xboole_0(k1_tarski(sK3(sK1))) | (~spl5_2 | ~spl5_12)),
% 0.22/0.56    inference(subsumption_resolution,[],[f564,f94])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    v1_zfmisc_1(sK1) | ~spl5_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f93])).
% 0.22/0.56  fof(f564,plain,(
% 0.22/0.56    sK1 = k1_tarski(sK3(sK1)) | ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | v1_xboole_0(k1_tarski(sK3(sK1))) | ~spl5_12),
% 0.22/0.56    inference(resolution,[],[f191,f65])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.56    inference(flattening,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.22/0.56  fof(f191,plain,(
% 0.22/0.56    r1_tarski(k1_tarski(sK3(sK1)),sK1) | ~spl5_12),
% 0.22/0.56    inference(avatar_component_clause,[],[f189])).
% 0.22/0.56  fof(f553,plain,(
% 0.22/0.56    spl5_43 | ~spl5_29),
% 0.22/0.56    inference(avatar_split_clause,[],[f541,f356,f482])).
% 0.22/0.56  fof(f482,plain,(
% 0.22/0.56    spl5_43 <=> l1_struct_0(sK2(sK0,sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 0.22/0.56  fof(f356,plain,(
% 0.22/0.56    spl5_29 <=> l1_pre_topc(sK2(sK0,sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.22/0.56  fof(f541,plain,(
% 0.22/0.56    l1_struct_0(sK2(sK0,sK1)) | ~spl5_29),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f357,f66])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.56  fof(f357,plain,(
% 0.22/0.56    l1_pre_topc(sK2(sK0,sK1)) | ~spl5_29),
% 0.22/0.56    inference(avatar_component_clause,[],[f356])).
% 0.22/0.56  fof(f519,plain,(
% 0.22/0.56    ~spl5_1 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_7 | spl5_8 | spl5_27),
% 0.22/0.56    inference(avatar_split_clause,[],[f387,f321,f124,f119,f109,f104,f99,f89])).
% 0.22/0.56  fof(f89,plain,(
% 0.22/0.56    spl5_1 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    spl5_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.56  fof(f321,plain,(
% 0.22/0.56    spl5_27 <=> m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.22/0.56  fof(f387,plain,(
% 0.22/0.56    ~v2_tex_2(sK1,sK0) | (~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_7 | spl5_8 | spl5_27)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f126,f121,f111,f106,f101,f322,f74])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.22/0.56    inference(pure_predicate_removal,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).
% 0.22/0.56  fof(f322,plain,(
% 0.22/0.56    ~m1_pre_topc(sK2(sK0,sK1),sK0) | spl5_27),
% 0.22/0.56    inference(avatar_component_clause,[],[f321])).
% 0.22/0.56  fof(f101,plain,(
% 0.22/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f99])).
% 0.22/0.56  fof(f510,plain,(
% 0.22/0.56    spl5_29 | ~spl5_5 | ~spl5_27),
% 0.22/0.56    inference(avatar_split_clause,[],[f509,f321,f109,f356])).
% 0.22/0.56  fof(f509,plain,(
% 0.22/0.56    l1_pre_topc(sK2(sK0,sK1)) | (~spl5_5 | ~spl5_27)),
% 0.22/0.56    inference(subsumption_resolution,[],[f499,f111])).
% 0.22/0.56  fof(f499,plain,(
% 0.22/0.56    l1_pre_topc(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl5_27),
% 0.22/0.56    inference(resolution,[],[f323,f68])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.56  fof(f323,plain,(
% 0.22/0.56    m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl5_27),
% 0.22/0.56    inference(avatar_component_clause,[],[f321])).
% 0.22/0.56  fof(f508,plain,(
% 0.22/0.56    spl5_42 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_8 | ~spl5_25 | spl5_26 | ~spl5_27),
% 0.22/0.56    inference(avatar_split_clause,[],[f507,f321,f304,f295,f124,f119,f114,f109,f478])).
% 0.22/0.56  fof(f478,plain,(
% 0.22/0.56    spl5_42 <=> v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.22/0.56  fof(f114,plain,(
% 0.22/0.56    spl5_6 <=> v2_tdlat_3(sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.56  fof(f295,plain,(
% 0.22/0.56    spl5_25 <=> v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.22/0.56  fof(f304,plain,(
% 0.22/0.56    spl5_26 <=> v2_struct_0(sK2(sK0,sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.22/0.56  fof(f507,plain,(
% 0.22/0.56    v7_struct_0(sK2(sK0,sK1)) | (~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_8 | ~spl5_25 | spl5_26 | ~spl5_27)),
% 0.22/0.56    inference(subsumption_resolution,[],[f506,f126])).
% 0.22/0.56  fof(f506,plain,(
% 0.22/0.56    v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK0) | (~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_25 | spl5_26 | ~spl5_27)),
% 0.22/0.56    inference(subsumption_resolution,[],[f505,f121])).
% 0.22/0.56  fof(f505,plain,(
% 0.22/0.56    v7_struct_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_5 | ~spl5_6 | ~spl5_25 | spl5_26 | ~spl5_27)),
% 0.22/0.56    inference(subsumption_resolution,[],[f504,f116])).
% 0.22/0.56  fof(f116,plain,(
% 0.22/0.56    v2_tdlat_3(sK0) | ~spl5_6),
% 0.22/0.56    inference(avatar_component_clause,[],[f114])).
% 0.22/0.56  fof(f504,plain,(
% 0.22/0.56    v7_struct_0(sK2(sK0,sK1)) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_5 | ~spl5_25 | spl5_26 | ~spl5_27)),
% 0.22/0.56    inference(subsumption_resolution,[],[f503,f111])).
% 0.22/0.56  fof(f503,plain,(
% 0.22/0.56    v7_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_25 | spl5_26 | ~spl5_27)),
% 0.22/0.56    inference(subsumption_resolution,[],[f502,f306])).
% 0.22/0.56  fof(f306,plain,(
% 0.22/0.56    ~v2_struct_0(sK2(sK0,sK1)) | spl5_26),
% 0.22/0.56    inference(avatar_component_clause,[],[f304])).
% 0.22/0.56  fof(f502,plain,(
% 0.22/0.56    v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_25 | ~spl5_27)),
% 0.22/0.56    inference(subsumption_resolution,[],[f498,f297])).
% 0.22/0.56  fof(f297,plain,(
% 0.22/0.56    v1_tdlat_3(sK2(sK0,sK1)) | ~spl5_25),
% 0.22/0.56    inference(avatar_component_clause,[],[f295])).
% 0.22/0.56  fof(f498,plain,(
% 0.22/0.56    ~v1_tdlat_3(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_27),
% 0.22/0.56    inference(resolution,[],[f323,f70])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).
% 0.22/0.56  fof(f485,plain,(
% 0.22/0.56    ~spl5_42 | ~spl5_43 | spl5_2 | ~spl5_24),
% 0.22/0.56    inference(avatar_split_clause,[],[f349,f286,f93,f482,f478])).
% 0.22/0.56  fof(f286,plain,(
% 0.22/0.56    spl5_24 <=> sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.56  fof(f349,plain,(
% 0.22/0.56    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | ~spl5_24),
% 0.22/0.56    inference(superposition,[],[f76,f288])).
% 0.22/0.56  fof(f288,plain,(
% 0.22/0.56    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl5_24),
% 0.22/0.56    inference(avatar_component_clause,[],[f286])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.22/0.56  fof(f407,plain,(
% 0.22/0.56    ~spl5_17 | ~spl5_16),
% 0.22/0.56    inference(avatar_split_clause,[],[f395,f221,f227])).
% 0.22/0.56  fof(f221,plain,(
% 0.22/0.56    spl5_16 <=> r2_hidden(sK3(sK1),u1_struct_0(sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.56  fof(f395,plain,(
% 0.22/0.56    ~v1_xboole_0(u1_struct_0(sK0)) | ~spl5_16),
% 0.22/0.56    inference(resolution,[],[f223,f77])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.56    inference(rectify,[],[f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.56    inference(nnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.56  fof(f223,plain,(
% 0.22/0.56    r2_hidden(sK3(sK1),u1_struct_0(sK0)) | ~spl5_16),
% 0.22/0.56    inference(avatar_component_clause,[],[f221])).
% 0.22/0.56  fof(f401,plain,(
% 0.22/0.56    spl5_35 | ~spl5_16),
% 0.22/0.56    inference(avatar_split_clause,[],[f390,f221,f398])).
% 0.22/0.56  fof(f390,plain,(
% 0.22/0.56    m1_subset_1(sK3(sK1),u1_struct_0(sK0)) | ~spl5_16),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f223,f79])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.56  fof(f326,plain,(
% 0.22/0.56    ~spl5_26 | ~spl5_1 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_7 | spl5_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f311,f124,f119,f109,f104,f99,f89,f304])).
% 0.22/0.56  fof(f311,plain,(
% 0.22/0.56    ~v2_struct_0(sK2(sK0,sK1)) | (~spl5_1 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_7 | spl5_8)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f126,f121,f111,f106,f101,f90,f72])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f45])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    v2_tex_2(sK1,sK0) | ~spl5_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f89])).
% 0.22/0.56  fof(f325,plain,(
% 0.22/0.56    spl5_25 | ~spl5_1 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_7 | spl5_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f312,f124,f119,f109,f104,f99,f89,f295])).
% 0.22/0.56  fof(f312,plain,(
% 0.22/0.56    v1_tdlat_3(sK2(sK0,sK1)) | (~spl5_1 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_7 | spl5_8)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f126,f121,f111,f106,f101,f90,f73])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v1_tdlat_3(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f45])).
% 0.22/0.56  fof(f319,plain,(
% 0.22/0.56    spl5_24 | ~spl5_1 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_7 | spl5_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f314,f124,f119,f109,f104,f99,f89,f286])).
% 0.22/0.56  fof(f314,plain,(
% 0.22/0.56    sK1 = u1_struct_0(sK2(sK0,sK1)) | (~spl5_1 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_7 | spl5_8)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f126,f121,f111,f106,f101,f90,f75])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f45])).
% 0.22/0.56  fof(f224,plain,(
% 0.22/0.56    spl5_16 | ~spl5_9 | ~spl5_13),
% 0.22/0.56    inference(avatar_split_clause,[],[f216,f201,f139,f221])).
% 0.22/0.56  fof(f139,plain,(
% 0.22/0.56    spl5_9 <=> r2_hidden(sK3(sK1),sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.56  fof(f201,plain,(
% 0.22/0.56    spl5_13 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.56  fof(f216,plain,(
% 0.22/0.56    r2_hidden(sK3(sK1),u1_struct_0(sK0)) | (~spl5_9 | ~spl5_13)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f141,f203,f81])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(rectify,[],[f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.56  fof(f203,plain,(
% 0.22/0.56    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl5_13),
% 0.22/0.56    inference(avatar_component_clause,[],[f201])).
% 0.22/0.56  fof(f141,plain,(
% 0.22/0.56    r2_hidden(sK3(sK1),sK1) | ~spl5_9),
% 0.22/0.56    inference(avatar_component_clause,[],[f139])).
% 0.22/0.56  fof(f205,plain,(
% 0.22/0.56    spl5_13 | ~spl5_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f198,f99,f201])).
% 0.22/0.56  fof(f198,plain,(
% 0.22/0.56    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl5_3),
% 0.22/0.56    inference(resolution,[],[f101,f86])).
% 0.22/0.56  fof(f86,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.56    inference(nnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.56  fof(f192,plain,(
% 0.22/0.56    spl5_12 | ~spl5_9),
% 0.22/0.56    inference(avatar_split_clause,[],[f176,f139,f189])).
% 0.22/0.56  fof(f176,plain,(
% 0.22/0.56    r1_tarski(k1_tarski(sK3(sK1)),sK1) | ~spl5_9),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f141,f85])).
% 0.22/0.56  fof(f85,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.56  fof(f142,plain,(
% 0.22/0.56    spl5_9 | spl5_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f129,f104,f139])).
% 0.22/0.56  fof(f129,plain,(
% 0.22/0.56    r2_hidden(sK3(sK1),sK1) | spl5_4),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f106,f78])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f49])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    ~spl5_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f56,f124])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ~v2_struct_0(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  % (26226)Refutation not found, incomplete strategy% (26226)------------------------------
% 0.22/0.56  % (26226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (26226)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (26226)Memory used [KB]: 10618
% 0.22/0.56  % (26226)Time elapsed: 0.130 s
% 0.22/0.56  % (26226)------------------------------
% 0.22/0.56  % (26226)------------------------------
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.56    inference(nnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,negated_conjecture,(
% 0.22/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.56    inference(negated_conjecture,[],[f16])).
% 0.22/0.56  fof(f16,conjecture,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    spl5_7),
% 0.22/0.56    inference(avatar_split_clause,[],[f57,f119])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    v2_pre_topc(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f43])).
% 0.22/0.56  fof(f117,plain,(
% 0.22/0.56    spl5_6),
% 0.22/0.56    inference(avatar_split_clause,[],[f58,f114])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    v2_tdlat_3(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f43])).
% 0.22/0.56  fof(f112,plain,(
% 0.22/0.56    spl5_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f59,f109])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    l1_pre_topc(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f43])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    ~spl5_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f60,f104])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ~v1_xboole_0(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f43])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    spl5_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f61,f99])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    inference(cnf_transformation,[],[f43])).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    spl5_1 | spl5_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f62,f93,f89])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f43])).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    ~spl5_1 | ~spl5_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f63,f93,f89])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f43])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (26240)------------------------------
% 0.22/0.56  % (26240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (26240)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (26240)Memory used [KB]: 6524
% 0.22/0.56  % (26240)Time elapsed: 0.124 s
% 0.22/0.56  % (26240)------------------------------
% 0.22/0.56  % (26240)------------------------------
% 0.22/0.56  % (26214)Success in time 0.2 s
%------------------------------------------------------------------------------
