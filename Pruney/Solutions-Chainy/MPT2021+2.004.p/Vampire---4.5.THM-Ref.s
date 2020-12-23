%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:05 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 257 expanded)
%              Number of leaves         :   33 ( 125 expanded)
%              Depth                    :    8
%              Number of atoms          :  376 (1188 expanded)
%              Number of equality atoms :   57 ( 264 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f442,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f65,f70,f75,f80,f102,f108,f114,f134,f147,f177,f190,f276,f277,f310,f337,f349,f440,f441])).

fof(f441,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK1)
    | ~ r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK2),u1_pre_topc(sK0))
    | r1_tarski(k7_setfam_1(u1_struct_0(sK1),sK2),u1_pre_topc(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f440,plain,
    ( spl4_37
    | ~ spl4_44
    | ~ spl4_7
    | ~ spl4_19
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f439,f232,f174,f72,f434,f346])).

fof(f346,plain,
    ( spl4_37
  <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f434,plain,
    ( spl4_44
  <=> r1_tarski(k7_setfam_1(u1_struct_0(sK1),sK2),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f72,plain,
    ( spl4_7
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f174,plain,
    ( spl4_19
  <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f232,plain,
    ( spl4_25
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f439,plain,
    ( ~ r1_tarski(k7_setfam_1(u1_struct_0(sK1),sK2),u1_pre_topc(sK0))
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK2),sK1)
    | ~ spl4_7
    | ~ spl4_19
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f438,f234])).

fof(f234,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f232])).

fof(f438,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK2),sK1)
    | ~ r1_tarski(k7_setfam_1(u1_struct_0(sK1),sK2),u1_pre_topc(sK1))
    | ~ spl4_7
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f425,f74])).

fof(f74,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f425,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK2),sK1)
    | ~ r1_tarski(k7_setfam_1(u1_struct_0(sK1),sK2),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_19 ),
    inference(resolution,[],[f176,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(f176,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f174])).

fof(f349,plain,
    ( ~ spl4_19
    | ~ spl4_37
    | ~ spl4_7
    | spl4_11
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f344,f169,f105,f72,f346,f174])).

fof(f105,plain,
    ( spl4_11
  <=> v2_tops_2(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f169,plain,
    ( spl4_18
  <=> sK2 = k7_setfam_1(u1_struct_0(sK1),k7_setfam_1(u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f344,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl4_7
    | spl4_11
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f343,f74])).

fof(f343,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | spl4_11
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f340,f107])).

fof(f107,plain,
    ( ~ v2_tops_2(sK2,sK1)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f340,plain,
    ( v2_tops_2(sK2,sK1)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_18 ),
    inference(superposition,[],[f35,f171])).

fof(f171,plain,
    ( sK2 = k7_setfam_1(u1_struct_0(sK1),k7_setfam_1(u1_struct_0(sK1),sK2))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f169])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
            & ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tops_2)).

fof(f337,plain,
    ( ~ spl4_34
    | spl4_36
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f332,f131,f77,f334,f307])).

fof(f307,plain,
    ( spl4_34
  <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f334,plain,
    ( spl4_36
  <=> r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK2),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f77,plain,
    ( spl4_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f131,plain,
    ( spl4_14
  <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f332,plain,
    ( r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK2),u1_pre_topc(sK0))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0)
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f325,f79])).

fof(f79,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f325,plain,
    ( r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK2),u1_pre_topc(sK0))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_14 ),
    inference(resolution,[],[f133,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f133,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f131])).

fof(f310,plain,
    ( ~ spl4_14
    | spl4_34
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f305,f126,f77,f47,f307,f131])).

fof(f47,plain,
    ( spl4_2
  <=> v2_tops_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f126,plain,
    ( spl4_13
  <=> sK2 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f305,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f304,f79])).

fof(f304,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_2
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f302,f49])).

fof(f49,plain,
    ( v2_tops_2(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f302,plain,
    ( ~ v2_tops_2(sK2,sK0)
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_13 ),
    inference(superposition,[],[f36,f128])).

fof(f128,plain,
    ( sK2 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK2))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f277,plain,
    ( spl4_26
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f254,f99,f57,f237])).

fof(f237,plain,
    ( spl4_26
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f57,plain,
    ( spl4_4
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f99,plain,
    ( spl4_10
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f254,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f59,f101,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f101,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f59,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f276,plain,
    ( spl4_25
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f255,f99,f57,f232])).

fof(f255,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f59,f101,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f190,plain,
    ( spl4_18
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f167,f111,f169])).

fof(f111,plain,
    ( spl4_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f167,plain,
    ( sK2 = k7_setfam_1(u1_struct_0(sK1),k7_setfam_1(u1_struct_0(sK1),sK2))
    | ~ spl4_12 ),
    inference(resolution,[],[f113,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f113,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f177,plain,
    ( spl4_19
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f158,f111,f174])).

fof(f158,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f113,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f147,plain,
    ( spl4_13
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f124,f67,f126])).

fof(f67,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f124,plain,
    ( sK2 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK2))
    | ~ spl4_6 ),
    inference(resolution,[],[f69,f37])).

fof(f69,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f134,plain,
    ( spl4_14
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f115,f67,f131])).

fof(f115,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f69,f38])).

fof(f114,plain,
    ( spl4_12
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f109,f62,f52,f111])).

fof(f52,plain,
    ( spl4_3
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f62,plain,
    ( spl4_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f109,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f64,f54])).

fof(f54,plain,
    ( sK2 = sK3
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f64,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f108,plain,
    ( ~ spl4_11
    | spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f103,f52,f42,f105])).

fof(f42,plain,
    ( spl4_1
  <=> v2_tops_2(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f103,plain,
    ( ~ v2_tops_2(sK2,sK1)
    | spl4_1
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f44,f54])).

fof(f44,plain,
    ( ~ v2_tops_2(sK3,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f102,plain,
    ( spl4_10
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f92,f77,f99])).

fof(f92,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f79,f32])).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f80,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f24,f77])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ v2_tops_2(sK3,sK1)
    & v2_tops_2(sK2,sK0)
    & sK2 = sK3
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f20,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tops_2(X3,X1)
                    & v2_tops_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,sK0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tops_2(X3,X1)
                & v2_tops_2(X2,sK0)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tops_2(X3,sK1)
              & v2_tops_2(X2,sK0)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v2_tops_2(X3,sK1)
            & v2_tops_2(X2,sK0)
            & X2 = X3
            & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X3] :
          ( ~ v2_tops_2(X3,sK1)
          & v2_tops_2(sK2,sK0)
          & sK2 = X3
          & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ~ v2_tops_2(X3,sK1)
        & v2_tops_2(sK2,sK0)
        & sK2 = X3
        & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
   => ( ~ v2_tops_2(sK3,sK1)
      & v2_tops_2(sK2,sK0)
      & sK2 = sK3
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( v2_tops_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v2_tops_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( v2_tops_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tops_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_9)).

fof(f75,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f25,f72])).

fof(f25,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f26,f67])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f29,f52])).

fof(f29,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f30,f47])).

fof(f30,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f31,f42])).

fof(f31,plain,(
    ~ v2_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.50  % (20283)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (20291)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (20268)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (20291)Refutation not found, incomplete strategy% (20291)------------------------------
% 0.22/0.52  % (20291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20291)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20291)Memory used [KB]: 10874
% 0.22/0.54  % (20291)Time elapsed: 0.087 s
% 0.22/0.54  % (20291)------------------------------
% 0.22/0.54  % (20291)------------------------------
% 0.22/0.54  % (20294)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.54  % (20294)Refutation found. Thanks to Tanya!
% 1.40/0.54  % SZS status Theorem for theBenchmark
% 1.40/0.54  % SZS output start Proof for theBenchmark
% 1.40/0.54  fof(f442,plain,(
% 1.40/0.54    $false),
% 1.40/0.54    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f65,f70,f75,f80,f102,f108,f114,f134,f147,f177,f190,f276,f277,f310,f337,f349,f440,f441])).
% 1.40/0.54  fof(f441,plain,(
% 1.40/0.54    u1_struct_0(sK0) != u1_struct_0(sK1) | ~r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK2),u1_pre_topc(sK0)) | r1_tarski(k7_setfam_1(u1_struct_0(sK1),sK2),u1_pre_topc(sK0))),
% 1.40/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.40/0.54  fof(f440,plain,(
% 1.40/0.54    spl4_37 | ~spl4_44 | ~spl4_7 | ~spl4_19 | ~spl4_25),
% 1.40/0.54    inference(avatar_split_clause,[],[f439,f232,f174,f72,f434,f346])).
% 1.40/0.54  fof(f346,plain,(
% 1.40/0.54    spl4_37 <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK2),sK1)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.40/0.54  fof(f434,plain,(
% 1.40/0.54    spl4_44 <=> r1_tarski(k7_setfam_1(u1_struct_0(sK1),sK2),u1_pre_topc(sK0))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.40/0.54  fof(f72,plain,(
% 1.40/0.54    spl4_7 <=> l1_pre_topc(sK1)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.40/0.54  fof(f174,plain,(
% 1.40/0.54    spl4_19 <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.40/0.54  fof(f232,plain,(
% 1.40/0.54    spl4_25 <=> u1_pre_topc(sK0) = u1_pre_topc(sK1)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.40/0.54  fof(f439,plain,(
% 1.40/0.54    ~r1_tarski(k7_setfam_1(u1_struct_0(sK1),sK2),u1_pre_topc(sK0)) | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK2),sK1) | (~spl4_7 | ~spl4_19 | ~spl4_25)),
% 1.40/0.54    inference(forward_demodulation,[],[f438,f234])).
% 1.40/0.54  fof(f234,plain,(
% 1.40/0.54    u1_pre_topc(sK0) = u1_pre_topc(sK1) | ~spl4_25),
% 1.40/0.54    inference(avatar_component_clause,[],[f232])).
% 1.40/0.54  fof(f438,plain,(
% 1.40/0.54    v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK2),sK1) | ~r1_tarski(k7_setfam_1(u1_struct_0(sK1),sK2),u1_pre_topc(sK1)) | (~spl4_7 | ~spl4_19)),
% 1.40/0.54    inference(subsumption_resolution,[],[f425,f74])).
% 1.40/0.54  fof(f74,plain,(
% 1.40/0.54    l1_pre_topc(sK1) | ~spl4_7),
% 1.40/0.54    inference(avatar_component_clause,[],[f72])).
% 1.40/0.54  fof(f425,plain,(
% 1.40/0.54    v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK2),sK1) | ~r1_tarski(k7_setfam_1(u1_struct_0(sK1),sK2),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1) | ~spl4_19),
% 1.40/0.54    inference(resolution,[],[f176,f34])).
% 1.40/0.54  fof(f34,plain,(
% 1.40/0.54    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f22])).
% 1.40/0.54  fof(f22,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.40/0.54    inference(nnf_transformation,[],[f12])).
% 1.40/0.54  fof(f12,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f6])).
% 1.40/0.54  fof(f6,axiom,(
% 1.40/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).
% 1.40/0.54  fof(f176,plain,(
% 1.40/0.54    m1_subset_1(k7_setfam_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl4_19),
% 1.40/0.54    inference(avatar_component_clause,[],[f174])).
% 1.40/0.54  fof(f349,plain,(
% 1.40/0.54    ~spl4_19 | ~spl4_37 | ~spl4_7 | spl4_11 | ~spl4_18),
% 1.40/0.54    inference(avatar_split_clause,[],[f344,f169,f105,f72,f346,f174])).
% 1.40/0.54  fof(f105,plain,(
% 1.40/0.54    spl4_11 <=> v2_tops_2(sK2,sK1)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.40/0.54  fof(f169,plain,(
% 1.40/0.54    spl4_18 <=> sK2 = k7_setfam_1(u1_struct_0(sK1),k7_setfam_1(u1_struct_0(sK1),sK2))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.40/0.54  fof(f344,plain,(
% 1.40/0.54    ~v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK2),sK1) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | (~spl4_7 | spl4_11 | ~spl4_18)),
% 1.40/0.54    inference(subsumption_resolution,[],[f343,f74])).
% 1.40/0.54  fof(f343,plain,(
% 1.40/0.54    ~v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK2),sK1) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | (spl4_11 | ~spl4_18)),
% 1.40/0.54    inference(subsumption_resolution,[],[f340,f107])).
% 1.40/0.54  fof(f107,plain,(
% 1.40/0.54    ~v2_tops_2(sK2,sK1) | spl4_11),
% 1.40/0.54    inference(avatar_component_clause,[],[f105])).
% 1.40/0.54  fof(f340,plain,(
% 1.40/0.54    v2_tops_2(sK2,sK1) | ~v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK2),sK1) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~spl4_18),
% 1.40/0.54    inference(superposition,[],[f35,f171])).
% 1.40/0.54  fof(f171,plain,(
% 1.40/0.54    sK2 = k7_setfam_1(u1_struct_0(sK1),k7_setfam_1(u1_struct_0(sK1),sK2)) | ~spl4_18),
% 1.40/0.54    inference(avatar_component_clause,[],[f169])).
% 1.40/0.54  fof(f35,plain,(
% 1.40/0.54    ( ! [X0,X1] : (v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f23])).
% 1.40/0.54  fof(f23,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) & (v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.40/0.54    inference(nnf_transformation,[],[f13])).
% 1.40/0.54  fof(f13,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f5])).
% 1.40/0.54  fof(f5,axiom,(
% 1.40/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0))))),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tops_2)).
% 1.40/0.54  fof(f337,plain,(
% 1.40/0.54    ~spl4_34 | spl4_36 | ~spl4_8 | ~spl4_14),
% 1.40/0.54    inference(avatar_split_clause,[],[f332,f131,f77,f334,f307])).
% 1.40/0.54  fof(f307,plain,(
% 1.40/0.54    spl4_34 <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.40/0.54  fof(f334,plain,(
% 1.40/0.54    spl4_36 <=> r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK2),u1_pre_topc(sK0))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.40/0.54  fof(f77,plain,(
% 1.40/0.54    spl4_8 <=> l1_pre_topc(sK0)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.40/0.54  fof(f131,plain,(
% 1.40/0.54    spl4_14 <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.40/0.54  fof(f332,plain,(
% 1.40/0.54    r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK2),u1_pre_topc(sK0)) | ~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0) | (~spl4_8 | ~spl4_14)),
% 1.40/0.54    inference(subsumption_resolution,[],[f325,f79])).
% 1.40/0.54  fof(f79,plain,(
% 1.40/0.54    l1_pre_topc(sK0) | ~spl4_8),
% 1.40/0.54    inference(avatar_component_clause,[],[f77])).
% 1.40/0.54  fof(f325,plain,(
% 1.40/0.54    r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK2),u1_pre_topc(sK0)) | ~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0) | ~l1_pre_topc(sK0) | ~spl4_14),
% 1.40/0.54    inference(resolution,[],[f133,f33])).
% 1.40/0.54  fof(f33,plain,(
% 1.40/0.54    ( ! [X0,X1] : (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f22])).
% 1.40/0.54  fof(f133,plain,(
% 1.40/0.54    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl4_14),
% 1.40/0.54    inference(avatar_component_clause,[],[f131])).
% 1.40/0.54  fof(f310,plain,(
% 1.40/0.54    ~spl4_14 | spl4_34 | ~spl4_2 | ~spl4_8 | ~spl4_13),
% 1.40/0.54    inference(avatar_split_clause,[],[f305,f126,f77,f47,f307,f131])).
% 1.40/0.54  fof(f47,plain,(
% 1.40/0.54    spl4_2 <=> v2_tops_2(sK2,sK0)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.40/0.54  fof(f126,plain,(
% 1.40/0.54    spl4_13 <=> sK2 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK2))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.40/0.54  fof(f305,plain,(
% 1.40/0.54    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl4_2 | ~spl4_8 | ~spl4_13)),
% 1.40/0.54    inference(subsumption_resolution,[],[f304,f79])).
% 1.40/0.54  fof(f304,plain,(
% 1.40/0.54    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | (~spl4_2 | ~spl4_13)),
% 1.40/0.54    inference(subsumption_resolution,[],[f302,f49])).
% 1.40/0.54  fof(f49,plain,(
% 1.40/0.54    v2_tops_2(sK2,sK0) | ~spl4_2),
% 1.40/0.54    inference(avatar_component_clause,[],[f47])).
% 1.40/0.54  fof(f302,plain,(
% 1.40/0.54    ~v2_tops_2(sK2,sK0) | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~spl4_13),
% 1.40/0.54    inference(superposition,[],[f36,f128])).
% 1.40/0.54  fof(f128,plain,(
% 1.40/0.54    sK2 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK2)) | ~spl4_13),
% 1.40/0.54    inference(avatar_component_clause,[],[f126])).
% 1.40/0.54  fof(f36,plain,(
% 1.40/0.54    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f23])).
% 1.40/0.54  fof(f277,plain,(
% 1.40/0.54    spl4_26 | ~spl4_4 | ~spl4_10),
% 1.40/0.54    inference(avatar_split_clause,[],[f254,f99,f57,f237])).
% 1.40/0.54  fof(f237,plain,(
% 1.40/0.54    spl4_26 <=> u1_struct_0(sK0) = u1_struct_0(sK1)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.40/0.54  fof(f57,plain,(
% 1.40/0.54    spl4_4 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.40/0.54  fof(f99,plain,(
% 1.40/0.54    spl4_10 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.40/0.54  fof(f254,plain,(
% 1.40/0.54    u1_struct_0(sK0) = u1_struct_0(sK1) | (~spl4_4 | ~spl4_10)),
% 1.40/0.54    inference(unit_resulting_resolution,[],[f59,f101,f39])).
% 1.40/0.54  fof(f39,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f16])).
% 1.40/0.54  fof(f16,plain,(
% 1.40/0.54    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.40/0.54    inference(ennf_transformation,[],[f4])).
% 1.40/0.54  fof(f4,axiom,(
% 1.40/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.40/0.54  fof(f101,plain,(
% 1.40/0.54    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl4_10),
% 1.40/0.54    inference(avatar_component_clause,[],[f99])).
% 1.40/0.54  fof(f59,plain,(
% 1.40/0.54    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~spl4_4),
% 1.40/0.54    inference(avatar_component_clause,[],[f57])).
% 1.40/0.54  fof(f276,plain,(
% 1.40/0.54    spl4_25 | ~spl4_4 | ~spl4_10),
% 1.40/0.54    inference(avatar_split_clause,[],[f255,f99,f57,f232])).
% 1.40/0.54  fof(f255,plain,(
% 1.40/0.54    u1_pre_topc(sK0) = u1_pre_topc(sK1) | (~spl4_4 | ~spl4_10)),
% 1.40/0.54    inference(unit_resulting_resolution,[],[f59,f101,f40])).
% 1.40/0.54  fof(f40,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f16])).
% 1.40/0.54  fof(f190,plain,(
% 1.40/0.54    spl4_18 | ~spl4_12),
% 1.40/0.54    inference(avatar_split_clause,[],[f167,f111,f169])).
% 1.40/0.54  fof(f111,plain,(
% 1.40/0.54    spl4_12 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.40/0.54  fof(f167,plain,(
% 1.40/0.54    sK2 = k7_setfam_1(u1_struct_0(sK1),k7_setfam_1(u1_struct_0(sK1),sK2)) | ~spl4_12),
% 1.40/0.54    inference(resolution,[],[f113,f37])).
% 1.40/0.54  fof(f37,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f14])).
% 1.40/0.54  fof(f14,plain,(
% 1.40/0.54    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.40/0.54    inference(ennf_transformation,[],[f2])).
% 1.40/0.54  fof(f2,axiom,(
% 1.40/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 1.40/0.54  fof(f113,plain,(
% 1.40/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl4_12),
% 1.40/0.54    inference(avatar_component_clause,[],[f111])).
% 1.40/0.54  fof(f177,plain,(
% 1.40/0.54    spl4_19 | ~spl4_12),
% 1.40/0.54    inference(avatar_split_clause,[],[f158,f111,f174])).
% 1.40/0.54  fof(f158,plain,(
% 1.40/0.54    m1_subset_1(k7_setfam_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl4_12),
% 1.40/0.54    inference(unit_resulting_resolution,[],[f113,f38])).
% 1.40/0.54  fof(f38,plain,(
% 1.40/0.54    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f15])).
% 1.40/0.54  fof(f15,plain,(
% 1.40/0.54    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.40/0.54    inference(ennf_transformation,[],[f1])).
% 1.40/0.54  fof(f1,axiom,(
% 1.40/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 1.40/0.54  fof(f147,plain,(
% 1.40/0.54    spl4_13 | ~spl4_6),
% 1.40/0.54    inference(avatar_split_clause,[],[f124,f67,f126])).
% 1.40/0.54  fof(f67,plain,(
% 1.40/0.54    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.40/0.54  fof(f124,plain,(
% 1.40/0.54    sK2 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK2)) | ~spl4_6),
% 1.40/0.54    inference(resolution,[],[f69,f37])).
% 1.40/0.54  fof(f69,plain,(
% 1.40/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl4_6),
% 1.40/0.54    inference(avatar_component_clause,[],[f67])).
% 1.40/0.54  fof(f134,plain,(
% 1.40/0.54    spl4_14 | ~spl4_6),
% 1.40/0.54    inference(avatar_split_clause,[],[f115,f67,f131])).
% 1.40/0.54  fof(f115,plain,(
% 1.40/0.54    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl4_6),
% 1.40/0.54    inference(unit_resulting_resolution,[],[f69,f38])).
% 1.40/0.54  fof(f114,plain,(
% 1.40/0.54    spl4_12 | ~spl4_3 | ~spl4_5),
% 1.40/0.54    inference(avatar_split_clause,[],[f109,f62,f52,f111])).
% 1.40/0.54  fof(f52,plain,(
% 1.40/0.54    spl4_3 <=> sK2 = sK3),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.40/0.54  fof(f62,plain,(
% 1.40/0.54    spl4_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.40/0.54  fof(f109,plain,(
% 1.40/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | (~spl4_3 | ~spl4_5)),
% 1.40/0.54    inference(forward_demodulation,[],[f64,f54])).
% 1.40/0.54  fof(f54,plain,(
% 1.40/0.54    sK2 = sK3 | ~spl4_3),
% 1.40/0.54    inference(avatar_component_clause,[],[f52])).
% 1.40/0.54  fof(f64,plain,(
% 1.40/0.54    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl4_5),
% 1.40/0.54    inference(avatar_component_clause,[],[f62])).
% 1.40/0.54  fof(f108,plain,(
% 1.40/0.54    ~spl4_11 | spl4_1 | ~spl4_3),
% 1.40/0.54    inference(avatar_split_clause,[],[f103,f52,f42,f105])).
% 1.40/0.54  fof(f42,plain,(
% 1.40/0.54    spl4_1 <=> v2_tops_2(sK3,sK1)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.40/0.54  fof(f103,plain,(
% 1.40/0.54    ~v2_tops_2(sK2,sK1) | (spl4_1 | ~spl4_3)),
% 1.40/0.54    inference(backward_demodulation,[],[f44,f54])).
% 1.40/0.54  fof(f44,plain,(
% 1.40/0.54    ~v2_tops_2(sK3,sK1) | spl4_1),
% 1.40/0.54    inference(avatar_component_clause,[],[f42])).
% 1.40/0.54  fof(f102,plain,(
% 1.40/0.54    spl4_10 | ~spl4_8),
% 1.40/0.54    inference(avatar_split_clause,[],[f92,f77,f99])).
% 1.40/0.54  fof(f92,plain,(
% 1.40/0.54    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl4_8),
% 1.40/0.54    inference(unit_resulting_resolution,[],[f79,f32])).
% 1.40/0.54  fof(f32,plain,(
% 1.40/0.54    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f11])).
% 1.40/0.54  fof(f11,plain,(
% 1.40/0.54    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f3])).
% 1.40/0.54  fof(f3,axiom,(
% 1.40/0.54    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.40/0.54  fof(f80,plain,(
% 1.40/0.54    spl4_8),
% 1.40/0.54    inference(avatar_split_clause,[],[f24,f77])).
% 1.40/0.54  fof(f24,plain,(
% 1.40/0.54    l1_pre_topc(sK0)),
% 1.40/0.54    inference(cnf_transformation,[],[f21])).
% 1.40/0.54  fof(f21,plain,(
% 1.40/0.54    (((~v2_tops_2(sK3,sK1) & v2_tops_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f20,f19,f18,f17])).
% 1.40/0.54  fof(f17,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f18,plain,(
% 1.40/0.54    ? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v2_tops_2(X3,sK1) & v2_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK1))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f19,plain,(
% 1.40/0.54    ? [X2] : (? [X3] : (~v2_tops_2(X3,sK1) & v2_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X3] : (~v2_tops_2(X3,sK1) & v2_tops_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f20,plain,(
% 1.40/0.54    ? [X3] : (~v2_tops_2(X3,sK1) & v2_tops_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) => (~v2_tops_2(sK3,sK1) & v2_tops_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f10,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.40/0.54    inference(flattening,[],[f9])).
% 1.40/0.54  fof(f9,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_tops_2(X3,X1) & (v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f8])).
% 1.40/0.54  fof(f8,negated_conjecture,(
% 1.40/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tops_2(X3,X1))))))),
% 1.40/0.54    inference(negated_conjecture,[],[f7])).
% 1.40/0.54  fof(f7,conjecture,(
% 1.40/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tops_2(X3,X1))))))),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_9)).
% 1.40/0.54  fof(f75,plain,(
% 1.40/0.54    spl4_7),
% 1.40/0.54    inference(avatar_split_clause,[],[f25,f72])).
% 1.40/0.54  fof(f25,plain,(
% 1.40/0.54    l1_pre_topc(sK1)),
% 1.40/0.54    inference(cnf_transformation,[],[f21])).
% 1.40/0.54  fof(f70,plain,(
% 1.40/0.54    spl4_6),
% 1.40/0.54    inference(avatar_split_clause,[],[f26,f67])).
% 1.40/0.54  fof(f26,plain,(
% 1.40/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.40/0.54    inference(cnf_transformation,[],[f21])).
% 1.40/0.54  fof(f65,plain,(
% 1.40/0.54    spl4_5),
% 1.40/0.54    inference(avatar_split_clause,[],[f27,f62])).
% 1.40/0.54  fof(f27,plain,(
% 1.40/0.54    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.40/0.54    inference(cnf_transformation,[],[f21])).
% 1.40/0.54  fof(f60,plain,(
% 1.40/0.54    spl4_4),
% 1.40/0.54    inference(avatar_split_clause,[],[f28,f57])).
% 1.40/0.54  fof(f28,plain,(
% 1.40/0.54    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 1.40/0.54    inference(cnf_transformation,[],[f21])).
% 1.40/0.54  fof(f55,plain,(
% 1.40/0.54    spl4_3),
% 1.40/0.54    inference(avatar_split_clause,[],[f29,f52])).
% 1.40/0.54  fof(f29,plain,(
% 1.40/0.54    sK2 = sK3),
% 1.40/0.54    inference(cnf_transformation,[],[f21])).
% 1.40/0.54  fof(f50,plain,(
% 1.40/0.54    spl4_2),
% 1.40/0.54    inference(avatar_split_clause,[],[f30,f47])).
% 1.40/0.54  fof(f30,plain,(
% 1.40/0.54    v2_tops_2(sK2,sK0)),
% 1.40/0.54    inference(cnf_transformation,[],[f21])).
% 1.40/0.54  fof(f45,plain,(
% 1.40/0.54    ~spl4_1),
% 1.40/0.54    inference(avatar_split_clause,[],[f31,f42])).
% 1.40/0.54  fof(f31,plain,(
% 1.40/0.54    ~v2_tops_2(sK3,sK1)),
% 1.40/0.54    inference(cnf_transformation,[],[f21])).
% 1.40/0.54  % SZS output end Proof for theBenchmark
% 1.40/0.54  % (20294)------------------------------
% 1.40/0.54  % (20294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (20294)Termination reason: Refutation
% 1.40/0.54  
% 1.40/0.54  % (20294)Memory used [KB]: 6524
% 1.40/0.54  % (20294)Time elapsed: 0.137 s
% 1.40/0.54  % (20294)------------------------------
% 1.40/0.54  % (20294)------------------------------
% 1.40/0.54  % (20260)Success in time 0.184 s
%------------------------------------------------------------------------------
