%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  236 ( 458 expanded)
%              Number of leaves         :   59 ( 201 expanded)
%              Depth                    :   10
%              Number of atoms          :  916 (2544 expanded)
%              Number of equality atoms :   64 ( 272 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f875,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f154,f159,f164,f169,f179,f184,f189,f194,f200,f206,f216,f226,f229,f242,f245,f258,f275,f279,f295,f326,f337,f347,f352,f368,f373,f378,f391,f400,f431,f446,f595,f830,f854,f856,f858,f865])).

fof(f865,plain,
    ( ~ spl10_26
    | spl10_35 ),
    inference(avatar_split_clause,[],[f860,f302,f236])).

fof(f236,plain,
    ( spl10_26
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f302,plain,
    ( spl10_35
  <=> m1_pre_topc(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f860,plain,
    ( ~ l1_pre_topc(sK2)
    | spl10_35 ),
    inference(resolution,[],[f304,f59])).

fof(f59,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f304,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | spl10_35 ),
    inference(avatar_component_clause,[],[f302])).

fof(f858,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | spl10_3
    | ~ spl10_7
    | spl10_8
    | ~ spl10_9
    | ~ spl10_20
    | ~ spl10_21
    | ~ spl10_36
    | ~ spl10_54
    | ~ spl10_82 ),
    inference(avatar_contradiction_clause,[],[f857])).

fof(f857,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | spl10_3
    | ~ spl10_7
    | spl10_8
    | ~ spl10_9
    | ~ spl10_20
    | ~ spl10_21
    | ~ spl10_36
    | ~ spl10_54
    | ~ spl10_82 ),
    inference(unit_resulting_resolution,[],[f103,f138,f108,f113,f133,f143,f308,f199,f205,f776,f594])).

fof(f594,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f593])).

fof(f593,plain,
    ( spl10_54
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f776,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ spl10_82 ),
    inference(avatar_component_clause,[],[f775])).

fof(f775,plain,
    ( spl10_82
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).

fof(f205,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl10_21
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f199,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl10_20
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f308,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl10_36
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f143,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl10_9
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f133,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl10_7
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f113,plain,
    ( ~ v2_struct_0(sK0)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl10_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f108,plain,
    ( v2_pre_topc(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl10_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f138,plain,
    ( ~ v2_struct_0(sK2)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl10_8
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f103,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl10_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f856,plain,
    ( ~ spl10_42
    | ~ spl10_90
    | ~ spl10_36
    | ~ spl10_25
    | ~ spl10_49
    | ~ spl10_37
    | spl10_82 ),
    inference(avatar_split_clause,[],[f855,f775,f323,f428,f223,f307,f821,f361])).

fof(f361,plain,
    ( spl10_42
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f821,plain,
    ( spl10_90
  <=> v3_pre_topc(u1_struct_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_90])])).

fof(f223,plain,
    ( spl10_25
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f428,plain,
    ( spl10_49
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f323,plain,
    ( spl10_37
  <=> u1_struct_0(sK2) = u1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f855,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_37
    | spl10_82 ),
    inference(forward_demodulation,[],[f838,f325])).

fof(f325,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f323])).

fof(f838,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v2_pre_topc(sK3)
    | spl10_82 ),
    inference(resolution,[],[f777,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f777,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | spl10_82 ),
    inference(avatar_component_clause,[],[f775])).

fof(f854,plain,
    ( ~ spl10_25
    | ~ spl10_49
    | ~ spl10_46
    | ~ spl10_37
    | ~ spl10_45
    | spl10_90 ),
    inference(avatar_split_clause,[],[f853,f821,f388,f323,f397,f428,f223])).

fof(f397,plain,
    ( spl10_46
  <=> r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f388,plain,
    ( spl10_45
  <=> u1_pre_topc(sK2) = u1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f853,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK3)
    | ~ spl10_37
    | ~ spl10_45
    | spl10_90 ),
    inference(forward_demodulation,[],[f852,f390])).

fof(f390,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(sK3)
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f388])).

fof(f852,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ spl10_37
    | spl10_90 ),
    inference(forward_demodulation,[],[f850,f325])).

fof(f850,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3)
    | spl10_90 ),
    inference(resolution,[],[f823,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f823,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | spl10_90 ),
    inference(avatar_component_clause,[],[f821])).

fof(f830,plain,
    ( ~ spl10_26
    | ~ spl10_35
    | ~ spl10_27
    | spl10_36 ),
    inference(avatar_split_clause,[],[f826,f307,f240,f302,f236])).

fof(f240,plain,
    ( spl10_27
  <=> ! [X0] :
        ( m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK2)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f826,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ spl10_27
    | spl10_36 ),
    inference(resolution,[],[f309,f241])).

fof(f241,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK2)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f240])).

fof(f309,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | spl10_36 ),
    inference(avatar_component_clause,[],[f307])).

fof(f595,plain,
    ( ~ spl10_14
    | spl10_10
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6
    | spl10_54
    | ~ spl10_41
    | ~ spl10_40
    | ~ spl10_20
    | spl10_16
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f591,f323,f176,f197,f344,f349,f593,f126,f121,f116,f146,f166])).

fof(f166,plain,
    ( spl10_14
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f146,plain,
    ( spl10_10
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f116,plain,
    ( spl10_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f121,plain,
    ( spl10_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f126,plain,
    ( spl10_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f349,plain,
    ( spl10_41
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f344,plain,
    ( spl10_40
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f176,plain,
    ( spl10_16
  <=> r1_tmap_1(sK3,sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f591,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ v1_funct_1(sK4)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | v2_struct_0(X0) )
    | spl10_16
    | ~ spl10_37 ),
    inference(forward_demodulation,[],[f590,f325])).

fof(f590,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ v1_funct_1(sK4)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | v2_struct_0(X0) )
    | spl10_16
    | ~ spl10_37 ),
    inference(forward_demodulation,[],[f589,f325])).

fof(f589,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | v2_struct_0(X0) )
    | spl10_16
    | ~ spl10_37 ),
    inference(forward_demodulation,[],[f588,f325])).

fof(f588,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | v2_struct_0(X0) )
    | spl10_16 ),
    inference(resolution,[],[f97,f178])).

fof(f178,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | spl10_16 ),
    inference(avatar_component_clause,[],[f176])).

fof(f97,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | X5 != X6
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f446,plain,
    ( ~ spl10_25
    | spl10_48 ),
    inference(avatar_split_clause,[],[f435,f424,f223])).

fof(f424,plain,
    ( spl10_48
  <=> m1_pre_topc(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f435,plain,
    ( ~ l1_pre_topc(sK3)
    | spl10_48 ),
    inference(resolution,[],[f426,f59])).

fof(f426,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | spl10_48 ),
    inference(avatar_component_clause,[],[f424])).

fof(f431,plain,
    ( ~ spl10_48
    | spl10_49
    | ~ spl10_37
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f422,f371,f323,f428,f424])).

fof(f371,plain,
    ( spl10_44
  <=> ! [X1] :
        ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_pre_topc(X1,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f422,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ spl10_37
    | ~ spl10_44 ),
    inference(superposition,[],[f372,f325])).

fof(f372,plain,
    ( ! [X1] :
        ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_pre_topc(X1,sK3) )
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f371])).

fof(f400,plain,
    ( spl10_46
    | ~ spl10_43
    | ~ spl10_45 ),
    inference(avatar_split_clause,[],[f392,f388,f365,f397])).

fof(f365,plain,
    ( spl10_43
  <=> r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f392,plain,
    ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl10_43
    | ~ spl10_45 ),
    inference(backward_demodulation,[],[f367,f390])).

fof(f367,plain,
    ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3))
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f365])).

fof(f391,plain,
    ( spl10_45
    | ~ spl10_32
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f386,f334,f277,f388])).

fof(f277,plain,
    ( spl10_32
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != sK3
        | u1_pre_topc(sK2) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f334,plain,
    ( spl10_38
  <=> sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f386,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(sK3)
    | ~ spl10_32
    | ~ spl10_38 ),
    inference(trivial_inequality_removal,[],[f385])).

fof(f385,plain,
    ( sK3 != sK3
    | u1_pre_topc(sK2) = u1_pre_topc(sK3)
    | ~ spl10_32
    | ~ spl10_38 ),
    inference(superposition,[],[f278,f336])).

fof(f336,plain,
    ( sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK3))
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f334])).

fof(f278,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK3
        | u1_pre_topc(sK2) = X1 )
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f277])).

fof(f378,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_9
    | spl10_42 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_9
    | spl10_42 ),
    inference(unit_resulting_resolution,[],[f108,f103,f143,f363,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f363,plain,
    ( ~ v2_pre_topc(sK3)
    | spl10_42 ),
    inference(avatar_component_clause,[],[f361])).

fof(f373,plain,
    ( ~ spl10_25
    | spl10_44
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f356,f323,f371,f223])).

fof(f356,plain,
    ( ! [X1] :
        ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_pre_topc(X1,sK3)
        | ~ l1_pre_topc(sK3) )
    | ~ spl10_37 ),
    inference(superposition,[],[f83,f325])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f368,plain,
    ( ~ spl10_42
    | ~ spl10_25
    | spl10_43
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f354,f323,f365,f223,f361])).

fof(f354,plain,
    ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_37 ),
    inference(superposition,[],[f79,f325])).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

% (28649)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f17,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f352,plain,
    ( spl10_41
    | ~ spl10_13
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f331,f323,f161,f349])).

fof(f161,plain,
    ( spl10_13
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f331,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl10_13
    | ~ spl10_37 ),
    inference(backward_demodulation,[],[f163,f325])).

fof(f163,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f347,plain,
    ( spl10_40
    | ~ spl10_12
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f330,f323,f156,f344])).

fof(f156,plain,
    ( spl10_12
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f330,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl10_12
    | ~ spl10_37 ),
    inference(backward_demodulation,[],[f158,f325])).

fof(f158,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f156])).

fof(f337,plain,
    ( spl10_38
    | ~ spl10_24
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f327,f323,f219,f334])).

fof(f219,plain,
    ( spl10_24
  <=> sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f327,plain,
    ( sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK3))
    | ~ spl10_24
    | ~ spl10_37 ),
    inference(backward_demodulation,[],[f221,f325])).

fof(f221,plain,
    ( sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f219])).

fof(f326,plain,
    ( spl10_37
    | ~ spl10_24
    | ~ spl10_29 ),
    inference(avatar_split_clause,[],[f321,f256,f219,f323])).

fof(f256,plain,
    ( spl10_29
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != sK3
        | u1_struct_0(sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f321,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ spl10_24
    | ~ spl10_29 ),
    inference(trivial_inequality_removal,[],[f320])).

fof(f320,plain,
    ( sK3 != sK3
    | u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ spl10_24
    | ~ spl10_29 ),
    inference(superposition,[],[f257,f221])).

fof(f257,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK3
        | u1_struct_0(sK2) = X0 )
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f256])).

fof(f295,plain,
    ( ~ spl10_7
    | ~ spl10_1
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f290,f210,f101,f131])).

fof(f210,plain,
    ( spl10_22
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f290,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ spl10_1
    | ~ spl10_22 ),
    inference(resolution,[],[f211,f103])).

fof(f211,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0) )
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f210])).

fof(f279,plain,
    ( ~ spl10_28
    | spl10_32
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f267,f151,f277,f252])).

fof(f252,plain,
    ( spl10_28
  <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f151,plain,
    ( spl10_11
  <=> sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f267,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK3
        | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | u1_pre_topc(sK2) = X1 )
    | ~ spl10_11 ),
    inference(superposition,[],[f95,f153])).

fof(f153,plain,
    ( sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f275,plain,
    ( ~ spl10_26
    | spl10_28 ),
    inference(avatar_split_clause,[],[f273,f252,f236])).

fof(f273,plain,
    ( ~ l1_pre_topc(sK2)
    | spl10_28 ),
    inference(resolution,[],[f254,f60])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f254,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | spl10_28 ),
    inference(avatar_component_clause,[],[f252])).

fof(f258,plain,
    ( ~ spl10_28
    | spl10_29
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f246,f151,f256,f252])).

fof(f246,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK3
        | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | u1_struct_0(sK2) = X0 )
    | ~ spl10_11 ),
    inference(superposition,[],[f94,f153])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f245,plain,
    ( ~ spl10_1
    | ~ spl10_7
    | spl10_26 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_7
    | spl10_26 ),
    inference(unit_resulting_resolution,[],[f103,f133,f238,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f238,plain,
    ( ~ l1_pre_topc(sK2)
    | spl10_26 ),
    inference(avatar_component_clause,[],[f236])).

fof(f242,plain,
    ( ~ spl10_26
    | spl10_27
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f233,f151,f240,f236])).

fof(f233,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK2)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl10_11 ),
    inference(superposition,[],[f81,f153])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f229,plain,
    ( ~ spl10_1
    | ~ spl10_9
    | spl10_25 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_9
    | spl10_25 ),
    inference(unit_resulting_resolution,[],[f103,f143,f225,f82])).

fof(f225,plain,
    ( ~ l1_pre_topc(sK3)
    | spl10_25 ),
    inference(avatar_component_clause,[],[f223])).

fof(f226,plain,
    ( spl10_24
    | ~ spl10_25
    | ~ spl10_23 ),
    inference(avatar_split_clause,[],[f217,f213,f223,f219])).

fof(f213,plain,
    ( spl10_23
  <=> v1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f217,plain,
    ( ~ l1_pre_topc(sK3)
    | sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ spl10_23 ),
    inference(resolution,[],[f215,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f215,plain,
    ( v1_pre_topc(sK3)
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f213])).

fof(f216,plain,
    ( spl10_22
    | spl10_23
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f208,f151,f213,f210])).

fof(f208,plain,
    ( ! [X0] :
        ( v1_pre_topc(sK3)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_11 ),
    inference(superposition,[],[f84,f153])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f206,plain,
    ( spl10_21
    | ~ spl10_17
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f201,f186,f181,f203])).

fof(f181,plain,
    ( spl10_17
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f186,plain,
    ( spl10_18
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f201,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl10_17
    | ~ spl10_18 ),
    inference(forward_demodulation,[],[f183,f188])).

fof(f188,plain,
    ( sK5 = sK6
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f186])).

fof(f183,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f181])).

fof(f200,plain,
    ( spl10_20
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f195,f191,f186,f197])).

fof(f191,plain,
    ( spl10_19
  <=> m1_subset_1(sK6,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f195,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(backward_demodulation,[],[f193,f188])).

fof(f193,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f191])).

fof(f194,plain,(
    spl10_19 ),
    inference(avatar_split_clause,[],[f40,f191])).

fof(f40,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f189,plain,(
    spl10_18 ),
    inference(avatar_split_clause,[],[f41,f186])).

fof(f41,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f19])).

fof(f184,plain,(
    spl10_17 ),
    inference(avatar_split_clause,[],[f42,f181])).

fof(f42,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f19])).

fof(f179,plain,(
    ~ spl10_16 ),
    inference(avatar_split_clause,[],[f43,f176])).

fof(f43,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f169,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f45,f166])).

fof(f45,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f164,plain,(
    spl10_13 ),
    inference(avatar_split_clause,[],[f46,f161])).

fof(f46,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f159,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f47,f156])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f154,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f48,f151])).

fof(f48,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f149,plain,(
    ~ spl10_10 ),
    inference(avatar_split_clause,[],[f49,f146])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f144,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f50,f141])).

fof(f50,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f139,plain,(
    ~ spl10_8 ),
    inference(avatar_split_clause,[],[f51,f136])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f134,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f52,f131])).

fof(f52,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f129,plain,(
    ~ spl10_6 ),
    inference(avatar_split_clause,[],[f53,f126])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f124,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f54,f121])).

fof(f54,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f119,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f55,f116])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f114,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f56,f111])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f109,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f57,f106])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f104,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f58,f101])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:34:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.44  % (28661)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.46  % (28653)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.46  % (28669)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.50  % (28661)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f875,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f154,f159,f164,f169,f179,f184,f189,f194,f200,f206,f216,f226,f229,f242,f245,f258,f275,f279,f295,f326,f337,f347,f352,f368,f373,f378,f391,f400,f431,f446,f595,f830,f854,f856,f858,f865])).
% 0.20/0.50  fof(f865,plain,(
% 0.20/0.50    ~spl10_26 | spl10_35),
% 0.20/0.50    inference(avatar_split_clause,[],[f860,f302,f236])).
% 0.20/0.50  fof(f236,plain,(
% 0.20/0.50    spl10_26 <=> l1_pre_topc(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 0.20/0.50  fof(f302,plain,(
% 0.20/0.50    spl10_35 <=> m1_pre_topc(sK2,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).
% 0.20/0.50  fof(f860,plain,(
% 0.20/0.50    ~l1_pre_topc(sK2) | spl10_35),
% 0.20/0.50    inference(resolution,[],[f304,f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.50  fof(f304,plain,(
% 0.20/0.50    ~m1_pre_topc(sK2,sK2) | spl10_35),
% 0.20/0.50    inference(avatar_component_clause,[],[f302])).
% 0.20/0.50  fof(f858,plain,(
% 0.20/0.50    ~spl10_1 | ~spl10_2 | spl10_3 | ~spl10_7 | spl10_8 | ~spl10_9 | ~spl10_20 | ~spl10_21 | ~spl10_36 | ~spl10_54 | ~spl10_82),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f857])).
% 0.20/0.50  fof(f857,plain,(
% 0.20/0.50    $false | (~spl10_1 | ~spl10_2 | spl10_3 | ~spl10_7 | spl10_8 | ~spl10_9 | ~spl10_20 | ~spl10_21 | ~spl10_36 | ~spl10_54 | ~spl10_82)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f103,f138,f108,f113,f133,f143,f308,f199,f205,f776,f594])).
% 0.20/0.50  fof(f594,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(X1) | v2_struct_0(X0) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(sK3,X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl10_54),
% 0.20/0.50    inference(avatar_component_clause,[],[f593])).
% 0.20/0.50  fof(f593,plain,(
% 0.20/0.50    spl10_54 <=> ! [X1,X0] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).
% 0.20/0.50  fof(f776,plain,(
% 0.20/0.50    v1_tsep_1(sK2,sK3) | ~spl10_82),
% 0.20/0.50    inference(avatar_component_clause,[],[f775])).
% 0.20/0.50  fof(f775,plain,(
% 0.20/0.50    spl10_82 <=> v1_tsep_1(sK2,sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~spl10_21),
% 0.20/0.50    inference(avatar_component_clause,[],[f203])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    spl10_21 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.20/0.50  fof(f199,plain,(
% 0.20/0.50    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl10_20),
% 0.20/0.50    inference(avatar_component_clause,[],[f197])).
% 0.20/0.50  fof(f197,plain,(
% 0.20/0.50    spl10_20 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.20/0.50  fof(f308,plain,(
% 0.20/0.50    m1_pre_topc(sK2,sK3) | ~spl10_36),
% 0.20/0.50    inference(avatar_component_clause,[],[f307])).
% 0.20/0.50  fof(f307,plain,(
% 0.20/0.50    spl10_36 <=> m1_pre_topc(sK2,sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    m1_pre_topc(sK3,sK0) | ~spl10_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f141])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    spl10_9 <=> m1_pre_topc(sK3,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    m1_pre_topc(sK2,sK0) | ~spl10_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f131])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    spl10_7 <=> m1_pre_topc(sK2,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    ~v2_struct_0(sK0) | spl10_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f111])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    spl10_3 <=> v2_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    v2_pre_topc(sK0) | ~spl10_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f106])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    spl10_2 <=> v2_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    ~v2_struct_0(sK2) | spl10_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f136])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    spl10_8 <=> v2_struct_0(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    l1_pre_topc(sK0) | ~spl10_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f101])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    spl10_1 <=> l1_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.50  fof(f856,plain,(
% 0.20/0.50    ~spl10_42 | ~spl10_90 | ~spl10_36 | ~spl10_25 | ~spl10_49 | ~spl10_37 | spl10_82),
% 0.20/0.50    inference(avatar_split_clause,[],[f855,f775,f323,f428,f223,f307,f821,f361])).
% 0.20/0.50  fof(f361,plain,(
% 0.20/0.50    spl10_42 <=> v2_pre_topc(sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).
% 0.20/0.50  fof(f821,plain,(
% 0.20/0.50    spl10_90 <=> v3_pre_topc(u1_struct_0(sK2),sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_90])])).
% 0.20/0.50  fof(f223,plain,(
% 0.20/0.50    spl10_25 <=> l1_pre_topc(sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 0.20/0.50  fof(f428,plain,(
% 0.20/0.50    spl10_49 <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).
% 0.20/0.50  fof(f323,plain,(
% 0.20/0.50    spl10_37 <=> u1_struct_0(sK2) = u1_struct_0(sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).
% 0.20/0.50  fof(f855,plain,(
% 0.20/0.50    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK3) | ~m1_pre_topc(sK2,sK3) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~v2_pre_topc(sK3) | (~spl10_37 | spl10_82)),
% 0.20/0.50    inference(forward_demodulation,[],[f838,f325])).
% 0.20/0.50  fof(f325,plain,(
% 0.20/0.50    u1_struct_0(sK2) = u1_struct_0(sK3) | ~spl10_37),
% 0.20/0.50    inference(avatar_component_clause,[],[f323])).
% 0.20/0.50  fof(f838,plain,(
% 0.20/0.50    ~l1_pre_topc(sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~v2_pre_topc(sK3) | spl10_82),
% 0.20/0.50    inference(resolution,[],[f777,f98])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f93])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.20/0.51  fof(f777,plain,(
% 0.20/0.51    ~v1_tsep_1(sK2,sK3) | spl10_82),
% 0.20/0.51    inference(avatar_component_clause,[],[f775])).
% 0.20/0.51  fof(f854,plain,(
% 0.20/0.51    ~spl10_25 | ~spl10_49 | ~spl10_46 | ~spl10_37 | ~spl10_45 | spl10_90),
% 0.20/0.51    inference(avatar_split_clause,[],[f853,f821,f388,f323,f397,f428,f223])).
% 0.20/0.51  fof(f397,plain,(
% 0.20/0.51    spl10_46 <=> r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).
% 0.20/0.51  fof(f388,plain,(
% 0.20/0.51    spl10_45 <=> u1_pre_topc(sK2) = u1_pre_topc(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).
% 0.20/0.51  fof(f853,plain,(
% 0.20/0.51    ~r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK3) | (~spl10_37 | ~spl10_45 | spl10_90)),
% 0.20/0.51    inference(forward_demodulation,[],[f852,f390])).
% 0.20/0.51  fof(f390,plain,(
% 0.20/0.51    u1_pre_topc(sK2) = u1_pre_topc(sK3) | ~spl10_45),
% 0.20/0.51    inference(avatar_component_clause,[],[f388])).
% 0.20/0.51  fof(f852,plain,(
% 0.20/0.51    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3)) | ~l1_pre_topc(sK3) | (~spl10_37 | spl10_90)),
% 0.20/0.51    inference(forward_demodulation,[],[f850,f325])).
% 0.20/0.51  fof(f850,plain,(
% 0.20/0.51    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3)) | ~l1_pre_topc(sK3) | spl10_90),
% 0.20/0.51    inference(resolution,[],[f823,f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.20/0.51  fof(f823,plain,(
% 0.20/0.51    ~v3_pre_topc(u1_struct_0(sK2),sK3) | spl10_90),
% 0.20/0.51    inference(avatar_component_clause,[],[f821])).
% 0.20/0.51  fof(f830,plain,(
% 0.20/0.51    ~spl10_26 | ~spl10_35 | ~spl10_27 | spl10_36),
% 0.20/0.51    inference(avatar_split_clause,[],[f826,f307,f240,f302,f236])).
% 0.20/0.51  fof(f240,plain,(
% 0.20/0.51    spl10_27 <=> ! [X0] : (m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 0.20/0.51  fof(f826,plain,(
% 0.20/0.51    ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK2) | (~spl10_27 | spl10_36)),
% 0.20/0.51    inference(resolution,[],[f309,f241])).
% 0.20/0.51  fof(f241,plain,(
% 0.20/0.51    ( ! [X0] : (m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(X0)) ) | ~spl10_27),
% 0.20/0.51    inference(avatar_component_clause,[],[f240])).
% 0.20/0.51  fof(f309,plain,(
% 0.20/0.51    ~m1_pre_topc(sK2,sK3) | spl10_36),
% 0.20/0.51    inference(avatar_component_clause,[],[f307])).
% 0.20/0.51  fof(f595,plain,(
% 0.20/0.51    ~spl10_14 | spl10_10 | ~spl10_4 | ~spl10_5 | spl10_6 | spl10_54 | ~spl10_41 | ~spl10_40 | ~spl10_20 | spl10_16 | ~spl10_37),
% 0.20/0.51    inference(avatar_split_clause,[],[f591,f323,f176,f197,f344,f349,f593,f126,f121,f116,f146,f166])).
% 0.20/0.51  fof(f166,plain,(
% 0.20/0.51    spl10_14 <=> v1_funct_1(sK4)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    spl10_10 <=> v2_struct_0(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    spl10_4 <=> l1_pre_topc(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    spl10_5 <=> v2_pre_topc(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    spl10_6 <=> v2_struct_0(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.20/0.51  fof(f349,plain,(
% 0.20/0.51    spl10_41 <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).
% 0.20/0.51  fof(f344,plain,(
% 0.20/0.51    spl10_40 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).
% 0.20/0.51  fof(f176,plain,(
% 0.20/0.51    spl10_16 <=> r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.20/0.51  fof(f591,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | ~v1_funct_1(sK4) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | v2_struct_0(X0)) ) | (spl10_16 | ~spl10_37)),
% 0.20/0.51    inference(forward_demodulation,[],[f590,f325])).
% 0.20/0.51  fof(f590,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | ~v1_funct_1(sK4) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | v2_struct_0(X0)) ) | (spl10_16 | ~spl10_37)),
% 0.20/0.51    inference(forward_demodulation,[],[f589,f325])).
% 0.20/0.51  fof(f589,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | v2_struct_0(X0)) ) | (spl10_16 | ~spl10_37)),
% 0.20/0.51    inference(forward_demodulation,[],[f588,f325])).
% 0.20/0.51  fof(f588,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | v2_struct_0(X0)) ) | spl10_16),
% 0.20/0.51    inference(resolution,[],[f97,f178])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    ~r1_tmap_1(sK3,sK1,sK4,sK5) | spl10_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f176])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | X5 != X6 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).
% 0.20/0.51  fof(f446,plain,(
% 0.20/0.51    ~spl10_25 | spl10_48),
% 0.20/0.51    inference(avatar_split_clause,[],[f435,f424,f223])).
% 0.20/0.51  fof(f424,plain,(
% 0.20/0.51    spl10_48 <=> m1_pre_topc(sK3,sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).
% 0.20/0.51  fof(f435,plain,(
% 0.20/0.51    ~l1_pre_topc(sK3) | spl10_48),
% 0.20/0.51    inference(resolution,[],[f426,f59])).
% 0.20/0.51  fof(f426,plain,(
% 0.20/0.51    ~m1_pre_topc(sK3,sK3) | spl10_48),
% 0.20/0.51    inference(avatar_component_clause,[],[f424])).
% 0.20/0.51  fof(f431,plain,(
% 0.20/0.51    ~spl10_48 | spl10_49 | ~spl10_37 | ~spl10_44),
% 0.20/0.51    inference(avatar_split_clause,[],[f422,f371,f323,f428,f424])).
% 0.20/0.51  fof(f371,plain,(
% 0.20/0.51    spl10_44 <=> ! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_pre_topc(X1,sK3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).
% 0.20/0.51  fof(f422,plain,(
% 0.20/0.51    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_pre_topc(sK3,sK3) | (~spl10_37 | ~spl10_44)),
% 0.20/0.51    inference(superposition,[],[f372,f325])).
% 0.20/0.51  fof(f372,plain,(
% 0.20/0.51    ( ! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_pre_topc(X1,sK3)) ) | ~spl10_44),
% 0.20/0.51    inference(avatar_component_clause,[],[f371])).
% 0.20/0.51  fof(f400,plain,(
% 0.20/0.51    spl10_46 | ~spl10_43 | ~spl10_45),
% 0.20/0.51    inference(avatar_split_clause,[],[f392,f388,f365,f397])).
% 0.20/0.51  fof(f365,plain,(
% 0.20/0.51    spl10_43 <=> r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).
% 0.20/0.51  fof(f392,plain,(
% 0.20/0.51    r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2)) | (~spl10_43 | ~spl10_45)),
% 0.20/0.51    inference(backward_demodulation,[],[f367,f390])).
% 0.20/0.51  fof(f367,plain,(
% 0.20/0.51    r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3)) | ~spl10_43),
% 0.20/0.51    inference(avatar_component_clause,[],[f365])).
% 0.20/0.51  fof(f391,plain,(
% 0.20/0.51    spl10_45 | ~spl10_32 | ~spl10_38),
% 0.20/0.51    inference(avatar_split_clause,[],[f386,f334,f277,f388])).
% 0.20/0.51  fof(f277,plain,(
% 0.20/0.51    spl10_32 <=> ! [X1,X0] : (g1_pre_topc(X0,X1) != sK3 | u1_pre_topc(sK2) = X1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).
% 0.20/0.51  fof(f334,plain,(
% 0.20/0.51    spl10_38 <=> sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).
% 0.20/0.51  fof(f386,plain,(
% 0.20/0.51    u1_pre_topc(sK2) = u1_pre_topc(sK3) | (~spl10_32 | ~spl10_38)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f385])).
% 0.20/0.51  fof(f385,plain,(
% 0.20/0.51    sK3 != sK3 | u1_pre_topc(sK2) = u1_pre_topc(sK3) | (~spl10_32 | ~spl10_38)),
% 0.20/0.51    inference(superposition,[],[f278,f336])).
% 0.20/0.51  fof(f336,plain,(
% 0.20/0.51    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK3)) | ~spl10_38),
% 0.20/0.51    inference(avatar_component_clause,[],[f334])).
% 0.20/0.51  fof(f278,plain,(
% 0.20/0.51    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != sK3 | u1_pre_topc(sK2) = X1) ) | ~spl10_32),
% 0.20/0.51    inference(avatar_component_clause,[],[f277])).
% 0.20/0.51  fof(f378,plain,(
% 0.20/0.51    ~spl10_1 | ~spl10_2 | ~spl10_9 | spl10_42),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f376])).
% 0.20/0.51  fof(f376,plain,(
% 0.20/0.51    $false | (~spl10_1 | ~spl10_2 | ~spl10_9 | spl10_42)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f108,f103,f143,f363,f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.20/0.51  fof(f363,plain,(
% 0.20/0.51    ~v2_pre_topc(sK3) | spl10_42),
% 0.20/0.51    inference(avatar_component_clause,[],[f361])).
% 0.20/0.51  fof(f373,plain,(
% 0.20/0.51    ~spl10_25 | spl10_44 | ~spl10_37),
% 0.20/0.51    inference(avatar_split_clause,[],[f356,f323,f371,f223])).
% 0.20/0.51  fof(f356,plain,(
% 0.20/0.51    ( ! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_pre_topc(X1,sK3) | ~l1_pre_topc(sK3)) ) | ~spl10_37),
% 0.20/0.51    inference(superposition,[],[f83,f325])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.51  fof(f368,plain,(
% 0.20/0.51    ~spl10_42 | ~spl10_25 | spl10_43 | ~spl10_37),
% 0.20/0.51    inference(avatar_split_clause,[],[f354,f323,f365,f223,f361])).
% 0.20/0.51  fof(f354,plain,(
% 0.20/0.51    r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~spl10_37),
% 0.20/0.51    inference(superposition,[],[f79,f325])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f17])).
% 0.20/0.51  % (28649)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.20/0.51    inference(rectify,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.20/0.51  fof(f352,plain,(
% 0.20/0.51    spl10_41 | ~spl10_13 | ~spl10_37),
% 0.20/0.51    inference(avatar_split_clause,[],[f331,f323,f161,f349])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    spl10_13 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.20/0.51  fof(f331,plain,(
% 0.20/0.51    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | (~spl10_13 | ~spl10_37)),
% 0.20/0.51    inference(backward_demodulation,[],[f163,f325])).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl10_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f161])).
% 0.20/0.51  fof(f347,plain,(
% 0.20/0.51    spl10_40 | ~spl10_12 | ~spl10_37),
% 0.20/0.51    inference(avatar_split_clause,[],[f330,f323,f156,f344])).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    spl10_12 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.20/0.51  fof(f330,plain,(
% 0.20/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | (~spl10_12 | ~spl10_37)),
% 0.20/0.51    inference(backward_demodulation,[],[f158,f325])).
% 0.20/0.51  fof(f158,plain,(
% 0.20/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl10_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f156])).
% 0.20/0.51  fof(f337,plain,(
% 0.20/0.51    spl10_38 | ~spl10_24 | ~spl10_37),
% 0.20/0.51    inference(avatar_split_clause,[],[f327,f323,f219,f334])).
% 0.20/0.51  fof(f219,plain,(
% 0.20/0.51    spl10_24 <=> sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 0.20/0.51  fof(f327,plain,(
% 0.20/0.51    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK3)) | (~spl10_24 | ~spl10_37)),
% 0.20/0.51    inference(backward_demodulation,[],[f221,f325])).
% 0.20/0.51  fof(f221,plain,(
% 0.20/0.51    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | ~spl10_24),
% 0.20/0.51    inference(avatar_component_clause,[],[f219])).
% 0.20/0.51  fof(f326,plain,(
% 0.20/0.51    spl10_37 | ~spl10_24 | ~spl10_29),
% 0.20/0.51    inference(avatar_split_clause,[],[f321,f256,f219,f323])).
% 0.20/0.51  fof(f256,plain,(
% 0.20/0.51    spl10_29 <=> ! [X1,X0] : (g1_pre_topc(X0,X1) != sK3 | u1_struct_0(sK2) = X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 0.20/0.51  fof(f321,plain,(
% 0.20/0.51    u1_struct_0(sK2) = u1_struct_0(sK3) | (~spl10_24 | ~spl10_29)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f320])).
% 0.20/0.51  fof(f320,plain,(
% 0.20/0.51    sK3 != sK3 | u1_struct_0(sK2) = u1_struct_0(sK3) | (~spl10_24 | ~spl10_29)),
% 0.20/0.51    inference(superposition,[],[f257,f221])).
% 0.20/0.51  fof(f257,plain,(
% 0.20/0.51    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != sK3 | u1_struct_0(sK2) = X0) ) | ~spl10_29),
% 0.20/0.51    inference(avatar_component_clause,[],[f256])).
% 0.20/0.51  fof(f295,plain,(
% 0.20/0.51    ~spl10_7 | ~spl10_1 | ~spl10_22),
% 0.20/0.51    inference(avatar_split_clause,[],[f290,f210,f101,f131])).
% 0.20/0.51  fof(f210,plain,(
% 0.20/0.51    spl10_22 <=> ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.20/0.51  fof(f290,plain,(
% 0.20/0.51    ~m1_pre_topc(sK2,sK0) | (~spl10_1 | ~spl10_22)),
% 0.20/0.51    inference(resolution,[],[f211,f103])).
% 0.20/0.51  fof(f211,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0)) ) | ~spl10_22),
% 0.20/0.51    inference(avatar_component_clause,[],[f210])).
% 0.20/0.51  fof(f279,plain,(
% 0.20/0.51    ~spl10_28 | spl10_32 | ~spl10_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f267,f151,f277,f252])).
% 0.20/0.51  fof(f252,plain,(
% 0.20/0.51    spl10_28 <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    spl10_11 <=> sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.20/0.51  fof(f267,plain,(
% 0.20/0.51    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != sK3 | ~m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | u1_pre_topc(sK2) = X1) ) | ~spl10_11),
% 0.20/0.51    inference(superposition,[],[f95,f153])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~spl10_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f151])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | X1 = X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.20/0.51  fof(f275,plain,(
% 0.20/0.51    ~spl10_26 | spl10_28),
% 0.20/0.51    inference(avatar_split_clause,[],[f273,f252,f236])).
% 0.20/0.51  fof(f273,plain,(
% 0.20/0.51    ~l1_pre_topc(sK2) | spl10_28),
% 0.20/0.51    inference(resolution,[],[f254,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.20/0.51  fof(f254,plain,(
% 0.20/0.51    ~m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | spl10_28),
% 0.20/0.51    inference(avatar_component_clause,[],[f252])).
% 0.20/0.51  fof(f258,plain,(
% 0.20/0.51    ~spl10_28 | spl10_29 | ~spl10_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f246,f151,f256,f252])).
% 0.20/0.51  fof(f246,plain,(
% 0.20/0.51    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != sK3 | ~m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | u1_struct_0(sK2) = X0) ) | ~spl10_11),
% 0.20/0.51    inference(superposition,[],[f94,f153])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | X0 = X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f39])).
% 0.20/0.51  fof(f245,plain,(
% 0.20/0.51    ~spl10_1 | ~spl10_7 | spl10_26),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f243])).
% 0.20/0.51  fof(f243,plain,(
% 0.20/0.51    $false | (~spl10_1 | ~spl10_7 | spl10_26)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f103,f133,f238,f82])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.51  fof(f238,plain,(
% 0.20/0.51    ~l1_pre_topc(sK2) | spl10_26),
% 0.20/0.51    inference(avatar_component_clause,[],[f236])).
% 0.20/0.51  fof(f242,plain,(
% 0.20/0.51    ~spl10_26 | spl10_27 | ~spl10_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f233,f151,f240,f236])).
% 0.20/0.51  fof(f233,plain,(
% 0.20/0.51    ( ! [X0] : (m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK2) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,sK2)) ) | ~spl10_11),
% 0.20/0.51    inference(superposition,[],[f81,f153])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.20/0.51  fof(f229,plain,(
% 0.20/0.51    ~spl10_1 | ~spl10_9 | spl10_25),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f227])).
% 0.20/0.51  fof(f227,plain,(
% 0.20/0.51    $false | (~spl10_1 | ~spl10_9 | spl10_25)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f103,f143,f225,f82])).
% 0.20/0.51  fof(f225,plain,(
% 0.20/0.51    ~l1_pre_topc(sK3) | spl10_25),
% 0.20/0.51    inference(avatar_component_clause,[],[f223])).
% 0.20/0.51  fof(f226,plain,(
% 0.20/0.51    spl10_24 | ~spl10_25 | ~spl10_23),
% 0.20/0.51    inference(avatar_split_clause,[],[f217,f213,f223,f219])).
% 0.20/0.51  fof(f213,plain,(
% 0.20/0.51    spl10_23 <=> v1_pre_topc(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    ~l1_pre_topc(sK3) | sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | ~spl10_23),
% 0.20/0.51    inference(resolution,[],[f215,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.20/0.51  fof(f215,plain,(
% 0.20/0.51    v1_pre_topc(sK3) | ~spl10_23),
% 0.20/0.51    inference(avatar_component_clause,[],[f213])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    spl10_22 | spl10_23 | ~spl10_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f208,f151,f213,f210])).
% 0.20/0.51  fof(f208,plain,(
% 0.20/0.51    ( ! [X0] : (v1_pre_topc(sK3) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) ) | ~spl10_11),
% 0.20/0.51    inference(superposition,[],[f84,f153])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).
% 0.20/0.51  fof(f206,plain,(
% 0.20/0.51    spl10_21 | ~spl10_17 | ~spl10_18),
% 0.20/0.51    inference(avatar_split_clause,[],[f201,f186,f181,f203])).
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    spl10_17 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    spl10_18 <=> sK5 = sK6),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.20/0.51  fof(f201,plain,(
% 0.20/0.51    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | (~spl10_17 | ~spl10_18)),
% 0.20/0.51    inference(forward_demodulation,[],[f183,f188])).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    sK5 = sK6 | ~spl10_18),
% 0.20/0.51    inference(avatar_component_clause,[],[f186])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~spl10_17),
% 0.20/0.51    inference(avatar_component_clause,[],[f181])).
% 0.20/0.51  fof(f200,plain,(
% 0.20/0.51    spl10_20 | ~spl10_18 | ~spl10_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f195,f191,f186,f197])).
% 0.20/0.51  fof(f191,plain,(
% 0.20/0.51    spl10_19 <=> m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.20/0.51  fof(f195,plain,(
% 0.20/0.51    m1_subset_1(sK5,u1_struct_0(sK2)) | (~spl10_18 | ~spl10_19)),
% 0.20/0.51    inference(backward_demodulation,[],[f193,f188])).
% 0.20/0.51  fof(f193,plain,(
% 0.20/0.51    m1_subset_1(sK6,u1_struct_0(sK2)) | ~spl10_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f191])).
% 0.20/0.51  fof(f194,plain,(
% 0.20/0.51    spl10_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f40,f191])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.20/0.51    inference(negated_conjecture,[],[f15])).
% 0.20/0.51  fof(f15,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    spl10_18),
% 0.20/0.51    inference(avatar_split_clause,[],[f41,f186])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    sK5 = sK6),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    spl10_17),
% 0.20/0.51    inference(avatar_split_clause,[],[f42,f181])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f179,plain,(
% 0.20/0.51    ~spl10_16),
% 0.20/0.51    inference(avatar_split_clause,[],[f43,f176])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f169,plain,(
% 0.20/0.51    spl10_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f45,f166])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    v1_funct_1(sK4)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f164,plain,(
% 0.20/0.51    spl10_13),
% 0.20/0.51    inference(avatar_split_clause,[],[f46,f161])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f159,plain,(
% 0.20/0.51    spl10_12),
% 0.20/0.51    inference(avatar_split_clause,[],[f47,f156])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    spl10_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f48,f151])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f149,plain,(
% 0.20/0.51    ~spl10_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f49,f146])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ~v2_struct_0(sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    spl10_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f50,f141])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    m1_pre_topc(sK3,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    ~spl10_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f51,f136])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ~v2_struct_0(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    spl10_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f52,f131])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    m1_pre_topc(sK2,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    ~spl10_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f53,f126])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ~v2_struct_0(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    spl10_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f54,f121])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    v2_pre_topc(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    spl10_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f55,f116])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    l1_pre_topc(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ~spl10_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f56,f111])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ~v2_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    spl10_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f57,f106])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    spl10_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f58,f101])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (28661)------------------------------
% 0.20/0.51  % (28661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28661)Termination reason: Refutation
% 0.20/0.51  % (28653)Refutation not found, incomplete strategy% (28653)------------------------------
% 0.20/0.51  % (28653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28653)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (28653)Memory used [KB]: 1918
% 0.20/0.51  % (28653)Time elapsed: 0.084 s
% 0.20/0.51  % (28653)------------------------------
% 0.20/0.51  % (28653)------------------------------
% 0.20/0.51  
% 0.20/0.51  % (28661)Memory used [KB]: 6908
% 0.20/0.51  % (28661)Time elapsed: 0.089 s
% 0.20/0.51  % (28661)------------------------------
% 0.20/0.51  % (28661)------------------------------
% 0.20/0.52  % (28645)Success in time 0.167 s
%------------------------------------------------------------------------------
