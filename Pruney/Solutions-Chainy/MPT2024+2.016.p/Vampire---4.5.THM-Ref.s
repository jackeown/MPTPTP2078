%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:11 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 423 expanded)
%              Number of leaves         :   48 ( 180 expanded)
%              Depth                    :   13
%              Number of atoms          :  741 (1702 expanded)
%              Number of equality atoms :   21 (  79 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1284,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f113,f118,f123,f128,f133,f138,f250,f271,f283,f304,f322,f740,f869,f887,f915,f1007,f1039,f1076,f1108,f1124,f1241,f1257,f1283])).

fof(f1283,plain,
    ( k2_xboole_0(sK8,sK9) != k4_subset_1(u1_struct_0(sK6),sK8,sK9)
    | m1_subset_1(k2_xboole_0(sK8,sK9),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK6),sK8,sK9),k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1257,plain,
    ( spl13_106
    | ~ spl13_79
    | ~ spl13_88 ),
    inference(avatar_split_clause,[],[f1223,f1073,f1004,f1254])).

fof(f1254,plain,
    ( spl13_106
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK6),sK8,sK9),k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_106])])).

fof(f1004,plain,
    ( spl13_79
  <=> m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_79])])).

fof(f1073,plain,
    ( spl13_88
  <=> m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_88])])).

fof(f1223,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK6),sK8,sK9),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl13_79
    | ~ spl13_88 ),
    inference(unit_resulting_resolution,[],[f1006,f1075,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f1075,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl13_88 ),
    inference(avatar_component_clause,[],[f1073])).

fof(f1006,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl13_79 ),
    inference(avatar_component_clause,[],[f1004])).

fof(f1241,plain,
    ( spl13_103
    | ~ spl13_79
    | ~ spl13_88 ),
    inference(avatar_split_clause,[],[f1227,f1073,f1004,f1238])).

fof(f1238,plain,
    ( spl13_103
  <=> k2_xboole_0(sK8,sK9) = k4_subset_1(u1_struct_0(sK6),sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_103])])).

fof(f1227,plain,
    ( k2_xboole_0(sK8,sK9) = k4_subset_1(u1_struct_0(sK6),sK8,sK9)
    | ~ spl13_79
    | ~ spl13_88 ),
    inference(unit_resulting_resolution,[],[f1006,f1075,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1124,plain,
    ( ~ spl13_5
    | ~ spl13_6
    | spl13_15
    | ~ spl13_79
    | ~ spl13_81
    | ~ spl13_88
    | ~ spl13_90 ),
    inference(avatar_contradiction_clause,[],[f1123])).

fof(f1123,plain,
    ( $false
    | ~ spl13_5
    | ~ spl13_6
    | spl13_15
    | ~ spl13_79
    | ~ spl13_81
    | ~ spl13_88
    | ~ spl13_90 ),
    inference(subsumption_resolution,[],[f1122,f132])).

fof(f132,plain,
    ( v2_pre_topc(sK6)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl13_6
  <=> v2_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f1122,plain,
    ( ~ v2_pre_topc(sK6)
    | ~ spl13_5
    | spl13_15
    | ~ spl13_79
    | ~ spl13_81
    | ~ spl13_88
    | ~ spl13_90 ),
    inference(subsumption_resolution,[],[f1121,f127])).

fof(f127,plain,
    ( l1_pre_topc(sK6)
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl13_5
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f1121,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | spl13_15
    | ~ spl13_79
    | ~ spl13_81
    | ~ spl13_88
    | ~ spl13_90 ),
    inference(subsumption_resolution,[],[f1120,f1016])).

fof(f1016,plain,
    ( v3_pre_topc(sK8,sK6)
    | ~ spl13_81 ),
    inference(avatar_component_clause,[],[f1014])).

fof(f1014,plain,
    ( spl13_81
  <=> v3_pre_topc(sK8,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_81])])).

fof(f1120,plain,
    ( ~ v3_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | spl13_15
    | ~ spl13_79
    | ~ spl13_88
    | ~ spl13_90 ),
    inference(subsumption_resolution,[],[f1119,f1006])).

fof(f1119,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | spl13_15
    | ~ spl13_88
    | ~ spl13_90 ),
    inference(subsumption_resolution,[],[f1118,f1085])).

fof(f1085,plain,
    ( v3_pre_topc(sK9,sK6)
    | ~ spl13_90 ),
    inference(avatar_component_clause,[],[f1083])).

fof(f1083,plain,
    ( spl13_90
  <=> v3_pre_topc(sK9,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_90])])).

fof(f1118,plain,
    ( ~ v3_pre_topc(sK9,sK6)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | spl13_15
    | ~ spl13_88 ),
    inference(subsumption_resolution,[],[f1116,f1075])).

fof(f1116,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_pre_topc(sK9,sK6)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | spl13_15 ),
    inference(resolution,[],[f90,f282])).

fof(f282,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK8,sK9),sK6)
    | spl13_15 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl13_15
  <=> v3_pre_topc(k2_xboole_0(sK8,sK9),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).

fof(f1108,plain,
    ( spl13_90
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f1065,f911,f1083])).

fof(f911,plain,
    ( spl13_72
  <=> sP2(sK6,sK7,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_72])])).

fof(f1065,plain,
    ( v3_pre_topc(sK9,sK6)
    | ~ spl13_72 ),
    inference(resolution,[],[f913,f175])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | v3_pre_topc(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ sP2(X0,X1,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(superposition,[],[f81,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sK10(X0,X1,X2) = X2
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( v3_pre_topc(sK10(X0,X1,X2),X0)
        & r2_hidden(X1,sK10(X0,X1,X2))
        & sK10(X0,X1,X2) = X2
        & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( v3_pre_topc(X3,X0)
          & r2_hidden(X1,X3)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_pre_topc(sK10(X0,X1,X2),X0)
        & r2_hidden(X1,sK10(X0,X1,X2))
        & sK10(X0,X1,X2) = X2
        & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( v3_pre_topc(X3,X0)
          & r2_hidden(X1,X3)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( v3_pre_topc(X3,X0)
          & r2_hidden(X1,X3)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP2(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK10(X0,X1,X2),X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f913,plain,
    ( sP2(sK6,sK7,sK9)
    | ~ spl13_72 ),
    inference(avatar_component_clause,[],[f911])).

fof(f1076,plain,
    ( spl13_88
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f1060,f911,f1073])).

fof(f1060,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl13_72 ),
    inference(unit_resulting_resolution,[],[f913,f203])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP2(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP2(X0,X1,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(superposition,[],[f78,f79])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1039,plain,
    ( spl13_81
    | ~ spl13_71 ),
    inference(avatar_split_clause,[],[f996,f883,f1014])).

fof(f883,plain,
    ( spl13_71
  <=> sP2(sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_71])])).

fof(f996,plain,
    ( v3_pre_topc(sK8,sK6)
    | ~ spl13_71 ),
    inference(resolution,[],[f885,f175])).

fof(f885,plain,
    ( sP2(sK6,sK7,sK8)
    | ~ spl13_71 ),
    inference(avatar_component_clause,[],[f883])).

fof(f1007,plain,
    ( spl13_79
    | ~ spl13_71 ),
    inference(avatar_split_clause,[],[f991,f883,f1004])).

fof(f991,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl13_71 ),
    inference(unit_resulting_resolution,[],[f885,f203])).

fof(f915,plain,
    ( spl13_72
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7 ),
    inference(avatar_split_clause,[],[f816,f135,f130,f125,f120,f110,f911])).

fof(f110,plain,
    ( spl13_2
  <=> m1_subset_1(sK9,u1_struct_0(k9_yellow_6(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f120,plain,
    ( spl13_4
  <=> m1_subset_1(sK7,u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f135,plain,
    ( spl13_7
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f816,plain,
    ( sP2(sK6,sK7,sK9)
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7 ),
    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f112,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | sP2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f18,f32])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_6)).

fof(f112,plain,
    ( m1_subset_1(sK9,u1_struct_0(k9_yellow_6(sK6,sK7)))
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f122,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f137,plain,
    ( ~ v2_struct_0(sK6)
    | spl13_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f887,plain,
    ( spl13_71
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7 ),
    inference(avatar_split_clause,[],[f822,f135,f130,f125,f120,f115,f883])).

fof(f115,plain,
    ( spl13_3
  <=> m1_subset_1(sK8,u1_struct_0(k9_yellow_6(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f822,plain,
    ( sP2(sK6,sK7,sK8)
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7 ),
    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f117,f82])).

fof(f117,plain,
    ( m1_subset_1(sK8,u1_struct_0(k9_yellow_6(sK6,sK7)))
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f869,plain,
    ( ~ spl13_3
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | spl13_18 ),
    inference(avatar_contradiction_clause,[],[f868])).

fof(f868,plain,
    ( $false
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | spl13_18 ),
    inference(subsumption_resolution,[],[f867,f137])).

fof(f867,plain,
    ( v2_struct_0(sK6)
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_18 ),
    inference(subsumption_resolution,[],[f866,f132])).

fof(f866,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_5
    | spl13_18 ),
    inference(subsumption_resolution,[],[f865,f127])).

fof(f865,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ spl13_3
    | ~ spl13_4
    | spl13_18 ),
    inference(subsumption_resolution,[],[f864,f122])).

fof(f864,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ spl13_3
    | spl13_18 ),
    inference(subsumption_resolution,[],[f829,f327])).

fof(f327,plain,
    ( ! [X0] : ~ sP2(X0,sK7,sK8)
    | spl13_18 ),
    inference(unit_resulting_resolution,[],[f314,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ sP2(X0,X1,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(superposition,[],[f80,f79])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK10(X0,X1,X2))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f314,plain,
    ( ~ r2_hidden(sK7,sK8)
    | spl13_18 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl13_18
  <=> r2_hidden(sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f829,plain,
    ( sP2(sK6,sK7,sK8)
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ spl13_3 ),
    inference(resolution,[],[f82,f117])).

fof(f740,plain,
    ( ~ spl13_65
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | spl13_12 ),
    inference(avatar_split_clause,[],[f729,f264,f135,f130,f125,f120,f737])).

fof(f737,plain,
    ( spl13_65
  <=> m1_subset_1(k2_xboole_0(sK8,sK9),k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_65])])).

fof(f264,plain,
    ( spl13_12
  <=> sP1(sK7,k2_xboole_0(sK8,sK9),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f729,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK8,sK9),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_6
    | spl13_7
    | spl13_12 ),
    inference(unit_resulting_resolution,[],[f137,f132,f127,f266,f122,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X1,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f16,f30,f29])).

fof(f29,plain,(
    ! [X0,X2,X1] :
      ( sP0(X0,X2,X1)
    <=> ( v3_pre_topc(X2,X0)
        & r2_hidden(X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ! [X1,X2,X0] :
      ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      <=> sP0(X0,X2,X1) )
      | ~ sP1(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f266,plain,
    ( ~ sP1(sK7,k2_xboole_0(sK8,sK9),sK6)
    | spl13_12 ),
    inference(avatar_component_clause,[],[f264])).

fof(f322,plain,
    ( ~ spl13_18
    | spl13_17 ),
    inference(avatar_split_clause,[],[f310,f299,f312])).

fof(f299,plain,
    ( spl13_17
  <=> sP4(sK9,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f310,plain,
    ( ~ r2_hidden(sK7,sK8)
    | spl13_17 ),
    inference(resolution,[],[f301,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X1,X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ~ r2_hidden(X1,X0)
          & ~ r2_hidden(X1,X2) ) )
      & ( r2_hidden(X1,X0)
        | r2_hidden(X1,X2)
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X1,X3,X0] :
      ( ( sP4(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP4(X1,X3,X0) ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X1,X3,X0] :
      ( ( sP4(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP4(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X1,X3,X0] :
      ( sP4(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f301,plain,
    ( ~ sP4(sK9,sK7,sK8)
    | spl13_17 ),
    inference(avatar_component_clause,[],[f299])).

fof(f304,plain,
    ( ~ spl13_17
    | spl13_14 ),
    inference(avatar_split_clause,[],[f290,f276,f299])).

fof(f276,plain,
    ( spl13_14
  <=> r2_hidden(sK7,k2_xboole_0(sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f290,plain,
    ( ~ sP4(sK9,sK7,sK8)
    | spl13_14 ),
    inference(resolution,[],[f278,f194])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_xboole_0(X2,X0))
      | ~ sP4(X0,X1,X2) ) ),
    inference(resolution,[],[f95,f103])).

fof(f103,plain,(
    ! [X0,X1] : sP5(X0,X1,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( sP5(X0,X1,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP5(X0,X1,X2) )
      & ( sP5(X0,X1,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP5(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f37,f36])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( sP5(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP4(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ sP4(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ( ( ~ sP4(X1,sK12(X0,X1,X2),X0)
            | ~ r2_hidden(sK12(X0,X1,X2),X2) )
          & ( sP4(X1,sK12(X0,X1,X2),X0)
            | r2_hidden(sK12(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP4(X1,X4,X0) )
            & ( sP4(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f58,f59])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP4(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP4(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP4(X1,sK12(X0,X1,X2),X0)
          | ~ r2_hidden(sK12(X0,X1,X2),X2) )
        & ( sP4(X1,sK12(X0,X1,X2),X0)
          | r2_hidden(sK12(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP4(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP4(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP4(X1,X4,X0) )
            & ( sP4(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP4(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP4(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP4(X1,X3,X0) )
            & ( sP4(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f278,plain,
    ( ~ r2_hidden(sK7,k2_xboole_0(sK8,sK9))
    | spl13_14 ),
    inference(avatar_component_clause,[],[f276])).

fof(f283,plain,
    ( ~ spl13_14
    | ~ spl13_15
    | spl13_13 ),
    inference(avatar_split_clause,[],[f273,f268,f280,f276])).

fof(f268,plain,
    ( spl13_13
  <=> sP0(sK6,k2_xboole_0(sK8,sK9),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f273,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK8,sK9),sK6)
    | ~ r2_hidden(sK7,k2_xboole_0(sK8,sK9))
    | spl13_13 ),
    inference(resolution,[],[f270,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ v3_pre_topc(X1,X0)
        | ~ r2_hidden(X2,X1) )
      & ( ( v3_pre_topc(X1,X0)
          & r2_hidden(X2,X1) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X2,X1)
        | ~ v3_pre_topc(X2,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( v3_pre_topc(X2,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X2,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X2,X1)
        | ~ v3_pre_topc(X2,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( v3_pre_topc(X2,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f270,plain,
    ( ~ sP0(sK6,k2_xboole_0(sK8,sK9),sK7)
    | spl13_13 ),
    inference(avatar_component_clause,[],[f268])).

fof(f271,plain,
    ( ~ spl13_12
    | ~ spl13_13
    | spl13_10 ),
    inference(avatar_split_clause,[],[f255,f244,f268,f264])).

fof(f244,plain,
    ( spl13_10
  <=> r2_hidden(k2_xboole_0(sK8,sK9),u1_struct_0(k9_yellow_6(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f255,plain,
    ( ~ sP0(sK6,k2_xboole_0(sK8,sK9),sK7)
    | ~ sP1(sK7,k2_xboole_0(sK8,sK9),sK6)
    | spl13_10 ),
    inference(resolution,[],[f246,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0)))
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0)))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X1,X2,X0] :
      ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
          | ~ sP0(X0,X2,X1) )
        & ( sP0(X0,X2,X1)
          | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
      | ~ sP1(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f246,plain,
    ( ~ r2_hidden(k2_xboole_0(sK8,sK9),u1_struct_0(k9_yellow_6(sK6,sK7)))
    | spl13_10 ),
    inference(avatar_component_clause,[],[f244])).

fof(f250,plain,
    ( ~ spl13_10
    | spl13_1 ),
    inference(avatar_split_clause,[],[f241,f105,f244])).

fof(f105,plain,
    ( spl13_1
  <=> m1_subset_1(k2_xboole_0(sK8,sK9),u1_struct_0(k9_yellow_6(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f241,plain,
    ( ~ r2_hidden(k2_xboole_0(sK8,sK9),u1_struct_0(k9_yellow_6(sK6,sK7)))
    | spl13_1 ),
    inference(resolution,[],[f233,f184])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(k9_yellow_6(sK6,sK7)))
        | ~ r2_hidden(k2_xboole_0(sK8,sK9),X0) )
    | spl13_1 ),
    inference(resolution,[],[f180,f107])).

fof(f107,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK8,sK9),u1_struct_0(k9_yellow_6(sK6,sK7)))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X2)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f91,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f233,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(unit_resulting_resolution,[],[f139,f179,f139,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X1,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | sP3(X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_folding,[],[f20,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(f179,plain,(
    ! [X0,X1] : ~ sP3(X0,X0,X1) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X0,X1)
      | ~ sP3(X0,X0,X1) ) ),
    inference(resolution,[],[f86,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK11(X0,X1,X2),X1)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(sK11(X0,X1,X2),X0)
        & r2_hidden(sK11(X0,X1,X2),X1)
        & m1_subset_1(sK11(X0,X1,X2),X2) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f53,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X2) )
     => ( ~ r2_hidden(sK11(X0,X1,X2),X0)
        & r2_hidden(sK11(X0,X1,X2),X1)
        & m1_subset_1(sK11(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X2) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
      | ~ sP3(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK11(X0,X1,X2),X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f139,plain,(
    ! [X0,X1] : m1_subset_1(X0,k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f83,f89])).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f138,plain,(
    ~ spl13_7 ),
    inference(avatar_split_clause,[],[f65,f135])).

fof(f65,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK8,sK9),u1_struct_0(k9_yellow_6(sK6,sK7)))
    & m1_subset_1(sK9,u1_struct_0(k9_yellow_6(sK6,sK7)))
    & m1_subset_1(sK8,u1_struct_0(k9_yellow_6(sK6,sK7)))
    & m1_subset_1(sK7,u1_struct_0(sK6))
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f14,f42,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                    & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK6,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK6,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK6,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK6)) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK6,X1)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK6,X1))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK6,X1))) )
        & m1_subset_1(X1,u1_struct_0(sK6)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK6,sK7)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK6,sK7))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK6,sK7))) )
      & m1_subset_1(sK7,u1_struct_0(sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK6,sK7)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK6,sK7))) )
        & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK6,sK7))) )
   => ( ? [X3] :
          ( ~ m1_subset_1(k2_xboole_0(sK8,X3),u1_struct_0(k9_yellow_6(sK6,sK7)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK6,sK7))) )
      & m1_subset_1(sK8,u1_struct_0(k9_yellow_6(sK6,sK7))) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X3] :
        ( ~ m1_subset_1(k2_xboole_0(sK8,X3),u1_struct_0(k9_yellow_6(sK6,sK7)))
        & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK6,sK7))) )
   => ( ~ m1_subset_1(k2_xboole_0(sK8,sK9),u1_struct_0(k9_yellow_6(sK6,sK7)))
      & m1_subset_1(sK9,u1_struct_0(k9_yellow_6(sK6,sK7))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).

fof(f133,plain,(
    spl13_6 ),
    inference(avatar_split_clause,[],[f66,f130])).

fof(f66,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f128,plain,(
    spl13_5 ),
    inference(avatar_split_clause,[],[f67,f125])).

fof(f67,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f123,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f68,f120])).

fof(f68,plain,(
    m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f43])).

fof(f118,plain,(
    spl13_3 ),
    inference(avatar_split_clause,[],[f69,f115])).

fof(f69,plain,(
    m1_subset_1(sK8,u1_struct_0(k9_yellow_6(sK6,sK7))) ),
    inference(cnf_transformation,[],[f43])).

fof(f113,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f70,f110])).

fof(f70,plain,(
    m1_subset_1(sK9,u1_struct_0(k9_yellow_6(sK6,sK7))) ),
    inference(cnf_transformation,[],[f43])).

fof(f108,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f71,f105])).

fof(f71,plain,(
    ~ m1_subset_1(k2_xboole_0(sK8,sK9),u1_struct_0(k9_yellow_6(sK6,sK7))) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:14:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (24462)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  % (24469)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.47  % (24461)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (24468)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (24460)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (24456)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (24470)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (24465)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (24474)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (24463)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (24455)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (24464)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (24459)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (24466)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (24456)Refutation not found, incomplete strategy% (24456)------------------------------
% 0.22/0.51  % (24456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (24456)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (24456)Memory used [KB]: 10618
% 0.22/0.51  % (24456)Time elapsed: 0.095 s
% 0.22/0.51  % (24456)------------------------------
% 0.22/0.51  % (24456)------------------------------
% 0.22/0.51  % (24457)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (24475)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (24458)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (24475)Refutation not found, incomplete strategy% (24475)------------------------------
% 0.22/0.51  % (24475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (24475)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (24475)Memory used [KB]: 10618
% 0.22/0.51  % (24475)Time elapsed: 0.097 s
% 0.22/0.51  % (24475)------------------------------
% 0.22/0.51  % (24475)------------------------------
% 0.22/0.51  % (24472)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % (24467)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.52  % (24473)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.29/0.54  % (24471)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.47/0.57  % (24471)Refutation found. Thanks to Tanya!
% 1.47/0.57  % SZS status Theorem for theBenchmark
% 1.47/0.57  % SZS output start Proof for theBenchmark
% 1.47/0.57  fof(f1284,plain,(
% 1.47/0.57    $false),
% 1.47/0.57    inference(avatar_sat_refutation,[],[f108,f113,f118,f123,f128,f133,f138,f250,f271,f283,f304,f322,f740,f869,f887,f915,f1007,f1039,f1076,f1108,f1124,f1241,f1257,f1283])).
% 1.47/0.57  fof(f1283,plain,(
% 1.47/0.57    k2_xboole_0(sK8,sK9) != k4_subset_1(u1_struct_0(sK6),sK8,sK9) | m1_subset_1(k2_xboole_0(sK8,sK9),k1_zfmisc_1(u1_struct_0(sK6))) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK6),sK8,sK9),k1_zfmisc_1(u1_struct_0(sK6)))),
% 1.47/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.47/0.57  fof(f1257,plain,(
% 1.47/0.57    spl13_106 | ~spl13_79 | ~spl13_88),
% 1.47/0.57    inference(avatar_split_clause,[],[f1223,f1073,f1004,f1254])).
% 1.47/0.57  fof(f1254,plain,(
% 1.47/0.57    spl13_106 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK6),sK8,sK9),k1_zfmisc_1(u1_struct_0(sK6)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_106])])).
% 1.47/0.57  fof(f1004,plain,(
% 1.47/0.57    spl13_79 <=> m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_79])])).
% 1.47/0.57  fof(f1073,plain,(
% 1.47/0.57    spl13_88 <=> m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_88])])).
% 1.47/0.57  fof(f1223,plain,(
% 1.47/0.57    m1_subset_1(k4_subset_1(u1_struct_0(sK6),sK8,sK9),k1_zfmisc_1(u1_struct_0(sK6))) | (~spl13_79 | ~spl13_88)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f1006,f1075,f92])).
% 1.47/0.57  fof(f92,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f26])).
% 1.47/0.57  fof(f26,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.47/0.57    inference(flattening,[],[f25])).
% 1.47/0.57  fof(f25,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.47/0.57    inference(ennf_transformation,[],[f3])).
% 1.47/0.57  fof(f3,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 1.47/0.57  fof(f1075,plain,(
% 1.47/0.57    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) | ~spl13_88),
% 1.47/0.57    inference(avatar_component_clause,[],[f1073])).
% 1.47/0.57  fof(f1006,plain,(
% 1.47/0.57    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) | ~spl13_79),
% 1.47/0.57    inference(avatar_component_clause,[],[f1004])).
% 1.47/0.57  fof(f1241,plain,(
% 1.47/0.57    spl13_103 | ~spl13_79 | ~spl13_88),
% 1.47/0.57    inference(avatar_split_clause,[],[f1227,f1073,f1004,f1238])).
% 1.47/0.57  fof(f1238,plain,(
% 1.47/0.57    spl13_103 <=> k2_xboole_0(sK8,sK9) = k4_subset_1(u1_struct_0(sK6),sK8,sK9)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_103])])).
% 1.47/0.57  fof(f1227,plain,(
% 1.47/0.57    k2_xboole_0(sK8,sK9) = k4_subset_1(u1_struct_0(sK6),sK8,sK9) | (~spl13_79 | ~spl13_88)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f1006,f1075,f93])).
% 1.47/0.57  fof(f93,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f28])).
% 1.47/0.57  fof(f28,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.47/0.57    inference(flattening,[],[f27])).
% 1.47/0.57  fof(f27,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.47/0.57    inference(ennf_transformation,[],[f4])).
% 1.47/0.57  fof(f4,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.47/0.57  fof(f1124,plain,(
% 1.47/0.57    ~spl13_5 | ~spl13_6 | spl13_15 | ~spl13_79 | ~spl13_81 | ~spl13_88 | ~spl13_90),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f1123])).
% 1.47/0.57  fof(f1123,plain,(
% 1.47/0.57    $false | (~spl13_5 | ~spl13_6 | spl13_15 | ~spl13_79 | ~spl13_81 | ~spl13_88 | ~spl13_90)),
% 1.47/0.57    inference(subsumption_resolution,[],[f1122,f132])).
% 1.47/0.57  fof(f132,plain,(
% 1.47/0.57    v2_pre_topc(sK6) | ~spl13_6),
% 1.47/0.57    inference(avatar_component_clause,[],[f130])).
% 1.47/0.57  fof(f130,plain,(
% 1.47/0.57    spl13_6 <=> v2_pre_topc(sK6)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).
% 1.47/0.57  fof(f1122,plain,(
% 1.47/0.57    ~v2_pre_topc(sK6) | (~spl13_5 | spl13_15 | ~spl13_79 | ~spl13_81 | ~spl13_88 | ~spl13_90)),
% 1.47/0.57    inference(subsumption_resolution,[],[f1121,f127])).
% 1.47/0.57  fof(f127,plain,(
% 1.47/0.57    l1_pre_topc(sK6) | ~spl13_5),
% 1.47/0.57    inference(avatar_component_clause,[],[f125])).
% 1.47/0.57  fof(f125,plain,(
% 1.47/0.57    spl13_5 <=> l1_pre_topc(sK6)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).
% 1.47/0.57  fof(f1121,plain,(
% 1.47/0.57    ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | (spl13_15 | ~spl13_79 | ~spl13_81 | ~spl13_88 | ~spl13_90)),
% 1.47/0.57    inference(subsumption_resolution,[],[f1120,f1016])).
% 1.47/0.57  fof(f1016,plain,(
% 1.47/0.57    v3_pre_topc(sK8,sK6) | ~spl13_81),
% 1.47/0.57    inference(avatar_component_clause,[],[f1014])).
% 1.47/0.57  fof(f1014,plain,(
% 1.47/0.57    spl13_81 <=> v3_pre_topc(sK8,sK6)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_81])])).
% 1.47/0.57  fof(f1120,plain,(
% 1.47/0.57    ~v3_pre_topc(sK8,sK6) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | (spl13_15 | ~spl13_79 | ~spl13_88 | ~spl13_90)),
% 1.47/0.57    inference(subsumption_resolution,[],[f1119,f1006])).
% 1.47/0.57  fof(f1119,plain,(
% 1.47/0.57    ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) | ~v3_pre_topc(sK8,sK6) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | (spl13_15 | ~spl13_88 | ~spl13_90)),
% 1.47/0.57    inference(subsumption_resolution,[],[f1118,f1085])).
% 1.47/0.57  fof(f1085,plain,(
% 1.47/0.57    v3_pre_topc(sK9,sK6) | ~spl13_90),
% 1.47/0.57    inference(avatar_component_clause,[],[f1083])).
% 1.47/0.57  fof(f1083,plain,(
% 1.47/0.57    spl13_90 <=> v3_pre_topc(sK9,sK6)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_90])])).
% 1.47/0.57  fof(f1118,plain,(
% 1.47/0.57    ~v3_pre_topc(sK9,sK6) | ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) | ~v3_pre_topc(sK8,sK6) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | (spl13_15 | ~spl13_88)),
% 1.47/0.57    inference(subsumption_resolution,[],[f1116,f1075])).
% 1.47/0.57  fof(f1116,plain,(
% 1.47/0.57    ~m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) | ~v3_pre_topc(sK9,sK6) | ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) | ~v3_pre_topc(sK8,sK6) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | spl13_15),
% 1.47/0.57    inference(resolution,[],[f90,f282])).
% 1.47/0.57  fof(f282,plain,(
% 1.47/0.57    ~v3_pre_topc(k2_xboole_0(sK8,sK9),sK6) | spl13_15),
% 1.47/0.57    inference(avatar_component_clause,[],[f280])).
% 1.47/0.57  fof(f280,plain,(
% 1.47/0.57    spl13_15 <=> v3_pre_topc(k2_xboole_0(sK8,sK9),sK6)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).
% 1.47/0.57  fof(f90,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f22])).
% 1.47/0.57  fof(f22,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.47/0.57    inference(flattening,[],[f21])).
% 1.47/0.57  fof(f21,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f8])).
% 1.47/0.57  fof(f8,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).
% 1.47/0.57  fof(f1108,plain,(
% 1.47/0.57    spl13_90 | ~spl13_72),
% 1.47/0.57    inference(avatar_split_clause,[],[f1065,f911,f1083])).
% 1.47/0.57  fof(f911,plain,(
% 1.47/0.57    spl13_72 <=> sP2(sK6,sK7,sK9)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_72])])).
% 1.47/0.57  fof(f1065,plain,(
% 1.47/0.57    v3_pre_topc(sK9,sK6) | ~spl13_72),
% 1.47/0.57    inference(resolution,[],[f913,f175])).
% 1.47/0.57  fof(f175,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | v3_pre_topc(X2,X0)) )),
% 1.47/0.57    inference(duplicate_literal_removal,[],[f174])).
% 1.47/0.57  fof(f174,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~sP2(X0,X1,X2) | ~sP2(X0,X1,X2)) )),
% 1.47/0.57    inference(superposition,[],[f81,f79])).
% 1.47/0.57  fof(f79,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (sK10(X0,X1,X2) = X2 | ~sP2(X0,X1,X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f51])).
% 1.47/0.57  fof(f51,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((v3_pre_topc(sK10(X0,X1,X2),X0) & r2_hidden(X1,sK10(X0,X1,X2)) & sK10(X0,X1,X2) = X2 & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~sP2(X0,X1,X2))),
% 1.47/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f49,f50])).
% 1.47/0.57  fof(f50,plain,(
% 1.47/0.57    ! [X2,X1,X0] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_pre_topc(sK10(X0,X1,X2),X0) & r2_hidden(X1,sK10(X0,X1,X2)) & sK10(X0,X1,X2) = X2 & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f49,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP2(X0,X1,X2))),
% 1.47/0.57    inference(nnf_transformation,[],[f32])).
% 1.47/0.57  fof(f32,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP2(X0,X1,X2))),
% 1.47/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.47/0.57  fof(f81,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (v3_pre_topc(sK10(X0,X1,X2),X0) | ~sP2(X0,X1,X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f51])).
% 1.47/0.57  fof(f913,plain,(
% 1.47/0.57    sP2(sK6,sK7,sK9) | ~spl13_72),
% 1.47/0.57    inference(avatar_component_clause,[],[f911])).
% 1.47/0.57  fof(f1076,plain,(
% 1.47/0.57    spl13_88 | ~spl13_72),
% 1.47/0.57    inference(avatar_split_clause,[],[f1060,f911,f1073])).
% 1.47/0.57  fof(f1060,plain,(
% 1.47/0.57    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) | ~spl13_72),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f913,f203])).
% 1.47/0.57  fof(f203,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~sP2(X0,X1,X2)) )),
% 1.47/0.57    inference(duplicate_literal_removal,[],[f202])).
% 1.47/0.57  fof(f202,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~sP2(X0,X1,X2) | ~sP2(X0,X1,X2)) )),
% 1.47/0.57    inference(superposition,[],[f78,f79])).
% 1.47/0.57  fof(f78,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~sP2(X0,X1,X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f51])).
% 1.47/0.57  fof(f1039,plain,(
% 1.47/0.57    spl13_81 | ~spl13_71),
% 1.47/0.57    inference(avatar_split_clause,[],[f996,f883,f1014])).
% 1.47/0.57  fof(f883,plain,(
% 1.47/0.57    spl13_71 <=> sP2(sK6,sK7,sK8)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_71])])).
% 1.47/0.57  fof(f996,plain,(
% 1.47/0.57    v3_pre_topc(sK8,sK6) | ~spl13_71),
% 1.47/0.57    inference(resolution,[],[f885,f175])).
% 1.47/0.57  fof(f885,plain,(
% 1.47/0.57    sP2(sK6,sK7,sK8) | ~spl13_71),
% 1.47/0.57    inference(avatar_component_clause,[],[f883])).
% 1.47/0.57  fof(f1007,plain,(
% 1.47/0.57    spl13_79 | ~spl13_71),
% 1.47/0.57    inference(avatar_split_clause,[],[f991,f883,f1004])).
% 1.47/0.57  fof(f991,plain,(
% 1.47/0.57    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) | ~spl13_71),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f885,f203])).
% 1.47/0.57  fof(f915,plain,(
% 1.47/0.57    spl13_72 | ~spl13_2 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7),
% 1.47/0.57    inference(avatar_split_clause,[],[f816,f135,f130,f125,f120,f110,f911])).
% 1.47/0.57  fof(f110,plain,(
% 1.47/0.57    spl13_2 <=> m1_subset_1(sK9,u1_struct_0(k9_yellow_6(sK6,sK7)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 1.47/0.57  fof(f120,plain,(
% 1.47/0.57    spl13_4 <=> m1_subset_1(sK7,u1_struct_0(sK6))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 1.47/0.57  fof(f135,plain,(
% 1.47/0.57    spl13_7 <=> v2_struct_0(sK6)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).
% 1.47/0.57  fof(f816,plain,(
% 1.47/0.57    sP2(sK6,sK7,sK9) | (~spl13_2 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f112,f82])).
% 1.47/0.57  fof(f82,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | sP2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f33])).
% 1.47/0.57  fof(f33,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (! [X2] : (sP2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.57    inference(definition_folding,[],[f18,f32])).
% 1.47/0.57  fof(f18,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.57    inference(flattening,[],[f17])).
% 1.47/0.57  fof(f17,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f9])).
% 1.47/0.57  fof(f9,axiom,(
% 1.47/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_6)).
% 1.47/0.57  fof(f112,plain,(
% 1.47/0.57    m1_subset_1(sK9,u1_struct_0(k9_yellow_6(sK6,sK7))) | ~spl13_2),
% 1.47/0.57    inference(avatar_component_clause,[],[f110])).
% 1.47/0.57  fof(f122,plain,(
% 1.47/0.57    m1_subset_1(sK7,u1_struct_0(sK6)) | ~spl13_4),
% 1.47/0.57    inference(avatar_component_clause,[],[f120])).
% 1.47/0.57  fof(f137,plain,(
% 1.47/0.57    ~v2_struct_0(sK6) | spl13_7),
% 1.47/0.57    inference(avatar_component_clause,[],[f135])).
% 1.47/0.57  fof(f887,plain,(
% 1.47/0.57    spl13_71 | ~spl13_3 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7),
% 1.47/0.57    inference(avatar_split_clause,[],[f822,f135,f130,f125,f120,f115,f883])).
% 1.47/0.57  fof(f115,plain,(
% 1.47/0.57    spl13_3 <=> m1_subset_1(sK8,u1_struct_0(k9_yellow_6(sK6,sK7)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 1.47/0.57  fof(f822,plain,(
% 1.47/0.57    sP2(sK6,sK7,sK8) | (~spl13_3 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f117,f82])).
% 1.47/0.57  fof(f117,plain,(
% 1.47/0.57    m1_subset_1(sK8,u1_struct_0(k9_yellow_6(sK6,sK7))) | ~spl13_3),
% 1.47/0.57    inference(avatar_component_clause,[],[f115])).
% 1.47/0.57  fof(f869,plain,(
% 1.47/0.57    ~spl13_3 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | spl13_18),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f868])).
% 1.47/0.57  fof(f868,plain,(
% 1.47/0.57    $false | (~spl13_3 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | spl13_18)),
% 1.47/0.57    inference(subsumption_resolution,[],[f867,f137])).
% 1.47/0.57  fof(f867,plain,(
% 1.47/0.57    v2_struct_0(sK6) | (~spl13_3 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_18)),
% 1.47/0.57    inference(subsumption_resolution,[],[f866,f132])).
% 1.47/0.57  fof(f866,plain,(
% 1.47/0.57    ~v2_pre_topc(sK6) | v2_struct_0(sK6) | (~spl13_3 | ~spl13_4 | ~spl13_5 | spl13_18)),
% 1.47/0.57    inference(subsumption_resolution,[],[f865,f127])).
% 1.47/0.57  fof(f865,plain,(
% 1.47/0.57    ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | (~spl13_3 | ~spl13_4 | spl13_18)),
% 1.47/0.57    inference(subsumption_resolution,[],[f864,f122])).
% 1.47/0.57  fof(f864,plain,(
% 1.47/0.57    ~m1_subset_1(sK7,u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | (~spl13_3 | spl13_18)),
% 1.47/0.57    inference(subsumption_resolution,[],[f829,f327])).
% 1.47/0.57  fof(f327,plain,(
% 1.47/0.57    ( ! [X0] : (~sP2(X0,sK7,sK8)) ) | spl13_18),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f314,f173])).
% 1.47/0.57  fof(f173,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 1.47/0.57    inference(duplicate_literal_removal,[],[f172])).
% 1.47/0.57  fof(f172,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~sP2(X0,X1,X2) | ~sP2(X0,X1,X2)) )),
% 1.47/0.57    inference(superposition,[],[f80,f79])).
% 1.47/0.57  fof(f80,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (r2_hidden(X1,sK10(X0,X1,X2)) | ~sP2(X0,X1,X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f51])).
% 1.47/0.57  fof(f314,plain,(
% 1.47/0.57    ~r2_hidden(sK7,sK8) | spl13_18),
% 1.47/0.57    inference(avatar_component_clause,[],[f312])).
% 1.47/0.57  fof(f312,plain,(
% 1.47/0.57    spl13_18 <=> r2_hidden(sK7,sK8)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).
% 1.47/0.57  fof(f829,plain,(
% 1.47/0.57    sP2(sK6,sK7,sK8) | ~m1_subset_1(sK7,u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~spl13_3),
% 1.47/0.57    inference(resolution,[],[f82,f117])).
% 1.47/0.57  fof(f740,plain,(
% 1.47/0.57    ~spl13_65 | ~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | spl13_12),
% 1.47/0.57    inference(avatar_split_clause,[],[f729,f264,f135,f130,f125,f120,f737])).
% 1.47/0.57  fof(f737,plain,(
% 1.47/0.57    spl13_65 <=> m1_subset_1(k2_xboole_0(sK8,sK9),k1_zfmisc_1(u1_struct_0(sK6)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_65])])).
% 1.47/0.57  fof(f264,plain,(
% 1.47/0.57    spl13_12 <=> sP1(sK7,k2_xboole_0(sK8,sK9),sK6)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).
% 1.47/0.57  fof(f729,plain,(
% 1.47/0.57    ~m1_subset_1(k2_xboole_0(sK8,sK9),k1_zfmisc_1(u1_struct_0(sK6))) | (~spl13_4 | ~spl13_5 | ~spl13_6 | spl13_7 | spl13_12)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f137,f132,f127,f266,f122,f77])).
% 1.47/0.57  fof(f77,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X1,X2,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f31])).
% 1.47/0.57  fof(f31,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (! [X2] : (sP1(X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.57    inference(definition_folding,[],[f16,f30,f29])).
% 1.47/0.57  fof(f29,plain,(
% 1.47/0.57    ! [X0,X2,X1] : (sP0(X0,X2,X1) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2)))),
% 1.47/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.47/0.57  fof(f30,plain,(
% 1.47/0.57    ! [X1,X2,X0] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> sP0(X0,X2,X1)) | ~sP1(X1,X2,X0))),
% 1.47/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.47/0.57  fof(f16,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.57    inference(flattening,[],[f15])).
% 1.47/0.57  fof(f15,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f10])).
% 1.47/0.57  fof(f10,axiom,(
% 1.47/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).
% 1.47/0.57  fof(f266,plain,(
% 1.47/0.57    ~sP1(sK7,k2_xboole_0(sK8,sK9),sK6) | spl13_12),
% 1.47/0.57    inference(avatar_component_clause,[],[f264])).
% 1.47/0.57  fof(f322,plain,(
% 1.47/0.57    ~spl13_18 | spl13_17),
% 1.47/0.57    inference(avatar_split_clause,[],[f310,f299,f312])).
% 1.47/0.57  fof(f299,plain,(
% 1.47/0.57    spl13_17 <=> sP4(sK9,sK7,sK8)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).
% 1.47/0.57  fof(f310,plain,(
% 1.47/0.57    ~r2_hidden(sK7,sK8) | spl13_17),
% 1.47/0.57    inference(resolution,[],[f301,f99])).
% 1.47/0.57  fof(f99,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (sP4(X0,X1,X2) | ~r2_hidden(X1,X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f63])).
% 1.47/0.57  fof(f63,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | (~r2_hidden(X1,X0) & ~r2_hidden(X1,X2))) & (r2_hidden(X1,X0) | r2_hidden(X1,X2) | ~sP4(X0,X1,X2)))),
% 1.47/0.57    inference(rectify,[],[f62])).
% 1.47/0.57  fof(f62,plain,(
% 1.47/0.57    ! [X1,X3,X0] : ((sP4(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~sP4(X1,X3,X0)))),
% 1.47/0.57    inference(flattening,[],[f61])).
% 1.47/0.57  fof(f61,plain,(
% 1.47/0.57    ! [X1,X3,X0] : ((sP4(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~sP4(X1,X3,X0)))),
% 1.47/0.57    inference(nnf_transformation,[],[f36])).
% 1.47/0.57  fof(f36,plain,(
% 1.47/0.57    ! [X1,X3,X0] : (sP4(X1,X3,X0) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0)))),
% 1.47/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.47/0.57  fof(f301,plain,(
% 1.47/0.57    ~sP4(sK9,sK7,sK8) | spl13_17),
% 1.47/0.57    inference(avatar_component_clause,[],[f299])).
% 1.47/0.57  fof(f304,plain,(
% 1.47/0.57    ~spl13_17 | spl13_14),
% 1.47/0.57    inference(avatar_split_clause,[],[f290,f276,f299])).
% 1.47/0.57  fof(f276,plain,(
% 1.47/0.57    spl13_14 <=> r2_hidden(sK7,k2_xboole_0(sK8,sK9))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).
% 1.47/0.57  fof(f290,plain,(
% 1.47/0.57    ~sP4(sK9,sK7,sK8) | spl13_14),
% 1.47/0.57    inference(resolution,[],[f278,f194])).
% 1.47/0.57  fof(f194,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_xboole_0(X2,X0)) | ~sP4(X0,X1,X2)) )),
% 1.47/0.57    inference(resolution,[],[f95,f103])).
% 1.47/0.57  fof(f103,plain,(
% 1.47/0.57    ( ! [X0,X1] : (sP5(X0,X1,k2_xboole_0(X0,X1))) )),
% 1.47/0.57    inference(equality_resolution,[],[f101])).
% 1.47/0.57  fof(f101,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (sP5(X0,X1,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.47/0.57    inference(cnf_transformation,[],[f64])).
% 1.47/0.57  fof(f64,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP5(X0,X1,X2)) & (sP5(X0,X1,X2) | k2_xboole_0(X0,X1) != X2))),
% 1.47/0.57    inference(nnf_transformation,[],[f38])).
% 1.47/0.57  fof(f38,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP5(X0,X1,X2))),
% 1.47/0.57    inference(definition_folding,[],[f1,f37,f36])).
% 1.47/0.57  fof(f37,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (sP5(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP4(X1,X3,X0)))),
% 1.47/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 1.47/0.57  fof(f1,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.47/0.57  fof(f95,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X1] : (~sP5(X0,X1,X2) | ~sP4(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f60])).
% 1.47/0.57  fof(f60,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ((~sP4(X1,sK12(X0,X1,X2),X0) | ~r2_hidden(sK12(X0,X1,X2),X2)) & (sP4(X1,sK12(X0,X1,X2),X0) | r2_hidden(sK12(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP4(X1,X4,X0)) & (sP4(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP5(X0,X1,X2)))),
% 1.47/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f58,f59])).
% 1.47/0.57  fof(f59,plain,(
% 1.47/0.57    ! [X2,X1,X0] : (? [X3] : ((~sP4(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP4(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP4(X1,sK12(X0,X1,X2),X0) | ~r2_hidden(sK12(X0,X1,X2),X2)) & (sP4(X1,sK12(X0,X1,X2),X0) | r2_hidden(sK12(X0,X1,X2),X2))))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f58,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ? [X3] : ((~sP4(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP4(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP4(X1,X4,X0)) & (sP4(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP5(X0,X1,X2)))),
% 1.47/0.57    inference(rectify,[],[f57])).
% 1.47/0.57  fof(f57,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ? [X3] : ((~sP4(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP4(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP4(X1,X3,X0)) & (sP4(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP5(X0,X1,X2)))),
% 1.47/0.57    inference(nnf_transformation,[],[f37])).
% 1.47/0.57  fof(f278,plain,(
% 1.47/0.57    ~r2_hidden(sK7,k2_xboole_0(sK8,sK9)) | spl13_14),
% 1.47/0.57    inference(avatar_component_clause,[],[f276])).
% 1.47/0.57  fof(f283,plain,(
% 1.47/0.57    ~spl13_14 | ~spl13_15 | spl13_13),
% 1.47/0.57    inference(avatar_split_clause,[],[f273,f268,f280,f276])).
% 1.47/0.57  fof(f268,plain,(
% 1.47/0.57    spl13_13 <=> sP0(sK6,k2_xboole_0(sK8,sK9),sK7)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).
% 1.47/0.57  fof(f273,plain,(
% 1.47/0.57    ~v3_pre_topc(k2_xboole_0(sK8,sK9),sK6) | ~r2_hidden(sK7,k2_xboole_0(sK8,sK9)) | spl13_13),
% 1.47/0.57    inference(resolution,[],[f270,f76])).
% 1.47/0.57  fof(f76,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f48])).
% 1.47/0.57  fof(f48,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1)) & ((v3_pre_topc(X1,X0) & r2_hidden(X2,X1)) | ~sP0(X0,X1,X2)))),
% 1.47/0.57    inference(rectify,[],[f47])).
% 1.47/0.57  fof(f47,plain,(
% 1.47/0.57    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X2,X1)))),
% 1.47/0.57    inference(flattening,[],[f46])).
% 1.47/0.57  fof(f46,plain,(
% 1.47/0.57    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X2,X1)))),
% 1.47/0.57    inference(nnf_transformation,[],[f29])).
% 1.47/0.57  fof(f270,plain,(
% 1.47/0.57    ~sP0(sK6,k2_xboole_0(sK8,sK9),sK7) | spl13_13),
% 1.47/0.57    inference(avatar_component_clause,[],[f268])).
% 1.47/0.57  fof(f271,plain,(
% 1.47/0.57    ~spl13_12 | ~spl13_13 | spl13_10),
% 1.47/0.57    inference(avatar_split_clause,[],[f255,f244,f268,f264])).
% 1.47/0.57  fof(f244,plain,(
% 1.47/0.57    spl13_10 <=> r2_hidden(k2_xboole_0(sK8,sK9),u1_struct_0(k9_yellow_6(sK6,sK7)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).
% 1.47/0.57  fof(f255,plain,(
% 1.47/0.57    ~sP0(sK6,k2_xboole_0(sK8,sK9),sK7) | ~sP1(sK7,k2_xboole_0(sK8,sK9),sK6) | spl13_10),
% 1.47/0.57    inference(resolution,[],[f246,f73])).
% 1.47/0.57  fof(f73,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f45])).
% 1.47/0.57  fof(f45,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (((r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))))) | ~sP1(X0,X1,X2))),
% 1.47/0.57    inference(rectify,[],[f44])).
% 1.47/0.57  fof(f44,plain,(
% 1.47/0.57    ! [X1,X2,X0] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~sP0(X0,X2,X1)) & (sP0(X0,X2,X1) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~sP1(X1,X2,X0))),
% 1.47/0.57    inference(nnf_transformation,[],[f30])).
% 1.47/0.57  fof(f246,plain,(
% 1.47/0.57    ~r2_hidden(k2_xboole_0(sK8,sK9),u1_struct_0(k9_yellow_6(sK6,sK7))) | spl13_10),
% 1.47/0.57    inference(avatar_component_clause,[],[f244])).
% 1.47/0.57  fof(f250,plain,(
% 1.47/0.57    ~spl13_10 | spl13_1),
% 1.47/0.57    inference(avatar_split_clause,[],[f241,f105,f244])).
% 1.47/0.57  fof(f105,plain,(
% 1.47/0.57    spl13_1 <=> m1_subset_1(k2_xboole_0(sK8,sK9),u1_struct_0(k9_yellow_6(sK6,sK7)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.47/0.57  fof(f241,plain,(
% 1.47/0.57    ~r2_hidden(k2_xboole_0(sK8,sK9),u1_struct_0(k9_yellow_6(sK6,sK7))) | spl13_1),
% 1.47/0.57    inference(resolution,[],[f233,f184])).
% 1.47/0.57  fof(f184,plain,(
% 1.47/0.57    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(k9_yellow_6(sK6,sK7))) | ~r2_hidden(k2_xboole_0(sK8,sK9),X0)) ) | spl13_1),
% 1.47/0.57    inference(resolution,[],[f180,f107])).
% 1.47/0.57  fof(f107,plain,(
% 1.47/0.57    ~m1_subset_1(k2_xboole_0(sK8,sK9),u1_struct_0(k9_yellow_6(sK6,sK7))) | spl13_1),
% 1.47/0.57    inference(avatar_component_clause,[],[f105])).
% 1.47/0.57  fof(f180,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X2) | ~r1_tarski(X2,X1)) )),
% 1.47/0.57    inference(resolution,[],[f91,f89])).
% 1.47/0.57  fof(f89,plain,(
% 1.47/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f56])).
% 1.47/0.57  fof(f56,plain,(
% 1.47/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.47/0.57    inference(nnf_transformation,[],[f6])).
% 1.47/0.57  fof(f6,axiom,(
% 1.47/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.47/0.57  fof(f91,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f24])).
% 1.47/0.57  fof(f24,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.47/0.57    inference(flattening,[],[f23])).
% 1.47/0.57  fof(f23,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.47/0.57    inference(ennf_transformation,[],[f7])).
% 1.47/0.57  fof(f7,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.47/0.57  fof(f233,plain,(
% 1.47/0.57    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f139,f179,f139,f87])).
% 1.47/0.57  fof(f87,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (sP3(X2,X1,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f35])).
% 1.47/0.57  fof(f35,plain,(
% 1.47/0.57    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | sP3(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.47/0.57    inference(definition_folding,[],[f20,f34])).
% 1.47/0.57  fof(f34,plain,(
% 1.47/0.57    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~sP3(X2,X1,X0))),
% 1.47/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.47/0.57  fof(f20,plain,(
% 1.47/0.57    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.47/0.57    inference(flattening,[],[f19])).
% 1.47/0.57  fof(f19,plain,(
% 1.47/0.57    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f5])).
% 1.47/0.57  fof(f5,axiom,(
% 1.47/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
% 1.47/0.57  fof(f179,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~sP3(X0,X0,X1)) )),
% 1.47/0.57    inference(duplicate_literal_removal,[],[f178])).
% 1.47/0.57  fof(f178,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~sP3(X0,X0,X1) | ~sP3(X0,X0,X1)) )),
% 1.47/0.57    inference(resolution,[],[f86,f85])).
% 1.47/0.57  fof(f85,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK11(X0,X1,X2),X1) | ~sP3(X0,X1,X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f55])).
% 1.47/0.57  fof(f55,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((~r2_hidden(sK11(X0,X1,X2),X0) & r2_hidden(sK11(X0,X1,X2),X1) & m1_subset_1(sK11(X0,X1,X2),X2)) | ~sP3(X0,X1,X2))),
% 1.47/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f53,f54])).
% 1.47/0.57  fof(f54,plain,(
% 1.47/0.57    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(X3,X1) & m1_subset_1(X3,X2)) => (~r2_hidden(sK11(X0,X1,X2),X0) & r2_hidden(sK11(X0,X1,X2),X1) & m1_subset_1(sK11(X0,X1,X2),X2)))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f53,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(X3,X1) & m1_subset_1(X3,X2)) | ~sP3(X0,X1,X2))),
% 1.47/0.57    inference(rectify,[],[f52])).
% 1.47/0.57  fof(f52,plain,(
% 1.47/0.57    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~sP3(X2,X1,X0))),
% 1.47/0.57    inference(nnf_transformation,[],[f34])).
% 1.47/0.57  fof(f86,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK11(X0,X1,X2),X0) | ~sP3(X0,X1,X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f55])).
% 1.47/0.57  fof(f139,plain,(
% 1.47/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_xboole_0(X0,X1)))) )),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f83,f89])).
% 1.47/0.57  fof(f83,plain,(
% 1.47/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f2])).
% 1.47/0.57  fof(f2,axiom,(
% 1.47/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.47/0.57  fof(f138,plain,(
% 1.47/0.57    ~spl13_7),
% 1.47/0.57    inference(avatar_split_clause,[],[f65,f135])).
% 1.47/0.57  fof(f65,plain,(
% 1.47/0.57    ~v2_struct_0(sK6)),
% 1.47/0.57    inference(cnf_transformation,[],[f43])).
% 1.47/0.57  fof(f43,plain,(
% 1.47/0.57    (((~m1_subset_1(k2_xboole_0(sK8,sK9),u1_struct_0(k9_yellow_6(sK6,sK7))) & m1_subset_1(sK9,u1_struct_0(k9_yellow_6(sK6,sK7)))) & m1_subset_1(sK8,u1_struct_0(k9_yellow_6(sK6,sK7)))) & m1_subset_1(sK7,u1_struct_0(sK6))) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)),
% 1.47/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f14,f42,f41,f40,f39])).
% 1.47/0.57  fof(f39,plain,(
% 1.47/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK6,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK6,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK6,X1)))) & m1_subset_1(X1,u1_struct_0(sK6))) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f40,plain,(
% 1.47/0.57    ? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK6,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK6,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK6,X1)))) & m1_subset_1(X1,u1_struct_0(sK6))) => (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK6,sK7))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK6,sK7)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK6,sK7)))) & m1_subset_1(sK7,u1_struct_0(sK6)))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f41,plain,(
% 1.47/0.57    ? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK6,sK7))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK6,sK7)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK6,sK7)))) => (? [X3] : (~m1_subset_1(k2_xboole_0(sK8,X3),u1_struct_0(k9_yellow_6(sK6,sK7))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK6,sK7)))) & m1_subset_1(sK8,u1_struct_0(k9_yellow_6(sK6,sK7))))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f42,plain,(
% 1.47/0.57    ? [X3] : (~m1_subset_1(k2_xboole_0(sK8,X3),u1_struct_0(k9_yellow_6(sK6,sK7))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK6,sK7)))) => (~m1_subset_1(k2_xboole_0(sK8,sK9),u1_struct_0(k9_yellow_6(sK6,sK7))) & m1_subset_1(sK9,u1_struct_0(k9_yellow_6(sK6,sK7))))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f14,plain,(
% 1.47/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.47/0.57    inference(flattening,[],[f13])).
% 1.47/0.57  fof(f13,plain,(
% 1.47/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f12])).
% 1.47/0.57  fof(f12,negated_conjecture,(
% 1.47/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.47/0.57    inference(negated_conjecture,[],[f11])).
% 1.47/0.57  fof(f11,conjecture,(
% 1.47/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).
% 1.47/0.57  fof(f133,plain,(
% 1.47/0.57    spl13_6),
% 1.47/0.57    inference(avatar_split_clause,[],[f66,f130])).
% 1.47/0.57  fof(f66,plain,(
% 1.47/0.57    v2_pre_topc(sK6)),
% 1.47/0.57    inference(cnf_transformation,[],[f43])).
% 1.47/0.57  fof(f128,plain,(
% 1.47/0.57    spl13_5),
% 1.47/0.57    inference(avatar_split_clause,[],[f67,f125])).
% 1.47/0.57  fof(f67,plain,(
% 1.47/0.57    l1_pre_topc(sK6)),
% 1.47/0.57    inference(cnf_transformation,[],[f43])).
% 1.47/0.57  fof(f123,plain,(
% 1.47/0.57    spl13_4),
% 1.47/0.57    inference(avatar_split_clause,[],[f68,f120])).
% 1.47/0.57  fof(f68,plain,(
% 1.47/0.57    m1_subset_1(sK7,u1_struct_0(sK6))),
% 1.47/0.57    inference(cnf_transformation,[],[f43])).
% 1.47/0.57  fof(f118,plain,(
% 1.47/0.57    spl13_3),
% 1.47/0.57    inference(avatar_split_clause,[],[f69,f115])).
% 1.47/0.57  fof(f69,plain,(
% 1.47/0.57    m1_subset_1(sK8,u1_struct_0(k9_yellow_6(sK6,sK7)))),
% 1.47/0.57    inference(cnf_transformation,[],[f43])).
% 1.47/0.57  fof(f113,plain,(
% 1.47/0.57    spl13_2),
% 1.47/0.57    inference(avatar_split_clause,[],[f70,f110])).
% 1.47/0.57  fof(f70,plain,(
% 1.47/0.57    m1_subset_1(sK9,u1_struct_0(k9_yellow_6(sK6,sK7)))),
% 1.47/0.57    inference(cnf_transformation,[],[f43])).
% 1.47/0.57  fof(f108,plain,(
% 1.47/0.57    ~spl13_1),
% 1.47/0.57    inference(avatar_split_clause,[],[f71,f105])).
% 1.47/0.57  fof(f71,plain,(
% 1.47/0.57    ~m1_subset_1(k2_xboole_0(sK8,sK9),u1_struct_0(k9_yellow_6(sK6,sK7)))),
% 1.47/0.57    inference(cnf_transformation,[],[f43])).
% 1.47/0.57  % SZS output end Proof for theBenchmark
% 1.47/0.57  % (24471)------------------------------
% 1.47/0.57  % (24471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (24471)Termination reason: Refutation
% 1.47/0.57  
% 1.47/0.57  % (24471)Memory used [KB]: 11513
% 1.47/0.57  % (24471)Time elapsed: 0.163 s
% 1.47/0.57  % (24471)------------------------------
% 1.47/0.57  % (24471)------------------------------
% 1.47/0.59  % (24454)Success in time 0.229 s
%------------------------------------------------------------------------------
