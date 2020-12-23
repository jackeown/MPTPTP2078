%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t7_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:54 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  385 (1174 expanded)
%              Number of leaves         :  110 ( 527 expanded)
%              Depth                    :   11
%              Number of atoms          : 1203 (3742 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1093,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f124,f131,f138,f145,f152,f159,f168,f181,f190,f197,f221,f233,f244,f256,f271,f281,f288,f300,f315,f322,f329,f358,f379,f386,f431,f470,f477,f505,f518,f527,f535,f544,f553,f577,f596,f605,f625,f635,f642,f656,f666,f673,f683,f690,f697,f704,f720,f752,f760,f767,f776,f788,f795,f808,f815,f827,f836,f844,f852,f864,f871,f879,f886,f893,f911,f920,f933,f940,f960,f967,f977,f984,f1007,f1019,f1026,f1033,f1053,f1073,f1082,f1087])).

fof(f1087,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_74
    | ~ spl8_88
    | ~ spl8_92
    | spl8_129 ),
    inference(avatar_contradiction_clause,[],[f1086])).

fof(f1086,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_74
    | ~ spl8_88
    | ~ spl8_92
    | ~ spl8_129 ),
    inference(subsumption_resolution,[],[f1084,f606])).

fof(f606,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f123,f130,f158,f604,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ( r2_hidden(X1,sK4(X0,X1,X2))
                & r1_tarski(sK4(X0,X1,X2),X2)
                & v3_pre_topc(sK4(X0,X1,X2),X0)
                & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f68,f69])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK4(X0,X1,X2))
        & r1_tarski(sK4(X0,X1,X2),X2)
        & v3_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X3] :
                  ( r2_hidden(X1,X3)
                  & r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',t54_tops_1)).

fof(f604,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl8_74 ),
    inference(avatar_component_clause,[],[f603])).

fof(f603,plain,
    ( spl8_74
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f158,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl8_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f130,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl8_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f123,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1084,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_88
    | ~ spl8_92
    | ~ spl8_129 ),
    inference(unit_resulting_resolution,[],[f116,f123,f130,f144,f682,f696,f885,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',t5_connsp_2)).

fof(f885,plain,
    ( ~ m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ spl8_129 ),
    inference(avatar_component_clause,[],[f884])).

fof(f884,plain,
    ( spl8_129
  <=> ~ m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_129])])).

fof(f696,plain,
    ( v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl8_92 ),
    inference(avatar_component_clause,[],[f695])).

fof(f695,plain,
    ( spl8_92
  <=> v3_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f682,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl8_88 ),
    inference(avatar_component_clause,[],[f681])).

fof(f681,plain,
    ( spl8_88
  <=> r2_hidden(sK1,sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f144,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl8_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f116,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl8_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1082,plain,
    ( ~ spl8_161
    | spl8_157 ),
    inference(avatar_split_clause,[],[f1056,f1051,f1080])).

fof(f1080,plain,
    ( spl8_161
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_161])])).

fof(f1051,plain,
    ( spl8_157
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_157])])).

fof(f1056,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_157 ),
    inference(unit_resulting_resolution,[],[f1052,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',t1_subset)).

fof(f1052,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_157 ),
    inference(avatar_component_clause,[],[f1051])).

fof(f1073,plain,
    ( ~ spl8_159
    | spl8_157 ),
    inference(avatar_split_clause,[],[f1054,f1051,f1071])).

fof(f1071,plain,
    ( spl8_159
  <=> ~ r1_tarski(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_159])])).

fof(f1054,plain,
    ( ~ r1_tarski(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_157 ),
    inference(unit_resulting_resolution,[],[f1052,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',t3_subset)).

fof(f1053,plain,
    ( ~ spl8_157
    | spl8_59
    | ~ spl8_138 ),
    inference(avatar_split_clause,[],[f947,f938,f503,f1051])).

fof(f503,plain,
    ( spl8_59
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f938,plain,
    ( spl8_138
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_138])])).

fof(f947,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_59
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f504,f939,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',t4_subset)).

fof(f939,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl8_138 ),
    inference(avatar_component_clause,[],[f938])).

fof(f504,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_59 ),
    inference(avatar_component_clause,[],[f503])).

fof(f1033,plain,
    ( spl8_154
    | spl8_25
    | ~ spl8_148 ),
    inference(avatar_split_clause,[],[f1010,f1005,f231,f1031])).

fof(f1031,plain,
    ( spl8_154
  <=> r2_hidden(sK5(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_154])])).

fof(f231,plain,
    ( spl8_25
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f1005,plain,
    ( spl8_148
  <=> m1_subset_1(sK5(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_148])])).

fof(f1010,plain,
    ( r2_hidden(sK5(sK2),u1_struct_0(sK0))
    | ~ spl8_25
    | ~ spl8_148 ),
    inference(unit_resulting_resolution,[],[f232,f1006,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',t2_subset)).

fof(f1006,plain,
    ( m1_subset_1(sK5(sK2),u1_struct_0(sK0))
    | ~ spl8_148 ),
    inference(avatar_component_clause,[],[f1005])).

fof(f232,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f231])).

fof(f1026,plain,
    ( ~ spl8_153
    | spl8_25
    | ~ spl8_148 ),
    inference(avatar_split_clause,[],[f1009,f1005,f231,f1024])).

fof(f1024,plain,
    ( spl8_153
  <=> ~ r2_hidden(u1_struct_0(sK0),sK5(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_153])])).

fof(f1009,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(sK2))
    | ~ spl8_25
    | ~ spl8_148 ),
    inference(unit_resulting_resolution,[],[f232,f1006,f172])).

fof(f172,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f99,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',antisymmetry_r2_hidden)).

fof(f1019,plain,
    ( ~ spl8_151
    | spl8_141 ),
    inference(avatar_split_clause,[],[f968,f958,f1017])).

fof(f1017,plain,
    ( spl8_151
  <=> ~ r2_hidden(sK2,sK5(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_151])])).

fof(f958,plain,
    ( spl8_141
  <=> ~ m1_subset_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_141])])).

fof(f968,plain,
    ( ~ r2_hidden(sK2,sK5(k1_zfmisc_1(sK1)))
    | ~ spl8_141 ),
    inference(unit_resulting_resolution,[],[f96,f959,f108])).

fof(f959,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | ~ spl8_141 ),
    inference(avatar_component_clause,[],[f958])).

fof(f96,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',existence_m1_subset_1)).

fof(f1007,plain,
    ( spl8_148
    | ~ spl8_12
    | ~ spl8_146 ),
    inference(avatar_split_clause,[],[f990,f982,f157,f1005])).

fof(f982,plain,
    ( spl8_146
  <=> r2_hidden(sK5(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_146])])).

fof(f990,plain,
    ( m1_subset_1(sK5(sK2),u1_struct_0(sK0))
    | ~ spl8_12
    | ~ spl8_146 ),
    inference(unit_resulting_resolution,[],[f158,f983,f108])).

fof(f983,plain,
    ( r2_hidden(sK5(sK2),sK2)
    | ~ spl8_146 ),
    inference(avatar_component_clause,[],[f982])).

fof(f984,plain,
    ( spl8_146
    | spl8_133 ),
    inference(avatar_split_clause,[],[f913,f909,f982])).

fof(f909,plain,
    ( spl8_133
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_133])])).

fof(f913,plain,
    ( r2_hidden(sK5(sK2),sK2)
    | ~ spl8_133 ),
    inference(unit_resulting_resolution,[],[f96,f910,f99])).

fof(f910,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl8_133 ),
    inference(avatar_component_clause,[],[f909])).

fof(f977,plain,
    ( ~ spl8_145
    | spl8_133 ),
    inference(avatar_split_clause,[],[f912,f909,f975])).

fof(f975,plain,
    ( spl8_145
  <=> ~ r2_hidden(sK2,sK5(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_145])])).

fof(f912,plain,
    ( ~ r2_hidden(sK2,sK5(sK2))
    | ~ spl8_133 ),
    inference(unit_resulting_resolution,[],[f96,f910,f172])).

fof(f967,plain,
    ( spl8_142
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f248,f136,f965])).

fof(f965,plain,
    ( spl8_142
  <=> m1_subset_1(k1_tops_1(sK7,sK5(k1_zfmisc_1(u1_struct_0(sK7)))),k1_zfmisc_1(u1_struct_0(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_142])])).

fof(f136,plain,
    ( spl8_6
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f248,plain,
    ( m1_subset_1(k1_tops_1(sK7,sK5(k1_zfmisc_1(u1_struct_0(sK7)))),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f137,f96,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',dt_k1_tops_1)).

fof(f137,plain,
    ( l1_pre_topc(sK7)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f960,plain,
    ( ~ spl8_141
    | spl8_47
    | spl8_133
    | ~ spl8_134 ),
    inference(avatar_split_clause,[],[f922,f918,f909,f353,f958])).

fof(f353,plain,
    ( spl8_47
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f918,plain,
    ( spl8_134
  <=> m1_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_134])])).

fof(f922,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | ~ spl8_47
    | ~ spl8_133
    | ~ spl8_134 ),
    inference(unit_resulting_resolution,[],[f910,f354,f919,f173])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f172,f99])).

fof(f919,plain,
    ( m1_subset_1(sK1,sK2)
    | ~ spl8_134 ),
    inference(avatar_component_clause,[],[f918])).

fof(f354,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f353])).

fof(f940,plain,
    ( spl8_138
    | spl8_133
    | ~ spl8_134 ),
    inference(avatar_split_clause,[],[f924,f918,f909,f938])).

fof(f924,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl8_133
    | ~ spl8_134 ),
    inference(unit_resulting_resolution,[],[f910,f919,f99])).

fof(f933,plain,
    ( ~ spl8_137
    | spl8_133
    | ~ spl8_134 ),
    inference(avatar_split_clause,[],[f923,f918,f909,f931])).

fof(f931,plain,
    ( spl8_137
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_137])])).

fof(f923,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl8_133
    | ~ spl8_134 ),
    inference(unit_resulting_resolution,[],[f910,f919,f172])).

fof(f920,plain,
    ( spl8_134
    | ~ spl8_88
    | ~ spl8_126 ),
    inference(avatar_split_clause,[],[f900,f877,f681,f918])).

fof(f877,plain,
    ( spl8_126
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_126])])).

fof(f900,plain,
    ( m1_subset_1(sK1,sK2)
    | ~ spl8_88
    | ~ spl8_126 ),
    inference(unit_resulting_resolution,[],[f682,f878,f108])).

fof(f878,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(sK2))
    | ~ spl8_126 ),
    inference(avatar_component_clause,[],[f877])).

fof(f911,plain,
    ( ~ spl8_133
    | ~ spl8_88
    | ~ spl8_126 ),
    inference(avatar_split_clause,[],[f901,f877,f681,f909])).

fof(f901,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl8_88
    | ~ spl8_126 ),
    inference(unit_resulting_resolution,[],[f682,f878,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',t5_subset)).

fof(f893,plain,
    ( spl8_130
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_32
    | ~ spl8_120 ),
    inference(avatar_split_clause,[],[f853,f850,f279,f143,f129,f122,f115,f891])).

fof(f891,plain,
    ( spl8_130
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_130])])).

fof(f279,plain,
    ( spl8_32
  <=> m1_connsp_2(sK6(sK0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f850,plain,
    ( spl8_120
  <=> m1_subset_1(sK6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_120])])).

fof(f853,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK6(sK0,sK1)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_32
    | ~ spl8_120 ),
    inference(unit_resulting_resolution,[],[f116,f123,f130,f144,f280,f851,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',d1_connsp_2)).

fof(f851,plain,
    ( m1_subset_1(sK6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_120 ),
    inference(avatar_component_clause,[],[f850])).

fof(f280,plain,
    ( m1_connsp_2(sK6(sK0,sK1),sK0,sK1)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f279])).

fof(f886,plain,
    ( ~ spl8_129
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_74
    | ~ spl8_90
    | ~ spl8_92
    | spl8_97 ),
    inference(avatar_split_clause,[],[f729,f718,f695,f688,f603,f157,f129,f122,f884])).

fof(f688,plain,
    ( spl8_90
  <=> r1_tarski(sK4(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_90])])).

fof(f718,plain,
    ( spl8_97
  <=> ~ v1_xboole_0(sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_97])])).

fof(f729,plain,
    ( ~ m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_74
    | ~ spl8_90
    | ~ spl8_92
    | ~ spl8_97 ),
    inference(subsumption_resolution,[],[f728,f719])).

fof(f719,plain,
    ( ~ v1_xboole_0(sK4(sK0,sK1,sK2))
    | ~ spl8_97 ),
    inference(avatar_component_clause,[],[f718])).

fof(f728,plain,
    ( ~ m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | v1_xboole_0(sK4(sK0,sK1,sK2))
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_74
    | ~ spl8_90
    | ~ spl8_92 ),
    inference(subsumption_resolution,[],[f727,f606])).

fof(f727,plain,
    ( ~ m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK4(sK0,sK1,sK2))
    | ~ spl8_90
    | ~ spl8_92 ),
    inference(subsumption_resolution,[],[f724,f689])).

fof(f689,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ spl8_90 ),
    inference(avatar_component_clause,[],[f688])).

fof(f724,plain,
    ( ~ r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK4(sK0,sK1,sK2))
    | ~ spl8_92 ),
    inference(resolution,[],[f696,f84])).

fof(f84,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK2)
      | ~ m1_connsp_2(X3,sK0,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,sK2)
        | ~ v3_pre_topc(X3,sK0)
        | ~ m1_connsp_2(X3,sK0,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X3) )
    & m1_connsp_2(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f62,f61,f60])).

fof(f60,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_connsp_2(X3,X0,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | v1_xboole_0(X3) )
                & m1_connsp_2(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,sK0)
                  | ~ m1_connsp_2(X3,sK0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,sK0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_connsp_2(X3,X0,sK1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                | v1_xboole_0(X3) )
            & m1_connsp_2(X2,X0,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_connsp_2(X3,X0,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
              | v1_xboole_0(X3) )
          & m1_connsp_2(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( ~ r1_tarski(X3,sK2)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_connsp_2(X3,X0,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X3) )
        & m1_connsp_2(sK2,X0,X1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & ~ v1_xboole_0(X3) )
                       => ~ ( r1_tarski(X3,X2)
                            & v3_pre_topc(X3,X0)
                            & m1_connsp_2(X3,X0,X1) ) )
                    & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',t7_connsp_2)).

fof(f879,plain,
    ( spl8_126
    | ~ spl8_90 ),
    inference(avatar_split_clause,[],[f723,f688,f877])).

fof(f723,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(sK2))
    | ~ spl8_90 ),
    inference(unit_resulting_resolution,[],[f689,f105])).

fof(f871,plain,
    ( spl8_124
    | ~ spl8_120 ),
    inference(avatar_split_clause,[],[f856,f850,f869])).

fof(f869,plain,
    ( spl8_124
  <=> r1_tarski(sK6(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_124])])).

fof(f856,plain,
    ( r1_tarski(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_120 ),
    inference(unit_resulting_resolution,[],[f851,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f864,plain,
    ( spl8_122
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f274,f129,f122,f115,f862])).

fof(f862,plain,
    ( spl8_122
  <=> m1_connsp_2(sK6(sK0,sK5(u1_struct_0(sK0))),sK0,sK5(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_122])])).

fof(f274,plain,
    ( m1_connsp_2(sK6(sK0,sK5(u1_struct_0(sK0))),sK0,sK5(u1_struct_0(sK0)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f116,f123,f130,f96,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK6(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK6(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f50,f73])).

fof(f73,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK6(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',existence_m1_connsp_2)).

fof(f852,plain,
    ( spl8_120
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f369,f279,f143,f129,f122,f115,f850])).

fof(f369,plain,
    ( m1_subset_1(sK6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f116,f123,f130,f280,f144,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',dt_m1_connsp_2)).

fof(f844,plain,
    ( ~ spl8_119
    | spl8_111 ),
    inference(avatar_split_clause,[],[f818,f806,f842])).

fof(f842,plain,
    ( spl8_119
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_119])])).

fof(f806,plain,
    ( spl8_111
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_111])])).

fof(f818,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_111 ),
    inference(unit_resulting_resolution,[],[f807,f98])).

fof(f807,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_111 ),
    inference(avatar_component_clause,[],[f806])).

fof(f836,plain,
    ( spl8_116
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f247,f129,f834])).

fof(f834,plain,
    ( spl8_116
  <=> m1_subset_1(k1_tops_1(sK0,sK5(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_116])])).

fof(f247,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK5(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f130,f96,f102])).

fof(f827,plain,
    ( ~ spl8_115
    | spl8_111 ),
    inference(avatar_split_clause,[],[f816,f806,f825])).

fof(f825,plain,
    ( spl8_115
  <=> ~ r1_tarski(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).

fof(f816,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_111 ),
    inference(unit_resulting_resolution,[],[f807,f105])).

fof(f815,plain,
    ( ~ spl8_113
    | spl8_59 ),
    inference(avatar_split_clause,[],[f508,f503,f813])).

fof(f813,plain,
    ( spl8_113
  <=> ~ r2_hidden(sK1,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).

fof(f508,plain,
    ( ~ r2_hidden(sK1,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl8_59 ),
    inference(unit_resulting_resolution,[],[f96,f504,f108])).

fof(f808,plain,
    ( ~ spl8_111
    | ~ spl8_28
    | spl8_59 ),
    inference(avatar_split_clause,[],[f507,f503,f254,f806])).

fof(f254,plain,
    ( spl8_28
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f507,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_28
    | ~ spl8_59 ),
    inference(unit_resulting_resolution,[],[f255,f504,f108])).

fof(f255,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f254])).

fof(f795,plain,
    ( ~ spl8_109
    | spl8_47
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f710,f681,f353,f793])).

fof(f793,plain,
    ( spl8_109
  <=> ~ m1_subset_1(sK4(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_109])])).

fof(f710,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),sK1)
    | ~ spl8_47
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f354,f682,f172])).

fof(f788,plain,
    ( ~ spl8_107
    | spl8_45 ),
    inference(avatar_split_clause,[],[f365,f350,f786])).

fof(f786,plain,
    ( spl8_107
  <=> ~ r2_hidden(u1_struct_0(sK0),sK5(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_107])])).

fof(f350,plain,
    ( spl8_45
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f365,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(k1_zfmisc_1(sK1)))
    | ~ spl8_45 ),
    inference(unit_resulting_resolution,[],[f96,f351,f108])).

fof(f351,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f350])).

fof(f776,plain,
    ( spl8_104
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f301,f157,f129,f774])).

fof(f774,plain,
    ( spl8_104
  <=> k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).

fof(f301,plain,
    ( k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2))
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f130,f158,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',projectivity_k1_tops_1)).

fof(f767,plain,
    ( spl8_102
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f707,f681,f765])).

fof(f765,plain,
    ( spl8_102
  <=> m1_subset_1(sK1,sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f707,plain,
    ( m1_subset_1(sK1,sK4(sK0,sK1,sK2))
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f682,f98])).

fof(f760,plain,
    ( ~ spl8_101
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f706,f681,f758])).

fof(f758,plain,
    ( spl8_101
  <=> ~ r2_hidden(sK4(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).

fof(f706,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK2),sK1)
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f682,f97])).

fof(f752,plain,
    ( spl8_98
    | ~ spl8_94 ),
    inference(avatar_split_clause,[],[f741,f702,f750])).

fof(f750,plain,
    ( spl8_98
  <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_98])])).

fof(f702,plain,
    ( spl8_94
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).

fof(f741,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl8_94 ),
    inference(unit_resulting_resolution,[],[f703,f104])).

fof(f703,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_94 ),
    inference(avatar_component_clause,[],[f702])).

fof(f720,plain,
    ( ~ spl8_97
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f708,f681,f718])).

fof(f708,plain,
    ( ~ v1_xboole_0(sK4(sK0,sK1,sK2))
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f682,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',t7_boole)).

fof(f704,plain,
    ( spl8_94
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f245,f157,f129,f702])).

fof(f245,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f130,f158,f102])).

fof(f697,plain,
    ( spl8_92
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f609,f603,f157,f129,f122,f695])).

fof(f609,plain,
    ( v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f123,f130,f158,f604,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(sK4(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f690,plain,
    ( spl8_90
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f608,f603,f157,f129,f122,f688])).

fof(f608,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f123,f130,f158,f604,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f683,plain,
    ( spl8_88
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f607,f603,f157,f129,f122,f681])).

fof(f607,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f123,f130,f158,f604,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f673,plain,
    ( ~ spl8_87
    | spl8_67 ),
    inference(avatar_split_clause,[],[f582,f542,f671])).

fof(f671,plain,
    ( spl8_87
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).

fof(f542,plain,
    ( spl8_67
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).

fof(f582,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_67 ),
    inference(unit_resulting_resolution,[],[f543,f98])).

fof(f543,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_67 ),
    inference(avatar_component_clause,[],[f542])).

fof(f666,plain,
    ( ~ spl8_85
    | spl8_65 ),
    inference(avatar_split_clause,[],[f568,f533,f664])).

fof(f664,plain,
    ( spl8_85
  <=> ~ r2_hidden(sK3(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_85])])).

fof(f533,plain,
    ( spl8_65
  <=> ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).

fof(f568,plain,
    ( ~ r2_hidden(sK3(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_65 ),
    inference(unit_resulting_resolution,[],[f534,f98])).

fof(f534,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_65 ),
    inference(avatar_component_clause,[],[f533])).

fof(f656,plain,
    ( ~ spl8_83
    | spl8_47
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f615,f603,f353,f654])).

fof(f654,plain,
    ( spl8_83
  <=> ~ m1_subset_1(k1_tops_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).

fof(f615,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),sK1)
    | ~ spl8_47
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f354,f604,f172])).

fof(f642,plain,
    ( spl8_80
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f612,f603,f640])).

fof(f640,plain,
    ( spl8_80
  <=> m1_subset_1(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f612,plain,
    ( m1_subset_1(sK1,k1_tops_1(sK0,sK2))
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f604,f98])).

fof(f635,plain,
    ( ~ spl8_79
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f611,f603,f633])).

fof(f633,plain,
    ( spl8_79
  <=> ~ r2_hidden(k1_tops_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).

fof(f611,plain,
    ( ~ r2_hidden(k1_tops_1(sK0,sK2),sK1)
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f604,f97])).

fof(f625,plain,
    ( ~ spl8_77
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f613,f603,f623])).

fof(f623,plain,
    ( spl8_77
  <=> ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).

fof(f613,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f604,f107])).

fof(f605,plain,
    ( spl8_74
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f585,f157,f150,f143,f129,f122,f115,f603])).

fof(f150,plain,
    ( spl8_10
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f585,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f116,f123,f130,f151,f144,f158,f86])).

fof(f151,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f596,plain,
    ( ~ spl8_73
    | spl8_67 ),
    inference(avatar_split_clause,[],[f580,f542,f594])).

fof(f594,plain,
    ( spl8_73
  <=> ~ r1_tarski(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_73])])).

fof(f580,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl8_67 ),
    inference(unit_resulting_resolution,[],[f543,f105])).

fof(f577,plain,
    ( ~ spl8_71
    | spl8_65 ),
    inference(avatar_split_clause,[],[f566,f533,f575])).

fof(f575,plain,
    ( spl8_71
  <=> ~ r1_tarski(sK3(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).

fof(f566,plain,
    ( ~ r1_tarski(sK3(sK0),k1_xboole_0)
    | ~ spl8_65 ),
    inference(unit_resulting_resolution,[],[f534,f105])).

fof(f553,plain,
    ( spl8_68
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f545,f429,f551])).

fof(f551,plain,
    ( spl8_68
  <=> v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f429,plain,
    ( spl8_52
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f545,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_52 ),
    inference(unit_resulting_resolution,[],[f96,f483,f99])).

fof(f483,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_52 ),
    inference(unit_resulting_resolution,[],[f96,f430,f109])).

fof(f430,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f429])).

fof(f544,plain,
    ( ~ spl8_67
    | ~ spl8_28
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f482,f429,f254,f542])).

fof(f482,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_28
    | ~ spl8_52 ),
    inference(unit_resulting_resolution,[],[f255,f430,f109])).

fof(f535,plain,
    ( ~ spl8_65
    | ~ spl8_20
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f478,f429,f195,f533])).

fof(f195,plain,
    ( spl8_20
  <=> r2_hidden(sK5(sK3(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f478,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_20
    | ~ spl8_52 ),
    inference(unit_resulting_resolution,[],[f196,f430,f109])).

fof(f196,plain,
    ( r2_hidden(sK5(sK3(sK0)),sK3(sK0))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f195])).

fof(f527,plain,
    ( ~ spl8_63
    | spl8_59 ),
    inference(avatar_split_clause,[],[f509,f503,f525])).

fof(f525,plain,
    ( spl8_63
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f509,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_59 ),
    inference(unit_resulting_resolution,[],[f504,f98])).

fof(f518,plain,
    ( ~ spl8_61
    | spl8_59 ),
    inference(avatar_split_clause,[],[f506,f503,f516])).

fof(f516,plain,
    ( spl8_61
  <=> ~ r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).

fof(f506,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl8_59 ),
    inference(unit_resulting_resolution,[],[f504,f105])).

fof(f505,plain,
    ( ~ spl8_59
    | ~ spl8_50
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f481,f429,f384,f503])).

fof(f384,plain,
    ( spl8_50
  <=> r2_hidden(sK5(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f481,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_50
    | ~ spl8_52 ),
    inference(unit_resulting_resolution,[],[f385,f430,f109])).

fof(f385,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f384])).

fof(f477,plain,
    ( spl8_56
    | spl8_53 ),
    inference(avatar_split_clause,[],[f441,f426,f475])).

fof(f475,plain,
    ( spl8_56
  <=> r2_hidden(sK5(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f426,plain,
    ( spl8_53
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f441,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0)
    | ~ spl8_53 ),
    inference(unit_resulting_resolution,[],[f96,f427,f99])).

fof(f427,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f426])).

fof(f470,plain,
    ( ~ spl8_55
    | spl8_53 ),
    inference(avatar_split_clause,[],[f440,f426,f468])).

fof(f468,plain,
    ( spl8_55
  <=> ~ r2_hidden(k1_xboole_0,sK5(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f440,plain,
    ( ~ r2_hidden(k1_xboole_0,sK5(k1_xboole_0))
    | ~ spl8_53 ),
    inference(unit_resulting_resolution,[],[f96,f427,f172])).

fof(f431,plain,
    ( spl8_52
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f408,f356,f429])).

fof(f356,plain,
    ( spl8_46
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f408,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_46 ),
    inference(backward_demodulation,[],[f395,f357])).

fof(f357,plain,
    ( v1_xboole_0(sK1)
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f356])).

fof(f395,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f357,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',t6_boole)).

fof(f386,plain,
    ( spl8_50
    | spl8_47 ),
    inference(avatar_split_clause,[],[f363,f353,f384])).

fof(f363,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | ~ spl8_47 ),
    inference(unit_resulting_resolution,[],[f96,f354,f99])).

fof(f379,plain,
    ( ~ spl8_49
    | spl8_47 ),
    inference(avatar_split_clause,[],[f362,f353,f377])).

fof(f377,plain,
    ( spl8_49
  <=> ~ r2_hidden(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f362,plain,
    ( ~ r2_hidden(sK1,sK5(sK1))
    | ~ spl8_47 ),
    inference(unit_resulting_resolution,[],[f96,f354,f172])).

fof(f358,plain,
    ( ~ spl8_45
    | spl8_46
    | spl8_27 ),
    inference(avatar_split_clause,[],[f257,f242,f356,f350])).

fof(f242,plain,
    ( spl8_27
  <=> ~ r2_hidden(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f257,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl8_27 ),
    inference(resolution,[],[f243,f99])).

fof(f243,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f242])).

fof(f329,plain,
    ( spl8_42
    | spl8_25
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f291,f286,f231,f327])).

fof(f327,plain,
    ( spl8_42
  <=> r2_hidden(sK5(sK3(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f286,plain,
    ( spl8_34
  <=> m1_subset_1(sK5(sK3(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f291,plain,
    ( r2_hidden(sK5(sK3(sK0)),u1_struct_0(sK0))
    | ~ spl8_25
    | ~ spl8_34 ),
    inference(unit_resulting_resolution,[],[f232,f287,f99])).

fof(f287,plain,
    ( m1_subset_1(sK5(sK3(sK0)),u1_struct_0(sK0))
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f286])).

fof(f322,plain,
    ( ~ spl8_41
    | spl8_25
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f290,f286,f231,f320])).

fof(f320,plain,
    ( spl8_41
  <=> ~ r2_hidden(u1_struct_0(sK0),sK5(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f290,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(sK3(sK0)))
    | ~ spl8_25
    | ~ spl8_34 ),
    inference(unit_resulting_resolution,[],[f232,f287,f172])).

fof(f315,plain,
    ( spl8_38
    | spl8_25 ),
    inference(avatar_split_clause,[],[f237,f231,f313])).

fof(f313,plain,
    ( spl8_38
  <=> r2_hidden(sK5(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f237,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f96,f232,f99])).

fof(f300,plain,
    ( ~ spl8_37
    | spl8_25 ),
    inference(avatar_split_clause,[],[f235,f231,f298])).

fof(f298,plain,
    ( spl8_37
  <=> ~ r2_hidden(u1_struct_0(sK0),sK5(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f235,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(u1_struct_0(sK0)))
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f96,f232,f172])).

fof(f288,plain,
    ( spl8_34
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f222,f219,f195,f286])).

fof(f219,plain,
    ( spl8_22
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f222,plain,
    ( m1_subset_1(sK5(sK3(sK0)),u1_struct_0(sK0))
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f196,f220,f108])).

fof(f220,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f219])).

fof(f281,plain,
    ( spl8_32
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f273,f143,f129,f122,f115,f279])).

fof(f273,plain,
    ( m1_connsp_2(sK6(sK0,sK1),sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f116,f123,f130,f144,f101])).

fof(f271,plain,
    ( spl8_30
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f224,f219,f269])).

fof(f269,plain,
    ( spl8_30
  <=> r1_tarski(sK3(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f224,plain,
    ( r1_tarski(sK3(sK0),u1_struct_0(sK0))
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f220,f104])).

fof(f256,plain,
    ( spl8_28
    | ~ spl8_8
    | spl8_25 ),
    inference(avatar_split_clause,[],[f236,f231,f143,f254])).

fof(f236,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl8_8
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f144,f232,f99])).

fof(f244,plain,
    ( ~ spl8_27
    | ~ spl8_8
    | spl8_25 ),
    inference(avatar_split_clause,[],[f234,f231,f143,f242])).

fof(f234,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl8_8
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f144,f232,f172])).

fof(f233,plain,
    ( ~ spl8_25
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f223,f219,f195,f231])).

fof(f223,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f196,f220,f109])).

fof(f221,plain,
    ( spl8_22
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f212,f129,f122,f115,f219])).

fof(f212,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f116,f123,f130,f89])).

fof(f89,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v2_tops_1(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',rc6_tops_1)).

fof(f197,plain,
    ( spl8_20
    | spl8_17 ),
    inference(avatar_split_clause,[],[f183,f179,f195])).

fof(f179,plain,
    ( spl8_17
  <=> ~ v1_xboole_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f183,plain,
    ( r2_hidden(sK5(sK3(sK0)),sK3(sK0))
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f96,f180,f99])).

fof(f180,plain,
    ( ~ v1_xboole_0(sK3(sK0))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f179])).

fof(f190,plain,
    ( ~ spl8_19
    | spl8_17 ),
    inference(avatar_split_clause,[],[f182,f179,f188])).

fof(f188,plain,
    ( spl8_19
  <=> ~ r2_hidden(sK3(sK0),sK5(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f182,plain,
    ( ~ r2_hidden(sK3(sK0),sK5(sK3(sK0)))
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f96,f180,f172])).

fof(f181,plain,
    ( ~ spl8_17
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f174,f129,f122,f115,f179])).

fof(f174,plain,
    ( ~ v1_xboole_0(sK3(sK0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f116,f123,f130,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f168,plain,
    ( spl8_14
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f161,f157,f166])).

fof(f166,plain,
    ( spl8_14
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f161,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f158,f104])).

fof(f159,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f82,f157])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

fof(f152,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f83,f150])).

fof(f83,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f145,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f81,f143])).

fof(f81,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f63])).

fof(f138,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f110,f136])).

fof(f110,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    l1_pre_topc(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f13,f76])).

fof(f76,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK7) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t7_connsp_2.p',existence_l1_pre_topc)).

fof(f131,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f80,f129])).

fof(f80,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f124,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f79,f122])).

fof(f79,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f117,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f78,f115])).

fof(f78,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f63])).
%------------------------------------------------------------------------------
