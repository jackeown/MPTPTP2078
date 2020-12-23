%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t22_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:50 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 511 expanded)
%              Number of leaves         :   53 ( 229 expanded)
%              Depth                    :    9
%              Number of atoms          :  544 (1704 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f475,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f88,f95,f102,f109,f116,f123,f133,f144,f158,f179,f187,f196,f215,f231,f240,f250,f258,f268,f281,f288,f298,f312,f323,f330,f344,f354,f377,f395,f402,f422,f429,f436,f456,f467,f474])).

fof(f474,plain,
    ( ~ spl7_16
    | spl7_33
    | ~ spl7_62
    | spl7_69 ),
    inference(avatar_contradiction_clause,[],[f473])).

fof(f473,plain,
    ( $false
    | ~ spl7_16
    | ~ spl7_33
    | ~ spl7_62
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f471,f442])).

fof(f442,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK3),sK2)
    | ~ spl7_16
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f143,f428,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',t4_subset)).

fof(f428,plain,
    ( r2_hidden(sK4(sK0,sK2,sK3),sK1)
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f427])).

fof(f427,plain,
    ( spl7_62
  <=> r2_hidden(sK4(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f143,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl7_16
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f471,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2,sK3),sK2)
    | ~ spl7_33
    | ~ spl7_69 ),
    inference(unit_resulting_resolution,[],[f249,f466,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',t2_subset)).

fof(f466,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl7_69 ),
    inference(avatar_component_clause,[],[f465])).

fof(f465,plain,
    ( spl7_69
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f249,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,sK3),sK2)
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl7_33
  <=> ~ r2_hidden(sK4(sK0,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f467,plain,
    ( ~ spl7_69
    | ~ spl7_16
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f445,f427,f142,f465])).

fof(f445,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl7_16
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f143,f428,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',t5_subset)).

fof(f456,plain,
    ( ~ spl7_67
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f441,f427,f454])).

fof(f454,plain,
    ( spl7_67
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f441,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f428,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',t7_boole)).

fof(f436,plain,
    ( ~ spl7_65
    | spl7_59 ),
    inference(avatar_split_clause,[],[f412,f400,f434])).

fof(f434,plain,
    ( spl7_65
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f400,plain,
    ( spl7_59
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f412,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_59 ),
    inference(unit_resulting_resolution,[],[f401,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',t1_subset)).

fof(f401,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_59 ),
    inference(avatar_component_clause,[],[f400])).

fof(f429,plain,
    ( spl7_62
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f299,f296,f213,f194,f114,f86,f79,f427])).

fof(f79,plain,
    ( spl7_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f86,plain,
    ( spl7_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f114,plain,
    ( spl7_10
  <=> r2_waybel_7(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f194,plain,
    ( spl7_24
  <=> v3_pre_topc(sK4(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f213,plain,
    ( spl7_26
  <=> r2_hidden(sK3,sK4(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f296,plain,
    ( spl7_42
  <=> m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f299,plain,
    ( r2_hidden(sK4(sK0,sK2,sK3),sK1)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f80,f87,f115,f214,f195,f297,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(X2,sK4(X0,X1,X2))
              & v3_pre_topc(sK4(X0,X1,X2),X0)
              & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(X2,sK4(X0,X1,X2))
        & v3_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X3)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X0) )
               => r2_hidden(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',d5_waybel_7)).

fof(f297,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f296])).

fof(f195,plain,
    ( v3_pre_topc(sK4(sK0,sK2,sK3),sK0)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f194])).

fof(f214,plain,
    ( r2_hidden(sK3,sK4(sK0,sK2,sK3))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f213])).

fof(f115,plain,
    ( r2_waybel_7(sK0,sK1,sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f87,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f80,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f79])).

fof(f422,plain,
    ( ~ spl7_61
    | spl7_59 ),
    inference(avatar_split_clause,[],[f410,f400,f420])).

fof(f420,plain,
    ( spl7_61
  <=> ~ r1_tarski(u1_struct_0(sK0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f410,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),o_0_0_xboole_0)
    | ~ spl7_59 ),
    inference(unit_resulting_resolution,[],[f401,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',t3_subset)).

fof(f402,plain,
    ( ~ spl7_59
    | ~ spl7_4
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f366,f352,f93,f400])).

fof(f93,plain,
    ( spl7_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f352,plain,
    ( spl7_52
  <=> r2_hidden(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f366,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_4
    | ~ spl7_52 ),
    inference(unit_resulting_resolution,[],[f94,f353,f73])).

fof(f353,plain,
    ( r2_hidden(sK3,u1_struct_0(sK0))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f352])).

fof(f94,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f395,plain,
    ( ~ spl7_57
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_24
    | ~ spl7_26
    | spl7_41
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f302,f296,f286,f213,f194,f86,f79,f393])).

fof(f393,plain,
    ( spl7_57
  <=> ~ r2_waybel_7(sK0,k1_zfmisc_1(o_0_0_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f286,plain,
    ( spl7_41
  <=> ~ r2_hidden(sK4(sK0,sK2,sK3),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f302,plain,
    ( ~ r2_waybel_7(sK0,k1_zfmisc_1(o_0_0_xboole_0),sK3)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_41
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f80,f87,f287,f214,f195,f297,f60])).

fof(f287,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f286])).

fof(f377,plain,
    ( ~ spl7_55
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f363,f352,f375])).

fof(f375,plain,
    ( spl7_55
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f363,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3)
    | ~ spl7_52 ),
    inference(unit_resulting_resolution,[],[f353,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',antisymmetry_r2_hidden)).

fof(f354,plain,
    ( spl7_52
    | spl7_45
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f337,f328,f310,f352])).

fof(f310,plain,
    ( spl7_45
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f328,plain,
    ( spl7_48
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f337,plain,
    ( r2_hidden(sK3,u1_struct_0(sK0))
    | ~ spl7_45
    | ~ spl7_48 ),
    inference(unit_resulting_resolution,[],[f311,f329,f68])).

fof(f329,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f328])).

fof(f311,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f310])).

fof(f344,plain,
    ( ~ spl7_51
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_24
    | ~ spl7_26
    | spl7_31
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f301,f296,f238,f213,f194,f86,f79,f342])).

fof(f342,plain,
    ( spl7_51
  <=> ~ r2_waybel_7(sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f238,plain,
    ( spl7_31
  <=> ~ r2_hidden(sK4(sK0,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f301,plain,
    ( ~ r2_waybel_7(sK0,sK3,sK3)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_31
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f80,f87,f239,f214,f195,f297,f60])).

fof(f239,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,sK3),sK3)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f238])).

fof(f330,plain,
    ( spl7_48
    | ~ spl7_26
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f304,f296,f213,f328])).

fof(f304,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_26
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f214,f297,f72])).

fof(f323,plain,
    ( ~ spl7_47
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f303,f296,f213,f194,f93,f86,f79,f321])).

fof(f321,plain,
    ( spl7_47
  <=> ~ r2_waybel_7(sK0,o_0_0_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f303,plain,
    ( ~ r2_waybel_7(sK0,o_0_0_xboole_0,sK3)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f80,f87,f134,f214,f195,f297,f60])).

fof(f134,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f94,f71])).

fof(f312,plain,
    ( ~ spl7_45
    | ~ spl7_26
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f305,f296,f213,f310])).

fof(f305,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_26
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f214,f297,f73])).

fof(f298,plain,
    ( spl7_42
    | ~ spl7_0
    | ~ spl7_2
    | spl7_13 ),
    inference(avatar_split_clause,[],[f261,f121,f86,f79,f296])).

fof(f121,plain,
    ( spl7_13
  <=> ~ r2_waybel_7(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f261,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f80,f87,f122,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f122,plain,
    ( ~ r2_waybel_7(sK0,sK2,sK3)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f288,plain,
    ( ~ spl7_41
    | spl7_37 ),
    inference(avatar_split_clause,[],[f271,f266,f286])).

fof(f266,plain,
    ( spl7_37
  <=> ~ m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f271,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_37 ),
    inference(unit_resulting_resolution,[],[f267,f67])).

fof(f267,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f266])).

fof(f281,plain,
    ( ~ spl7_39
    | spl7_37 ),
    inference(avatar_split_clause,[],[f269,f266,f279])).

fof(f279,plain,
    ( spl7_39
  <=> ~ r1_tarski(sK4(sK0,sK2,sK3),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f269,plain,
    ( ~ r1_tarski(sK4(sK0,sK2,sK3),o_0_0_xboole_0)
    | ~ spl7_37 ),
    inference(unit_resulting_resolution,[],[f267,f69])).

fof(f268,plain,
    ( ~ spl7_37
    | ~ spl7_4
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f220,f213,f93,f266])).

fof(f220,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2,sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_4
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f94,f214,f73])).

fof(f258,plain,
    ( spl7_34
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f218,f213,f256])).

fof(f256,plain,
    ( spl7_34
  <=> m1_subset_1(sK3,sK4(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f218,plain,
    ( m1_subset_1(sK3,sK4(sK0,sK2,sK3))
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f214,f67])).

fof(f250,plain,
    ( ~ spl7_33
    | ~ spl7_0
    | ~ spl7_2
    | spl7_13 ),
    inference(avatar_split_clause,[],[f241,f121,f86,f79,f248])).

fof(f241,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,sK3),sK2)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f122,f87,f80,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ l1_pre_topc(X0)
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f240,plain,
    ( ~ spl7_31
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f217,f213,f238])).

fof(f217,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,sK3),sK3)
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f214,f66])).

fof(f231,plain,
    ( ~ spl7_29
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f219,f213,f229])).

fof(f229,plain,
    ( spl7_29
  <=> ~ v1_xboole_0(sK4(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f219,plain,
    ( ~ v1_xboole_0(sK4(sK0,sK2,sK3))
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f214,f71])).

fof(f215,plain,
    ( spl7_26
    | ~ spl7_0
    | ~ spl7_2
    | spl7_13 ),
    inference(avatar_split_clause,[],[f206,f121,f86,f79,f213])).

fof(f206,plain,
    ( r2_hidden(sK3,sK4(sK0,sK2,sK3))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f122,f87,f80,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | r2_hidden(X2,sK4(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f196,plain,
    ( spl7_24
    | ~ spl7_0
    | ~ spl7_2
    | spl7_13 ),
    inference(avatar_split_clause,[],[f189,f121,f86,f79,f194])).

fof(f189,plain,
    ( v3_pre_topc(sK4(sK0,sK2,sK3),sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f80,f87,f122,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK4(X0,X1,X2),X0)
      | r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f187,plain,
    ( spl7_22
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f180,f177,f185])).

fof(f185,plain,
    ( spl7_22
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f177,plain,
    ( spl7_20
  <=> o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f180,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_20 ),
    inference(superposition,[],[f65,f178])).

fof(f178,plain,
    ( o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f177])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',existence_m1_subset_1)).

fof(f179,plain,
    ( spl7_20
    | ~ spl7_4
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f164,f156,f93,f177])).

fof(f156,plain,
    ( spl7_18
  <=> v1_xboole_0(sK5(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f164,plain,
    ( o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_4
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f157,f126])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f124,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',t6_boole)).

fof(f124,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f94,f59])).

fof(f157,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f156])).

fof(f158,plain,
    ( spl7_18
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f151,f93,f156])).

fof(f151,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f65,f150,f68])).

fof(f150,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f94,f65,f73])).

fof(f144,plain,
    ( spl7_16
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f137,f107,f142])).

fof(f107,plain,
    ( spl7_8
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f137,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f108,f69])).

fof(f108,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f133,plain,
    ( spl7_14
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f124,f93,f131])).

fof(f131,plain,
    ( spl7_14
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f123,plain,(
    ~ spl7_13 ),
    inference(avatar_split_clause,[],[f57,f121])).

fof(f57,plain,(
    ~ r2_waybel_7(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r2_waybel_7(sK0,sK2,sK3)
    & r2_waybel_7(sK0,sK1,sK3)
    & r1_tarski(sK1,sK2)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ~ r2_waybel_7(X0,X2,X3)
            & r2_waybel_7(X0,X1,X3)
            & r1_tarski(X1,X2) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X3,X2,X1] :
          ( ~ r2_waybel_7(sK0,X2,X3)
          & r2_waybel_7(sK0,X1,X3)
          & r1_tarski(X1,X2) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_waybel_7(X0,X2,X3)
          & r2_waybel_7(X0,X1,X3)
          & r1_tarski(X1,X2) )
     => ( ~ r2_waybel_7(X0,sK2,sK3)
        & r2_waybel_7(X0,sK1,sK3)
        & r1_tarski(sK1,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_waybel_7(X0,X2,X3)
          & r2_waybel_7(X0,X1,X3)
          & r1_tarski(X1,X2) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_waybel_7(X0,X2,X3)
          & r2_waybel_7(X0,X1,X3)
          & r1_tarski(X1,X2) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1,X2,X3] :
            ( ( r2_waybel_7(X0,X1,X3)
              & r1_tarski(X1,X2) )
           => r2_waybel_7(X0,X2,X3) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2,X3] :
            ( ( r2_waybel_7(X0,X1,X3)
              & r1_tarski(X1,X2) )
           => r2_waybel_7(X0,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2,X3] :
          ( ( r2_waybel_7(X0,X1,X3)
            & r1_tarski(X1,X2) )
         => r2_waybel_7(X0,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',t22_yellow19)).

fof(f116,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f56,f114])).

fof(f56,plain,(
    r2_waybel_7(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f109,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f55,f107])).

fof(f55,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f102,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f74,f100])).

fof(f100,plain,
    ( spl7_6
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f74,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f12,f51])).

fof(f51,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK6) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',existence_l1_pre_topc)).

fof(f95,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f58,f93])).

fof(f58,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',dt_o_0_0_xboole_0)).

fof(f88,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f54,f86])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f53,f79])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
