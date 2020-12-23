%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t26_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:18 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  402 (1145 expanded)
%              Number of leaves         :   98 ( 485 expanded)
%              Depth                    :   10
%              Number of atoms          : 1157 (3381 expanded)
%              Number of equality atoms :   21 ( 146 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f122,f129,f136,f143,f150,f157,f164,f171,f178,f188,f211,f224,f246,f254,f285,f303,f325,f335,f337,f352,f354,f356,f358,f359,f393,f424,f431,f445,f454,f463,f470,f523,f534,f541,f571,f583,f592,f630,f642,f662,f669,f678,f687,f694,f701,f703,f705,f707,f751,f753,f756,f758,f763,f765,f767,f769,f784,f791,f798,f808,f815,f824,f831,f838,f852,f861,f872,f879,f916,f947,f954,f977,f985,f993,f1010,f1019,f1034,f1041,f1056,f1063,f1101,f1108,f1119,f1121])).

fof(f1121,plain,
    ( ~ spl11_4
    | spl11_97
    | ~ spl11_130 ),
    inference(avatar_contradiction_clause,[],[f1120])).

fof(f1120,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_97
    | ~ spl11_130 ),
    inference(subsumption_resolution,[],[f1118,f864])).

fof(f864,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k4_tarski(X0,X1),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl11_4
    | ~ spl11_97 ),
    inference(unit_resulting_resolution,[],[f286,f860,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',t2_subset)).

fof(f860,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl11_97 ),
    inference(avatar_component_clause,[],[f859])).

fof(f859,plain,
    ( spl11_97
  <=> ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_97])])).

fof(f286,plain,
    ( ! [X2,X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,o_0_0_xboole_0))
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f189,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',t106_zfmisc_1)).

fof(f189,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f128,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',t7_boole)).

fof(f128,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl11_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f1118,plain,
    ( m1_subset_1(k4_tarski(sK3,sK4),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl11_130 ),
    inference(avatar_component_clause,[],[f1117])).

fof(f1117,plain,
    ( spl11_130
  <=> m1_subset_1(k4_tarski(sK3,sK4),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_130])])).

fof(f1119,plain,
    ( spl11_130
    | ~ spl11_30
    | ~ spl11_56
    | ~ spl11_72 ),
    inference(avatar_split_clause,[],[f746,f667,f532,f277,f1117])).

fof(f277,plain,
    ( spl11_30
  <=> u1_struct_0(sK2) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f532,plain,
    ( spl11_56
  <=> r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f667,plain,
    ( spl11_72
  <=> m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_72])])).

fof(f746,plain,
    ( m1_subset_1(k4_tarski(sK3,sK4),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl11_30
    | ~ spl11_56
    | ~ spl11_72 ),
    inference(backward_demodulation,[],[f278,f697])).

fof(f697,plain,
    ( m1_subset_1(k4_tarski(sK3,sK4),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
    | ~ spl11_56
    | ~ spl11_72 ),
    inference(unit_resulting_resolution,[],[f533,f668,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',t4_subset)).

fof(f668,plain,
    ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ spl11_72 ),
    inference(avatar_component_clause,[],[f667])).

fof(f533,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2))
    | ~ spl11_56 ),
    inference(avatar_component_clause,[],[f532])).

fof(f278,plain,
    ( u1_struct_0(sK2) = o_0_0_xboole_0
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f277])).

fof(f1108,plain,
    ( ~ spl11_129
    | ~ spl11_122 ),
    inference(avatar_split_clause,[],[f1065,f1054,f1106])).

fof(f1106,plain,
    ( spl11_129
  <=> ~ r2_hidden(u1_orders_2(sK2),sK9(u1_orders_2(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_129])])).

fof(f1054,plain,
    ( spl11_122
  <=> r2_hidden(sK9(u1_orders_2(sK2)),u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_122])])).

fof(f1065,plain,
    ( ~ r2_hidden(u1_orders_2(sK2),sK9(u1_orders_2(sK2)))
    | ~ spl11_122 ),
    inference(unit_resulting_resolution,[],[f1055,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',antisymmetry_r2_hidden)).

fof(f1055,plain,
    ( r2_hidden(sK9(u1_orders_2(sK2)),u1_orders_2(sK2))
    | ~ spl11_122 ),
    inference(avatar_component_clause,[],[f1054])).

fof(f1101,plain,
    ( ~ spl11_127
    | ~ spl11_30
    | spl11_55 ),
    inference(avatar_split_clause,[],[f738,f521,f277,f1099])).

fof(f1099,plain,
    ( spl11_127
  <=> ~ r2_hidden(o_0_0_xboole_0,sK9(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_127])])).

fof(f521,plain,
    ( spl11_55
  <=> ~ r2_hidden(u1_struct_0(sK2),sK9(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_55])])).

fof(f738,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK9(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl11_30
    | ~ spl11_55 ),
    inference(backward_demodulation,[],[f278,f522])).

fof(f522,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK9(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl11_55 ),
    inference(avatar_component_clause,[],[f521])).

fof(f1063,plain,
    ( ~ spl11_125
    | spl11_61
    | spl11_67 ),
    inference(avatar_split_clause,[],[f634,f628,f569,f1061])).

fof(f1061,plain,
    ( spl11_125
  <=> ~ m1_subset_1(k4_tarski(sK3,sK5),u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_125])])).

fof(f569,plain,
    ( spl11_61
  <=> ~ v1_xboole_0(u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_61])])).

fof(f628,plain,
    ( spl11_67
  <=> ~ r2_hidden(k4_tarski(sK3,sK5),u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_67])])).

fof(f634,plain,
    ( ~ m1_subset_1(k4_tarski(sK3,sK5),u1_orders_2(sK2))
    | ~ spl11_61
    | ~ spl11_67 ),
    inference(unit_resulting_resolution,[],[f570,f629,f99])).

fof(f629,plain,
    ( ~ r2_hidden(k4_tarski(sK3,sK5),u1_orders_2(sK2))
    | ~ spl11_67 ),
    inference(avatar_component_clause,[],[f628])).

fof(f570,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK2))
    | ~ spl11_61 ),
    inference(avatar_component_clause,[],[f569])).

fof(f1056,plain,
    ( spl11_122
    | spl11_61 ),
    inference(avatar_split_clause,[],[f572,f569,f1054])).

fof(f572,plain,
    ( r2_hidden(sK9(u1_orders_2(sK2)),u1_orders_2(sK2))
    | ~ spl11_61 ),
    inference(unit_resulting_resolution,[],[f96,f570,f99])).

fof(f96,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f19,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',existence_m1_subset_1)).

fof(f1041,plain,
    ( spl11_120
    | ~ spl11_58 ),
    inference(avatar_split_clause,[],[f598,f539,f1039])).

fof(f1039,plain,
    ( spl11_120
  <=> m1_subset_1(k4_tarski(sK4,sK5),u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_120])])).

fof(f539,plain,
    ( spl11_58
  <=> r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f598,plain,
    ( m1_subset_1(k4_tarski(sK4,sK5),u1_orders_2(sK2))
    | ~ spl11_58 ),
    inference(unit_resulting_resolution,[],[f540,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',t1_subset)).

fof(f540,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK2))
    | ~ spl11_58 ),
    inference(avatar_component_clause,[],[f539])).

fof(f1034,plain,
    ( ~ spl11_119
    | ~ spl11_58 ),
    inference(avatar_split_clause,[],[f597,f539,f1032])).

fof(f1032,plain,
    ( spl11_119
  <=> ~ r2_hidden(u1_orders_2(sK2),k4_tarski(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_119])])).

fof(f597,plain,
    ( ~ r2_hidden(u1_orders_2(sK2),k4_tarski(sK4,sK5))
    | ~ spl11_58 ),
    inference(unit_resulting_resolution,[],[f540,f97])).

fof(f1019,plain,
    ( ~ spl11_117
    | spl11_115 ),
    inference(avatar_split_clause,[],[f1012,f1008,f1017])).

fof(f1017,plain,
    ( spl11_117
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_117])])).

fof(f1008,plain,
    ( spl11_115
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_115])])).

fof(f1012,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_115 ),
    inference(unit_resulting_resolution,[],[f1009,f98])).

fof(f1009,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_115 ),
    inference(avatar_component_clause,[],[f1008])).

fof(f1010,plain,
    ( ~ spl11_115
    | ~ spl11_4
    | ~ spl11_98 ),
    inference(avatar_split_clause,[],[f926,f867,f127,f1008])).

fof(f867,plain,
    ( spl11_98
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_98])])).

fof(f926,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_4
    | ~ spl11_98 ),
    inference(unit_resulting_resolution,[],[f128,f868,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',t5_subset)).

fof(f868,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_98 ),
    inference(avatar_component_clause,[],[f867])).

fof(f993,plain,
    ( spl11_112
    | ~ spl11_4
    | ~ spl11_110 ),
    inference(avatar_split_clause,[],[f986,f983,f127,f991])).

fof(f991,plain,
    ( spl11_112
  <=> r8_relat_2(u1_orders_2(sK10),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_112])])).

fof(f983,plain,
    ( spl11_110
  <=> sP1(u1_orders_2(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_110])])).

fof(f986,plain,
    ( r8_relat_2(u1_orders_2(sK10),o_0_0_xboole_0)
    | ~ spl11_4
    | ~ spl11_110 ),
    inference(unit_resulting_resolution,[],[f194,f984,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r8_relat_2(X0,X1)
      | ~ sP0(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | ~ r8_relat_2(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f984,plain,
    ( sP1(u1_orders_2(sK10))
    | ~ spl11_110 ),
    inference(avatar_component_clause,[],[f983])).

fof(f194,plain,
    ( ! [X0] : sP0(X0,o_0_0_xboole_0)
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f189,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK8(X0,X1)),X0)
          & r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
          & r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
          & r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X1) ) )
      & ( ! [X5,X6,X7] :
            ( r2_hidden(k4_tarski(X5,X7),X0)
            | ~ r2_hidden(k4_tarski(X6,X7),X0)
            | ~ r2_hidden(k4_tarski(X5,X6),X0)
            | ~ r2_hidden(X7,X1)
            | ~ r2_hidden(X6,X1)
            | ~ r2_hidden(X5,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f60,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2,X3,X4] :
          ( ~ r2_hidden(k4_tarski(X2,X4),X0)
          & r2_hidden(k4_tarski(X3,X4),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X4,X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK8(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
        & r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3,X4] :
            ( ~ r2_hidden(k4_tarski(X2,X4),X0)
            & r2_hidden(k4_tarski(X3,X4),X0)
            & r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(X4,X1)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) ) )
      & ( ! [X5,X6,X7] :
            ( r2_hidden(k4_tarski(X5,X7),X0)
            | ~ r2_hidden(k4_tarski(X6,X7),X0)
            | ~ r2_hidden(k4_tarski(X5,X6),X0)
            | ~ r2_hidden(X7,X1)
            | ~ r2_hidden(X6,X1)
            | ~ r2_hidden(X5,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3,X4] :
            ( ~ r2_hidden(k4_tarski(X2,X4),X0)
            & r2_hidden(k4_tarski(X3,X4),X0)
            & r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(X4,X1)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) ) )
      & ( ! [X2,X3,X4] :
            ( r2_hidden(k4_tarski(X2,X4),X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2,X3,X4] :
          ( r2_hidden(k4_tarski(X2,X4),X0)
          | ~ r2_hidden(k4_tarski(X3,X4),X0)
          | ~ r2_hidden(k4_tarski(X2,X3),X0)
          | ~ r2_hidden(X4,X1)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f985,plain,
    ( spl11_110
    | ~ spl11_108 ),
    inference(avatar_split_clause,[],[f978,f975,f983])).

fof(f975,plain,
    ( spl11_108
  <=> v1_relat_1(u1_orders_2(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_108])])).

fof(f978,plain,
    ( sP1(u1_orders_2(sK10))
    | ~ spl11_108 ),
    inference(unit_resulting_resolution,[],[f976,f89])).

fof(f89,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f35,f51,f50])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( ( r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => r2_hidden(k4_tarski(X2,X4),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',d8_relat_2)).

fof(f976,plain,
    ( v1_relat_1(u1_orders_2(sK10))
    | ~ spl11_108 ),
    inference(avatar_component_clause,[],[f975])).

fof(f977,plain,
    ( spl11_108
    | ~ spl11_106 ),
    inference(avatar_split_clause,[],[f969,f952,f975])).

fof(f952,plain,
    ( spl11_106
  <=> m1_subset_1(u1_orders_2(sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_106])])).

fof(f969,plain,
    ( v1_relat_1(u1_orders_2(sK10))
    | ~ spl11_106 ),
    inference(unit_resulting_resolution,[],[f953,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',cc1_relset_1)).

fof(f953,plain,
    ( m1_subset_1(u1_orders_2(sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10))))
    | ~ spl11_106 ),
    inference(avatar_component_clause,[],[f952])).

fof(f954,plain,
    ( spl11_106
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f327,f134,f952])).

fof(f134,plain,
    ( spl11_6
  <=> l1_orders_2(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f327,plain,
    ( m1_subset_1(u1_orders_2(sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10))))
    | ~ spl11_6 ),
    inference(unit_resulting_resolution,[],[f135,f90])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',dt_u1_orders_2)).

fof(f135,plain,
    ( l1_orders_2(sK10)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f947,plain,
    ( ~ spl11_105
    | ~ spl11_98 ),
    inference(avatar_split_clause,[],[f924,f867,f945])).

fof(f945,plain,
    ( spl11_105
  <=> ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_105])])).

fof(f924,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_98 ),
    inference(unit_resulting_resolution,[],[f868,f101])).

fof(f916,plain,
    ( spl11_102
    | ~ spl11_4
    | ~ spl11_28
    | spl11_99 ),
    inference(avatar_split_clause,[],[f890,f870,f252,f127,f914])).

fof(f914,plain,
    ( spl11_102
  <=> m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_102])])).

fof(f252,plain,
    ( spl11_28
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f870,plain,
    ( spl11_99
  <=> ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_99])])).

fof(f890,plain,
    ( m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl11_4
    | ~ spl11_28
    | ~ spl11_99 ),
    inference(backward_demodulation,[],[f886,f253])).

fof(f253,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f252])).

fof(f886,plain,
    ( o_0_0_xboole_0 = k1_zfmisc_1(o_0_0_xboole_0)
    | ~ spl11_4
    | ~ spl11_28
    | ~ spl11_99 ),
    inference(unit_resulting_resolution,[],[f253,f871,f199])).

fof(f199,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,X4)
        | r2_hidden(X3,X4)
        | o_0_0_xboole_0 = X4 )
    | ~ spl11_4 ),
    inference(resolution,[],[f99,f181])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl11_4 ),
    inference(backward_demodulation,[],[f179,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',t6_boole)).

fof(f179,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f128,f95])).

fof(f871,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_99 ),
    inference(avatar_component_clause,[],[f870])).

fof(f879,plain,
    ( ~ spl11_101
    | ~ spl11_30
    | spl11_53 ),
    inference(avatar_split_clause,[],[f729,f468,f277,f877])).

fof(f877,plain,
    ( spl11_101
  <=> ~ r2_hidden(o_0_0_xboole_0,sK9(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_101])])).

fof(f468,plain,
    ( spl11_53
  <=> ~ r2_hidden(u1_struct_0(sK2),sK9(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_53])])).

fof(f729,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK9(o_0_0_xboole_0))
    | ~ spl11_30
    | ~ spl11_53 ),
    inference(backward_demodulation,[],[f278,f469])).

fof(f469,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK9(u1_struct_0(sK2)))
    | ~ spl11_53 ),
    inference(avatar_component_clause,[],[f468])).

fof(f872,plain,
    ( ~ spl11_99
    | ~ spl11_30
    | spl11_49 ),
    inference(avatar_split_clause,[],[f725,f452,f277,f870])).

fof(f452,plain,
    ( spl11_49
  <=> ~ r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_49])])).

fof(f725,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_30
    | ~ spl11_49 ),
    inference(backward_demodulation,[],[f278,f453])).

fof(f453,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_49 ),
    inference(avatar_component_clause,[],[f452])).

fof(f861,plain,
    ( ~ spl11_97
    | ~ spl11_30
    | ~ spl11_56
    | ~ spl11_72 ),
    inference(avatar_split_clause,[],[f748,f667,f532,f277,f859])).

fof(f748,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl11_30
    | ~ spl11_56
    | ~ spl11_72 ),
    inference(backward_demodulation,[],[f278,f699])).

fof(f699,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
    | ~ spl11_56
    | ~ spl11_72 ),
    inference(unit_resulting_resolution,[],[f533,f668,f104])).

fof(f852,plain,
    ( spl11_94
    | ~ spl11_30
    | ~ spl11_72 ),
    inference(avatar_split_clause,[],[f745,f667,f277,f850])).

fof(f850,plain,
    ( spl11_94
  <=> m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_94])])).

fof(f745,plain,
    ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl11_30
    | ~ spl11_72 ),
    inference(backward_demodulation,[],[f278,f668])).

fof(f838,plain,
    ( spl11_92
    | ~ spl11_22
    | ~ spl11_30 ),
    inference(avatar_split_clause,[],[f711,f277,f209,f836])).

fof(f836,plain,
    ( spl11_92
  <=> r8_relat_2(u1_orders_2(sK2),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_92])])).

fof(f209,plain,
    ( spl11_22
  <=> r8_relat_2(u1_orders_2(sK2),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f711,plain,
    ( r8_relat_2(u1_orders_2(sK2),o_0_0_xboole_0)
    | ~ spl11_22
    | ~ spl11_30 ),
    inference(backward_demodulation,[],[f278,f210])).

fof(f210,plain,
    ( r8_relat_2(u1_orders_2(sK2),u1_struct_0(sK2))
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f209])).

fof(f831,plain,
    ( ~ spl11_91
    | ~ spl11_30
    | spl11_45 ),
    inference(avatar_split_clause,[],[f720,f429,f277,f829])).

fof(f829,plain,
    ( spl11_91
  <=> ~ r2_hidden(o_0_0_xboole_0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_91])])).

fof(f429,plain,
    ( spl11_45
  <=> ~ r2_hidden(u1_struct_0(sK2),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).

fof(f720,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK5)
    | ~ spl11_30
    | ~ spl11_45 ),
    inference(backward_demodulation,[],[f278,f430])).

fof(f430,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK5)
    | ~ spl11_45 ),
    inference(avatar_component_clause,[],[f429])).

fof(f824,plain,
    ( ~ spl11_89
    | ~ spl11_30
    | spl11_43 ),
    inference(avatar_split_clause,[],[f719,f422,f277,f822])).

fof(f822,plain,
    ( spl11_89
  <=> ~ r2_hidden(o_0_0_xboole_0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_89])])).

fof(f422,plain,
    ( spl11_43
  <=> ~ r2_hidden(u1_struct_0(sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_43])])).

fof(f719,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK4)
    | ~ spl11_30
    | ~ spl11_43 ),
    inference(backward_demodulation,[],[f278,f423])).

fof(f423,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK4)
    | ~ spl11_43 ),
    inference(avatar_component_clause,[],[f422])).

fof(f815,plain,
    ( ~ spl11_87
    | ~ spl11_30
    | spl11_41 ),
    inference(avatar_split_clause,[],[f716,f391,f277,f813])).

fof(f813,plain,
    ( spl11_87
  <=> ~ r2_hidden(o_0_0_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_87])])).

fof(f391,plain,
    ( spl11_41
  <=> ~ r2_hidden(u1_struct_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).

fof(f716,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK3)
    | ~ spl11_30
    | ~ spl11_41 ),
    inference(backward_demodulation,[],[f278,f392])).

fof(f392,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK3)
    | ~ spl11_41 ),
    inference(avatar_component_clause,[],[f391])).

fof(f808,plain,
    ( spl11_74
    | ~ spl11_72 ),
    inference(avatar_split_clause,[],[f695,f667,f673])).

fof(f673,plain,
    ( spl11_74
  <=> v1_relat_1(u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_74])])).

fof(f695,plain,
    ( v1_relat_1(u1_orders_2(sK2))
    | ~ spl11_72 ),
    inference(unit_resulting_resolution,[],[f668,f102])).

fof(f798,plain,
    ( spl11_84
    | ~ spl11_12
    | ~ spl11_30 ),
    inference(avatar_split_clause,[],[f710,f277,f155,f796])).

fof(f796,plain,
    ( spl11_84
  <=> m1_subset_1(sK5,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_84])])).

fof(f155,plain,
    ( spl11_12
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f710,plain,
    ( m1_subset_1(sK5,o_0_0_xboole_0)
    | ~ spl11_12
    | ~ spl11_30 ),
    inference(backward_demodulation,[],[f278,f156])).

fof(f156,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f791,plain,
    ( spl11_82
    | ~ spl11_10
    | ~ spl11_30 ),
    inference(avatar_split_clause,[],[f709,f277,f148,f789])).

fof(f789,plain,
    ( spl11_82
  <=> m1_subset_1(sK4,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_82])])).

fof(f148,plain,
    ( spl11_10
  <=> m1_subset_1(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f709,plain,
    ( m1_subset_1(sK4,o_0_0_xboole_0)
    | ~ spl11_10
    | ~ spl11_30 ),
    inference(backward_demodulation,[],[f278,f149])).

fof(f149,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f148])).

fof(f784,plain,
    ( spl11_80
    | ~ spl11_8
    | ~ spl11_30 ),
    inference(avatar_split_clause,[],[f708,f277,f141,f782])).

fof(f782,plain,
    ( spl11_80
  <=> m1_subset_1(sK3,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_80])])).

fof(f141,plain,
    ( spl11_8
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f708,plain,
    ( m1_subset_1(sK3,o_0_0_xboole_0)
    | ~ spl11_8
    | ~ spl11_30 ),
    inference(backward_demodulation,[],[f278,f142])).

fof(f142,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f141])).

fof(f769,plain,
    ( ~ spl11_4
    | ~ spl11_30
    | ~ spl11_50
    | ~ spl11_58 ),
    inference(avatar_contradiction_clause,[],[f768])).

fof(f768,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_30
    | ~ spl11_50
    | ~ spl11_58 ),
    inference(subsumption_resolution,[],[f743,f256])).

fof(f256,plain,
    ( ! [X2,X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(o_0_0_xboole_0,X2))
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f189,f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f743,plain,
    ( r2_hidden(k4_tarski(sK9(o_0_0_xboole_0),k4_tarski(sK4,sK5)),k2_zfmisc_1(o_0_0_xboole_0,u1_orders_2(sK2)))
    | ~ spl11_30
    | ~ spl11_50
    | ~ spl11_58 ),
    inference(backward_demodulation,[],[f278,f611])).

fof(f611,plain,
    ( r2_hidden(k4_tarski(sK9(u1_struct_0(sK2)),k4_tarski(sK4,sK5)),k2_zfmisc_1(u1_struct_0(sK2),u1_orders_2(sK2)))
    | ~ spl11_50
    | ~ spl11_58 ),
    inference(unit_resulting_resolution,[],[f462,f540,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f462,plain,
    ( r2_hidden(sK9(u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ spl11_50 ),
    inference(avatar_component_clause,[],[f461])).

fof(f461,plain,
    ( spl11_50
  <=> r2_hidden(sK9(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f767,plain,
    ( ~ spl11_4
    | ~ spl11_30
    | ~ spl11_50
    | ~ spl11_58 ),
    inference(avatar_contradiction_clause,[],[f766])).

fof(f766,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_30
    | ~ spl11_50
    | ~ spl11_58 ),
    inference(subsumption_resolution,[],[f742,f286])).

fof(f742,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK4,sK5),sK9(o_0_0_xboole_0)),k2_zfmisc_1(u1_orders_2(sK2),o_0_0_xboole_0))
    | ~ spl11_30
    | ~ spl11_50
    | ~ spl11_58 ),
    inference(backward_demodulation,[],[f278,f604])).

fof(f604,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK4,sK5),sK9(u1_struct_0(sK2))),k2_zfmisc_1(u1_orders_2(sK2),u1_struct_0(sK2)))
    | ~ spl11_50
    | ~ spl11_58 ),
    inference(unit_resulting_resolution,[],[f462,f540,f107])).

fof(f765,plain,
    ( ~ spl11_4
    | ~ spl11_30
    | ~ spl11_50
    | ~ spl11_56 ),
    inference(avatar_contradiction_clause,[],[f764])).

fof(f764,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_30
    | ~ spl11_50
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f741,f256])).

fof(f741,plain,
    ( r2_hidden(k4_tarski(sK9(o_0_0_xboole_0),k4_tarski(sK3,sK4)),k2_zfmisc_1(o_0_0_xboole_0,u1_orders_2(sK2)))
    | ~ spl11_30
    | ~ spl11_50
    | ~ spl11_56 ),
    inference(backward_demodulation,[],[f278,f556])).

fof(f556,plain,
    ( r2_hidden(k4_tarski(sK9(u1_struct_0(sK2)),k4_tarski(sK3,sK4)),k2_zfmisc_1(u1_struct_0(sK2),u1_orders_2(sK2)))
    | ~ spl11_50
    | ~ spl11_56 ),
    inference(unit_resulting_resolution,[],[f462,f533,f107])).

fof(f763,plain,
    ( ~ spl11_4
    | ~ spl11_30
    | ~ spl11_50
    | ~ spl11_56 ),
    inference(avatar_contradiction_clause,[],[f762])).

fof(f762,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_30
    | ~ spl11_50
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f740,f286])).

fof(f740,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK3,sK4),sK9(o_0_0_xboole_0)),k2_zfmisc_1(u1_orders_2(sK2),o_0_0_xboole_0))
    | ~ spl11_30
    | ~ spl11_50
    | ~ spl11_56 ),
    inference(backward_demodulation,[],[f278,f550])).

fof(f550,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK3,sK4),sK9(u1_struct_0(sK2))),k2_zfmisc_1(u1_orders_2(sK2),u1_struct_0(sK2)))
    | ~ spl11_50
    | ~ spl11_56 ),
    inference(unit_resulting_resolution,[],[f462,f533,f107])).

fof(f758,plain,
    ( ~ spl11_4
    | ~ spl11_30
    | ~ spl11_50 ),
    inference(avatar_contradiction_clause,[],[f757])).

fof(f757,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_30
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f734,f256])).

fof(f734,plain,
    ( r2_hidden(k4_tarski(sK9(o_0_0_xboole_0),sK9(o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl11_30
    | ~ spl11_50 ),
    inference(backward_demodulation,[],[f278,f496])).

fof(f496,plain,
    ( r2_hidden(k4_tarski(sK9(u1_struct_0(sK2)),sK9(u1_struct_0(sK2))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
    | ~ spl11_50 ),
    inference(unit_resulting_resolution,[],[f462,f462,f107])).

fof(f756,plain,
    ( ~ spl11_4
    | ~ spl11_30
    | ~ spl11_50 ),
    inference(avatar_contradiction_clause,[],[f755])).

fof(f755,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_30
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f733,f128])).

fof(f733,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl11_30
    | ~ spl11_50 ),
    inference(backward_demodulation,[],[f278,f480])).

fof(f480,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl11_50 ),
    inference(resolution,[],[f462,f101])).

fof(f753,plain,
    ( ~ spl11_4
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_50 ),
    inference(avatar_contradiction_clause,[],[f752])).

fof(f752,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f730,f253])).

fof(f730,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_4
    | ~ spl11_30
    | ~ spl11_50 ),
    inference(backward_demodulation,[],[f278,f471])).

fof(f471,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_4
    | ~ spl11_50 ),
    inference(unit_resulting_resolution,[],[f128,f462,f104])).

fof(f751,plain,
    ( ~ spl11_4
    | ~ spl11_30
    | ~ spl11_50 ),
    inference(avatar_contradiction_clause,[],[f750])).

fof(f750,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_30
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f728,f189])).

fof(f728,plain,
    ( r2_hidden(sK9(o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl11_30
    | ~ spl11_50 ),
    inference(backward_demodulation,[],[f278,f462])).

fof(f707,plain,
    ( ~ spl11_34
    | ~ spl11_50 ),
    inference(avatar_contradiction_clause,[],[f706])).

fof(f706,plain,
    ( $false
    | ~ spl11_34
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f299,f480])).

fof(f299,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl11_34
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f705,plain,
    ( ~ spl11_4
    | ~ spl11_46
    | ~ spl11_50 ),
    inference(avatar_contradiction_clause,[],[f704])).

fof(f704,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_46
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f441,f471])).

fof(f441,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f440])).

fof(f440,plain,
    ( spl11_46
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f703,plain,
    ( ~ spl11_72
    | spl11_75 ),
    inference(avatar_contradiction_clause,[],[f702])).

fof(f702,plain,
    ( $false
    | ~ spl11_72
    | ~ spl11_75 ),
    inference(subsumption_resolution,[],[f695,f677])).

fof(f677,plain,
    ( ~ v1_relat_1(u1_orders_2(sK2))
    | ~ spl11_75 ),
    inference(avatar_component_clause,[],[f676])).

fof(f676,plain,
    ( spl11_75
  <=> ~ v1_relat_1(u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_75])])).

fof(f701,plain,
    ( ~ spl11_72
    | spl11_75 ),
    inference(avatar_contradiction_clause,[],[f696])).

fof(f696,plain,
    ( $false
    | ~ spl11_72
    | ~ spl11_75 ),
    inference(unit_resulting_resolution,[],[f677,f668,f102])).

fof(f694,plain,
    ( spl11_78
    | ~ spl11_56 ),
    inference(avatar_split_clause,[],[f544,f532,f692])).

fof(f692,plain,
    ( spl11_78
  <=> m1_subset_1(k4_tarski(sK3,sK4),u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_78])])).

fof(f544,plain,
    ( m1_subset_1(k4_tarski(sK3,sK4),u1_orders_2(sK2))
    | ~ spl11_56 ),
    inference(unit_resulting_resolution,[],[f533,f98])).

fof(f687,plain,
    ( ~ spl11_77
    | ~ spl11_56 ),
    inference(avatar_split_clause,[],[f543,f532,f685])).

fof(f685,plain,
    ( spl11_77
  <=> ~ r2_hidden(u1_orders_2(sK2),k4_tarski(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_77])])).

fof(f543,plain,
    ( ~ r2_hidden(u1_orders_2(sK2),k4_tarski(sK3,sK4))
    | ~ spl11_56 ),
    inference(unit_resulting_resolution,[],[f533,f97])).

fof(f678,plain,
    ( ~ spl11_75
    | spl11_71 ),
    inference(avatar_split_clause,[],[f670,f660,f676])).

fof(f660,plain,
    ( spl11_71
  <=> ~ sP1(u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_71])])).

fof(f670,plain,
    ( ~ v1_relat_1(u1_orders_2(sK2))
    | ~ spl11_71 ),
    inference(unit_resulting_resolution,[],[f661,f89])).

fof(f661,plain,
    ( ~ sP1(u1_orders_2(sK2))
    | ~ spl11_71 ),
    inference(avatar_component_clause,[],[f660])).

fof(f669,plain,
    ( spl11_72
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f326,f120,f667])).

fof(f120,plain,
    ( spl11_2
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f326,plain,
    ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f121,f90])).

fof(f121,plain,
    ( l1_orders_2(sK2)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f662,plain,
    ( ~ spl11_71
    | ~ spl11_22
    | spl11_69 ),
    inference(avatar_split_clause,[],[f643,f640,f209,f660])).

fof(f640,plain,
    ( spl11_69
  <=> ~ sP0(u1_orders_2(sK2),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_69])])).

fof(f643,plain,
    ( ~ sP1(u1_orders_2(sK2))
    | ~ spl11_22
    | ~ spl11_69 ),
    inference(unit_resulting_resolution,[],[f210,f641,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f641,plain,
    ( ~ sP0(u1_orders_2(sK2),u1_struct_0(sK2))
    | ~ spl11_69 ),
    inference(avatar_component_clause,[],[f640])).

fof(f642,plain,
    ( ~ spl11_69
    | ~ spl11_32
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_56
    | ~ spl11_58
    | spl11_67 ),
    inference(avatar_split_clause,[],[f635,f628,f539,f532,f333,f323,f283,f640])).

fof(f283,plain,
    ( spl11_32
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f323,plain,
    ( spl11_36
  <=> r2_hidden(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).

fof(f333,plain,
    ( spl11_38
  <=> r2_hidden(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f635,plain,
    ( ~ sP0(u1_orders_2(sK2),u1_struct_0(sK2))
    | ~ spl11_32
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_56
    | ~ spl11_58
    | ~ spl11_67 ),
    inference(unit_resulting_resolution,[],[f334,f284,f324,f533,f540,f629,f82])).

fof(f82,plain,(
    ! [X6,X0,X7,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X6,X7),X0)
      | r2_hidden(k4_tarski(X5,X7),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f324,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | ~ spl11_36 ),
    inference(avatar_component_clause,[],[f323])).

fof(f284,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl11_32 ),
    inference(avatar_component_clause,[],[f283])).

fof(f334,plain,
    ( r2_hidden(sK5,u1_struct_0(sK2))
    | ~ spl11_38 ),
    inference(avatar_component_clause,[],[f333])).

fof(f630,plain,
    ( ~ spl11_67
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_12
    | spl11_19 ),
    inference(avatar_split_clause,[],[f574,f176,f155,f141,f120,f628])).

fof(f176,plain,
    ( spl11_19
  <=> ~ r1_orders_2(sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f574,plain,
    ( ~ r2_hidden(k4_tarski(sK3,sK5),u1_orders_2(sK2))
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_12
    | ~ spl11_19 ),
    inference(unit_resulting_resolution,[],[f121,f142,f177,f156,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',d9_orders_2)).

fof(f177,plain,
    ( ~ r1_orders_2(sK2,sK3,sK5)
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f176])).

fof(f592,plain,
    ( ~ spl11_65
    | spl11_63 ),
    inference(avatar_split_clause,[],[f585,f581,f590])).

fof(f590,plain,
    ( spl11_65
  <=> ~ r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_65])])).

fof(f581,plain,
    ( spl11_63
  <=> ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_63])])).

fof(f585,plain,
    ( ~ r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_63 ),
    inference(unit_resulting_resolution,[],[f582,f98])).

fof(f582,plain,
    ( ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_63 ),
    inference(avatar_component_clause,[],[f581])).

fof(f583,plain,
    ( ~ spl11_63
    | ~ spl11_4
    | ~ spl11_56 ),
    inference(avatar_split_clause,[],[f546,f532,f127,f581])).

fof(f546,plain,
    ( ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_4
    | ~ spl11_56 ),
    inference(unit_resulting_resolution,[],[f128,f533,f104])).

fof(f571,plain,
    ( ~ spl11_61
    | ~ spl11_56 ),
    inference(avatar_split_clause,[],[f545,f532,f569])).

fof(f545,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK2))
    | ~ spl11_56 ),
    inference(unit_resulting_resolution,[],[f533,f101])).

fof(f541,plain,
    ( spl11_58
    | ~ spl11_2
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f525,f169,f155,f148,f120,f539])).

fof(f169,plain,
    ( spl11_16
  <=> r1_orders_2(sK2,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f525,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK2))
    | ~ spl11_2
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16 ),
    inference(unit_resulting_resolution,[],[f121,f149,f170,f156,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f170,plain,
    ( r1_orders_2(sK2,sK4,sK5)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f169])).

fof(f534,plain,
    ( spl11_56
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f524,f162,f148,f141,f120,f532])).

fof(f162,plain,
    ( spl11_14
  <=> r1_orders_2(sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f524,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2))
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_14 ),
    inference(unit_resulting_resolution,[],[f121,f142,f163,f149,f93])).

fof(f163,plain,
    ( r1_orders_2(sK2,sK3,sK4)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f162])).

fof(f523,plain,
    ( ~ spl11_55
    | spl11_47 ),
    inference(avatar_split_clause,[],[f446,f443,f521])).

fof(f443,plain,
    ( spl11_47
  <=> ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_47])])).

fof(f446,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK9(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl11_47 ),
    inference(unit_resulting_resolution,[],[f96,f444,f103])).

fof(f444,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_47 ),
    inference(avatar_component_clause,[],[f443])).

fof(f470,plain,
    ( ~ spl11_53
    | ~ spl11_4
    | spl11_31 ),
    inference(avatar_split_clause,[],[f369,f274,f127,f468])).

fof(f274,plain,
    ( spl11_31
  <=> u1_struct_0(sK2) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f369,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK9(u1_struct_0(sK2)))
    | ~ spl11_4
    | ~ spl11_31 ),
    inference(unit_resulting_resolution,[],[f275,f268])).

fof(f268,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,sK9(X5))
        | o_0_0_xboole_0 = X5 )
    | ~ spl11_4 ),
    inference(resolution,[],[f262,f97])).

fof(f262,plain,
    ( ! [X0] :
        ( r2_hidden(sK9(X0),X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl11_4 ),
    inference(resolution,[],[f199,f96])).

fof(f275,plain,
    ( u1_struct_0(sK2) != o_0_0_xboole_0
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f274])).

fof(f463,plain,
    ( spl11_50
    | spl11_35 ),
    inference(avatar_split_clause,[],[f360,f301,f461])).

fof(f301,plain,
    ( spl11_35
  <=> ~ v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f360,plain,
    ( r2_hidden(sK9(u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ spl11_35 ),
    inference(unit_resulting_resolution,[],[f96,f302,f99])).

fof(f302,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl11_35 ),
    inference(avatar_component_clause,[],[f301])).

fof(f454,plain,
    ( ~ spl11_49
    | spl11_47 ),
    inference(avatar_split_clause,[],[f447,f443,f452])).

fof(f447,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_47 ),
    inference(unit_resulting_resolution,[],[f444,f98])).

fof(f445,plain,
    ( ~ spl11_47
    | ~ spl11_4
    | ~ spl11_32 ),
    inference(avatar_split_clause,[],[f309,f283,f127,f443])).

fof(f309,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_4
    | ~ spl11_32 ),
    inference(unit_resulting_resolution,[],[f128,f284,f104])).

fof(f431,plain,
    ( ~ spl11_45
    | ~ spl11_38 ),
    inference(avatar_split_clause,[],[f407,f333,f429])).

fof(f407,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK5)
    | ~ spl11_38 ),
    inference(unit_resulting_resolution,[],[f334,f97])).

fof(f424,plain,
    ( ~ spl11_43
    | ~ spl11_36 ),
    inference(avatar_split_clause,[],[f397,f323,f422])).

fof(f397,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK4)
    | ~ spl11_36 ),
    inference(unit_resulting_resolution,[],[f324,f97])).

fof(f393,plain,
    ( ~ spl11_41
    | ~ spl11_32 ),
    inference(avatar_split_clause,[],[f312,f283,f391])).

fof(f312,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK3)
    | ~ spl11_32 ),
    inference(unit_resulting_resolution,[],[f284,f97])).

fof(f359,plain,
    ( ~ spl11_35
    | ~ spl11_32 ),
    inference(avatar_split_clause,[],[f318,f283,f301])).

fof(f318,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl11_32 ),
    inference(resolution,[],[f284,f101])).

fof(f358,plain,
    ( ~ spl11_4
    | ~ spl11_30
    | ~ spl11_36 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_30
    | ~ spl11_36 ),
    inference(subsumption_resolution,[],[f348,f189])).

fof(f348,plain,
    ( r2_hidden(sK4,o_0_0_xboole_0)
    | ~ spl11_30
    | ~ spl11_36 ),
    inference(backward_demodulation,[],[f278,f324])).

fof(f356,plain,
    ( ~ spl11_4
    | ~ spl11_30
    | ~ spl11_32 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_30
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f347,f128])).

fof(f347,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl11_30
    | ~ spl11_32 ),
    inference(backward_demodulation,[],[f278,f318])).

fof(f354,plain,
    ( ~ spl11_4
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f343,f253])).

fof(f343,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_4
    | ~ spl11_30
    | ~ spl11_32 ),
    inference(backward_demodulation,[],[f278,f309])).

fof(f352,plain,
    ( ~ spl11_4
    | ~ spl11_30
    | ~ spl11_32 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_30
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f342,f189])).

fof(f342,plain,
    ( r2_hidden(sK3,o_0_0_xboole_0)
    | ~ spl11_30
    | ~ spl11_32 ),
    inference(backward_demodulation,[],[f278,f284])).

fof(f337,plain,
    ( ~ spl11_32
    | ~ spl11_34 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f299,f318])).

fof(f335,plain,
    ( spl11_38
    | ~ spl11_4
    | ~ spl11_12
    | spl11_31 ),
    inference(avatar_split_clause,[],[f293,f274,f155,f127,f333])).

fof(f293,plain,
    ( r2_hidden(sK5,u1_struct_0(sK2))
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_31 ),
    inference(unit_resulting_resolution,[],[f156,f275,f199])).

fof(f325,plain,
    ( spl11_36
    | ~ spl11_4
    | ~ spl11_10
    | spl11_31 ),
    inference(avatar_split_clause,[],[f292,f274,f148,f127,f323])).

fof(f292,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_31 ),
    inference(unit_resulting_resolution,[],[f149,f275,f199])).

fof(f303,plain,
    ( ~ spl11_35
    | ~ spl11_4
    | spl11_31 ),
    inference(avatar_split_clause,[],[f296,f274,f127,f301])).

fof(f296,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl11_4
    | ~ spl11_31 ),
    inference(unit_resulting_resolution,[],[f128,f275,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',t8_boole)).

fof(f285,plain,
    ( spl11_30
    | spl11_32
    | ~ spl11_4
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f259,f141,f127,f283,f277])).

fof(f259,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | u1_struct_0(sK2) = o_0_0_xboole_0
    | ~ spl11_4
    | ~ spl11_8 ),
    inference(resolution,[],[f199,f142])).

fof(f254,plain,
    ( spl11_28
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f247,f244,f252])).

fof(f244,plain,
    ( spl11_26
  <=> o_0_0_xboole_0 = sK9(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f247,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_26 ),
    inference(superposition,[],[f96,f245])).

fof(f245,plain,
    ( o_0_0_xboole_0 = sK9(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f244])).

fof(f246,plain,
    ( spl11_26
    | ~ spl11_4
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f230,f222,f127,f244])).

fof(f222,plain,
    ( spl11_24
  <=> v1_xboole_0(sK9(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f230,plain,
    ( o_0_0_xboole_0 = sK9(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_4
    | ~ spl11_24 ),
    inference(unit_resulting_resolution,[],[f223,f181])).

fof(f223,plain,
    ( v1_xboole_0(sK9(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f222])).

fof(f224,plain,
    ( spl11_24
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f214,f127,f222])).

fof(f214,plain,
    ( v1_xboole_0(sK9(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f96,f213,f99])).

fof(f213,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK9(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f128,f96,f104])).

fof(f211,plain,
    ( spl11_22
    | ~ spl11_0
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f204,f120,f113,f209])).

fof(f113,plain,
    ( spl11_0
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f204,plain,
    ( r8_relat_2(u1_orders_2(sK2),u1_struct_0(sK2))
    | ~ spl11_0
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f121,f114,f91])).

fof(f91,plain,(
    ! [X0] :
      ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( ( v4_orders_2(X0)
          | ~ r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v4_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',d5_orders_2)).

fof(f114,plain,
    ( v4_orders_2(sK2)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f113])).

fof(f188,plain,
    ( spl11_20
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f179,f127,f186])).

fof(f186,plain,
    ( spl11_20
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f178,plain,(
    ~ spl11_19 ),
    inference(avatar_split_clause,[],[f78,f176])).

fof(f78,plain,(
    ~ r1_orders_2(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ~ r1_orders_2(sK2,sK3,sK5)
    & r1_orders_2(sK2,sK4,sK5)
    & r1_orders_2(sK2,sK3,sK4)
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v4_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f33,f56,f55,f54,f53])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(sK2,X1,X3)
                  & r1_orders_2(sK2,X2,X3)
                  & r1_orders_2(sK2,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(sK2)) )
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v4_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X1,X3)
                  & r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_orders_2(X0,sK3,X3)
                & r1_orders_2(X0,X2,X3)
                & r1_orders_2(X0,sK3,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X1,X3)
              & r1_orders_2(X0,X2,X3)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r1_orders_2(X0,X1,X3)
            & r1_orders_2(X0,sK4,X3)
            & r1_orders_2(X0,X1,sK4)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r1_orders_2(X0,X2,X3)
          & r1_orders_2(X0,X1,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK5)
        & r1_orders_2(X0,X2,sK5)
        & r1_orders_2(X0,X1,X2)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X1,X3)
                  & r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X1,X3)
                  & r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                     => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',t26_orders_2)).

fof(f171,plain,(
    spl11_16 ),
    inference(avatar_split_clause,[],[f77,f169])).

fof(f77,plain,(
    r1_orders_2(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f164,plain,(
    spl11_14 ),
    inference(avatar_split_clause,[],[f76,f162])).

fof(f76,plain,(
    r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f157,plain,(
    spl11_12 ),
    inference(avatar_split_clause,[],[f75,f155])).

fof(f75,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f150,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f74,f148])).

fof(f74,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f143,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f73,f141])).

fof(f73,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f136,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f108,f134])).

fof(f108,plain,(
    l1_orders_2(sK10) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    l1_orders_2(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f17,f69])).

fof(f69,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK10) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',existence_l1_orders_2)).

fof(f129,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f79,f127])).

fof(f79,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',dt_o_0_0_xboole_0)).

fof(f122,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f72,f120])).

fof(f72,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f115,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f71,f113])).

fof(f71,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
