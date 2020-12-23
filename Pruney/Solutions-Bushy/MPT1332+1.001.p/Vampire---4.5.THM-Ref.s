%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1332+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  240 ( 683 expanded)
%              Number of leaves         :   63 ( 310 expanded)
%              Depth                    :   12
%              Number of atoms          :  929 (3538 expanded)
%              Number of equality atoms :  125 ( 492 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1537,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f92,f97,f101,f110,f115,f120,f125,f130,f135,f143,f148,f165,f181,f227,f244,f264,f282,f283,f290,f307,f320,f321,f338,f354,f355,f356,f432,f891,f917,f1096,f1142,f1161,f1257,f1263,f1401,f1407,f1519,f1530,f1535,f1536])).

fof(f1536,plain,
    ( u1_struct_0(sK0) != k10_relat_1(sK2,u1_struct_0(sK1))
    | k10_relat_1(sK2,sK4(sK0,sK1,sK2)) != k3_subset_1(k10_relat_1(sK2,u1_struct_0(sK1)),k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2))))
    | v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2)))),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1535,plain,
    ( u1_struct_0(sK0) != k10_relat_1(sK2,u1_struct_0(sK1))
    | k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),sK3)) != k3_subset_1(k10_relat_1(sK2,u1_struct_0(sK1)),k10_relat_1(sK2,sK3))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k10_relat_1(sK2,sK3)),sK0)
    | ~ v4_pre_topc(k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),sK3)),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1530,plain,
    ( spl5_105
    | ~ spl5_8
    | ~ spl5_26
    | ~ spl5_44
    | ~ spl5_109 ),
    inference(avatar_split_clause,[],[f1525,f1159,f417,f258,f112,f1132])).

fof(f1132,plain,
    ( spl5_105
  <=> v4_pre_topc(k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).

fof(f112,plain,
    ( spl5_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f258,plain,
    ( spl5_26
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f417,plain,
    ( spl5_44
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f1159,plain,
    ( spl5_109
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f1525,plain,
    ( v4_pre_topc(k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),sK3)),sK0)
    | ~ spl5_8
    | ~ spl5_26
    | ~ spl5_44
    | ~ spl5_109 ),
    inference(unit_resulting_resolution,[],[f260,f418,f1363])).

fof(f1363,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl5_8
    | ~ spl5_109 ),
    inference(forward_demodulation,[],[f1160,f212])).

fof(f212,plain,
    ( ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f114,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f1160,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl5_109 ),
    inference(avatar_component_clause,[],[f1159])).

fof(f418,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f417])).

fof(f260,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f258])).

fof(f1519,plain,
    ( spl5_153
    | ~ spl5_8
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f1513,f304,f112,f1515])).

fof(f1515,plain,
    ( spl5_153
  <=> u1_struct_0(sK0) = k10_relat_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_153])])).

fof(f304,plain,
    ( spl5_31
  <=> u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f1513,plain,
    ( u1_struct_0(sK0) = k10_relat_1(sK2,u1_struct_0(sK1))
    | ~ spl5_8
    | ~ spl5_31 ),
    inference(superposition,[],[f212,f306])).

fof(f306,plain,
    ( u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1))
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f304])).

fof(f1407,plain,
    ( spl5_137
    | ~ spl5_24
    | ~ spl5_35
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f1402,f350,f345,f242,f1404])).

fof(f1404,plain,
    ( spl5_137
  <=> k10_relat_1(sK2,sK4(sK0,sK1,sK2)) = k3_subset_1(k10_relat_1(sK2,u1_struct_0(sK1)),k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).

fof(f242,plain,
    ( spl5_24
  <=> ! [X1,X0] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f345,plain,
    ( spl5_35
  <=> sK4(sK0,sK1,sK2) = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f350,plain,
    ( spl5_36
  <=> k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2)) = k6_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f1402,plain,
    ( k10_relat_1(sK2,sK4(sK0,sK1,sK2)) = k3_subset_1(k10_relat_1(sK2,u1_struct_0(sK1)),k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2))))
    | ~ spl5_24
    | ~ spl5_35
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f936,f347])).

fof(f347,plain,
    ( sK4(sK0,sK1,sK2) = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2)))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f345])).

fof(f936,plain,
    ( k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2)))) = k3_subset_1(k10_relat_1(sK2,u1_struct_0(sK1)),k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2))))
    | ~ spl5_24
    | ~ spl5_36 ),
    inference(superposition,[],[f570,f352])).

fof(f352,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2)) = k6_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f350])).

fof(f570,plain,
    ( ! [X2,X3] : k3_subset_1(k10_relat_1(sK2,X2),k10_relat_1(sK2,k6_subset_1(X2,X3))) = k10_relat_1(sK2,k3_subset_1(X2,k6_subset_1(X2,X3)))
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f569,f193])).

fof(f193,plain,(
    ! [X0,X1] : k3_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f70,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f71])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f70,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f569,plain,
    ( ! [X2,X3] : k3_subset_1(k10_relat_1(sK2,X2),k10_relat_1(sK2,k6_subset_1(X2,X3))) = k10_relat_1(sK2,k6_subset_1(X2,k6_subset_1(X2,X3)))
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f557,f243])).

fof(f243,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f242])).

fof(f557,plain,
    ( ! [X2,X3] : k3_subset_1(k10_relat_1(sK2,X2),k10_relat_1(sK2,k6_subset_1(X2,X3))) = k6_subset_1(k10_relat_1(sK2,X2),k10_relat_1(sK2,k6_subset_1(X2,X3)))
    | ~ spl5_24 ),
    inference(superposition,[],[f193,f243])).

fof(f1401,plain,
    ( spl5_136
    | ~ spl5_24
    | ~ spl5_27
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f1007,f277,f272,f242,f1398])).

fof(f1398,plain,
    ( spl5_136
  <=> k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),sK3)) = k3_subset_1(k10_relat_1(sK2,u1_struct_0(sK1)),k10_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).

fof(f272,plain,
    ( spl5_27
  <=> sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f277,plain,
    ( spl5_28
  <=> k3_subset_1(u1_struct_0(sK1),sK3) = k6_subset_1(u1_struct_0(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f1007,plain,
    ( k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),sK3)) = k3_subset_1(k10_relat_1(sK2,u1_struct_0(sK1)),k10_relat_1(sK2,sK3))
    | ~ spl5_24
    | ~ spl5_27
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f996,f274])).

fof(f274,plain,
    ( sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f272])).

fof(f996,plain,
    ( k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),sK3)) = k3_subset_1(k10_relat_1(sK2,u1_struct_0(sK1)),k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3))))
    | ~ spl5_24
    | ~ spl5_28 ),
    inference(superposition,[],[f991,f279])).

fof(f279,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK3) = k6_subset_1(u1_struct_0(sK1),sK3)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f277])).

fof(f991,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k3_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,k3_subset_1(X0,k6_subset_1(X0,X1))))
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f525,f570])).

fof(f525,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k3_subset_1(k10_relat_1(sK2,X0),k3_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,k6_subset_1(X0,X1))))
    | ~ spl5_24 ),
    inference(superposition,[],[f183,f243])).

fof(f183,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k3_subset_1(X0,k3_subset_1(X0,k6_subset_1(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f70,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1263,plain,
    ( ~ spl5_23
    | ~ spl5_8
    | ~ spl5_12
    | spl5_22 ),
    inference(avatar_split_clause,[],[f1241,f224,f132,f112,f234])).

fof(f234,plain,
    ( spl5_23
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k10_relat_1(sK2,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f132,plain,
    ( spl5_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f224,plain,
    ( spl5_22
  <=> v3_pre_topc(k10_relat_1(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f1241,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k10_relat_1(sK2,sK3)),sK0)
    | ~ spl5_8
    | ~ spl5_12
    | spl5_22 ),
    inference(unit_resulting_resolution,[],[f134,f226,f221,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(f221,plain,
    ( ! [X0] : m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f208,f212])).

fof(f208,plain,
    ( ! [X0] : m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f114,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f226,plain,
    ( ~ v3_pre_topc(k10_relat_1(sK2,sK3),sK0)
    | spl5_22 ),
    inference(avatar_component_clause,[],[f224])).

fof(f134,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f132])).

fof(f1257,plain,
    ( spl5_111
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_49 ),
    inference(avatar_split_clause,[],[f1243,f464,f132,f112,f1167])).

fof(f1167,plain,
    ( spl5_111
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f464,plain,
    ( spl5_49
  <=> v3_pre_topc(k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f1243,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2)))),sK0)
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_49 ),
    inference(unit_resulting_resolution,[],[f134,f466,f221,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f466,plain,
    ( v3_pre_topc(k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2))),sK0)
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f464])).

fof(f1161,plain,
    ( ~ spl5_12
    | ~ spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | ~ spl5_8
    | spl5_109
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f1099,f80,f1159,f112,f117,f122,f127,f132])).

fof(f127,plain,
    ( spl5_11
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f122,plain,
    ( spl5_10
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f117,plain,
    ( spl5_9
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f80,plain,
    ( spl5_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1099,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f81,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v5_pre_topc(X2,X0,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
                    & v4_pre_topc(sK4(X0,X1,X2),X1)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
        & v4_pre_topc(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

fof(f81,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f1142,plain,
    ( spl5_16
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f518,f132,f160])).

fof(f160,plain,
    ( spl5_16
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f518,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f134,f151])).

fof(f151,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f58,f61])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f1096,plain,
    ( ~ spl5_11
    | ~ spl5_4
    | spl5_26
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1094,f89,f258,f94,f127])).

fof(f94,plain,
    ( spl5_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f89,plain,
    ( spl5_3
  <=> v3_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1094,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f91,f68])).

fof(f91,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f917,plain,
    ( spl5_49
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_30
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f906,f460,f293,f112,f99,f464])).

fof(f99,plain,
    ( spl5_5
  <=> ! [X4] :
        ( v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f293,plain,
    ( spl5_30
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f460,plain,
    ( spl5_48
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f906,plain,
    ( v3_pre_topc(k10_relat_1(sK2,k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2))),sK0)
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_30
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f295,f461,f222])).

fof(f222,plain,
    ( ! [X4] :
        ( ~ v3_pre_topc(X4,sK1)
        | v3_pre_topc(k10_relat_1(sK2,X4),sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f100,f212])).

fof(f100,plain,
    ( ! [X4] :
        ( ~ v3_pre_topc(X4,sK1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
        | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK0) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f461,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f460])).

fof(f295,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2)),sK1)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f293])).

fof(f891,plain,
    ( spl5_48
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f882,f350,f460])).

fof(f882,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_36 ),
    inference(superposition,[],[f70,f352])).

fof(f432,plain,
    ( spl5_44
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f431,f277,f417])).

fof(f431,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_28 ),
    inference(superposition,[],[f70,f279])).

fof(f356,plain,
    ( spl5_35
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f343,f287,f345])).

fof(f287,plain,
    ( spl5_29
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f343,plain,
    ( sK4(sK0,sK1,sK2) = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2)))
    | ~ spl5_29 ),
    inference(resolution,[],[f289,f73])).

fof(f289,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f287])).

fof(f355,plain,
    ( spl5_36
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f342,f287,f350])).

fof(f342,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2)) = k6_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2))
    | ~ spl5_29 ),
    inference(resolution,[],[f289,f78])).

fof(f354,plain,
    ( spl5_30
    | ~ spl5_11
    | ~ spl5_25
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f339,f287,f248,f127,f293])).

fof(f248,plain,
    ( spl5_25
  <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f339,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK4(sK0,sK1,sK2)),sK1)
    | ~ spl5_11
    | ~ spl5_25
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f129,f250,f289,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f250,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f248])).

fof(f129,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f127])).

fof(f338,plain,
    ( ~ spl5_34
    | spl5_1
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f333,f132,f127,f122,f117,f112,f80,f335])).

fof(f335,plain,
    ( spl5_34
  <=> v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f333,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | spl5_1
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f331,f212])).

fof(f331,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0)
    | spl5_1
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f134,f129,f124,f82,f119,f114,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f119,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f82,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f124,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f321,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | k1_xboole_0 != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_xboole_0)
    | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f320,plain,
    ( spl5_32
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f315,f145,f140,f122,f117,f112,f107,f103,f317])).

fof(f317,plain,
    ( spl5_32
  <=> k1_xboole_0 = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f103,plain,
    ( spl5_6
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f107,plain,
    ( spl5_7
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f140,plain,
    ( spl5_13
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f145,plain,
    ( spl5_14
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f315,plain,
    ( k1_xboole_0 = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f313,f104])).

fof(f104,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f313,plain,
    ( k1_xboole_0 = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f142,f147,f124,f119,f114,f109,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | k1_xboole_0 = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(inner_rewriting,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k2_struct_0(X1) = k1_xboole_0
                 => k2_struct_0(X0) = k1_xboole_0 )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

fof(f109,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f147,plain,
    ( l1_struct_0(sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f145])).

fof(f142,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f140])).

fof(f307,plain,
    ( spl5_31
    | spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f302,f160,f155,f145,f140,f122,f117,f112,f103,f304])).

fof(f155,plain,
    ( spl5_15
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f302,plain,
    ( u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1))
    | spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f301,f162])).

fof(f162,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f160])).

fof(f301,plain,
    ( k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1))
    | spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f299,f157])).

fof(f157,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f155])).

fof(f299,plain,
    ( k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f142,f147,f124,f105,f119,f114,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f105,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f290,plain,
    ( spl5_29
    | spl5_1
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f284,f132,f127,f122,f117,f112,f80,f287])).

fof(f284,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_1
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f134,f129,f124,f82,f119,f114,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f283,plain,
    ( spl5_27
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f270,f94,f272])).

fof(f270,plain,
    ( sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3))
    | ~ spl5_4 ),
    inference(resolution,[],[f96,f73])).

fof(f96,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f282,plain,
    ( spl5_28
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f269,f94,f277])).

fof(f269,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK3) = k6_subset_1(u1_struct_0(sK1),sK3)
    | ~ spl5_4 ),
    inference(resolution,[],[f96,f78])).

fof(f264,plain,
    ( spl5_25
    | spl5_1
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f263,f132,f127,f122,f117,f112,f80,f248])).

fof(f263,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | spl5_1
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f134,f129,f124,f119,f114,f82,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | v4_pre_topc(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f244,plain,
    ( ~ spl5_18
    | spl5_24
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f240,f122,f242,f177])).

fof(f177,plain,
    ( spl5_18
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f240,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
        | ~ v1_relat_1(sK2) )
    | ~ spl5_10 ),
    inference(resolution,[],[f75,f124])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f227,plain,
    ( ~ spl5_22
    | spl5_2
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f220,f112,f84,f224])).

fof(f84,plain,
    ( spl5_2
  <=> v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f220,plain,
    ( ~ v3_pre_topc(k10_relat_1(sK2,sK3),sK0)
    | spl5_2
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f86,f212])).

fof(f86,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f181,plain,
    ( spl5_18
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f174,f112,f177])).

fof(f174,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_8 ),
    inference(resolution,[],[f74,f114])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f165,plain,
    ( spl5_15
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f153,f145,f155])).

fof(f153,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl5_14 ),
    inference(resolution,[],[f58,f147])).

fof(f148,plain,
    ( spl5_14
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f137,f127,f145])).

fof(f137,plain,
    ( l1_struct_0(sK1)
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f129,f61])).

fof(f143,plain,
    ( spl5_13
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f138,f132,f140])).

fof(f138,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f134,f61])).

fof(f135,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f48,f132])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK0)
        & v3_pre_topc(sK3,sK1)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) )
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( ! [X4] :
          ( v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK0)
          | ~ v3_pre_topc(X4,sK1)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
      | v5_pre_topc(sK2,sK0,sK1) )
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f40,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | v5_pre_topc(X2,X0,X1) )
                & ( k2_struct_0(X0) = k1_xboole_0
                  | k2_struct_0(X1) != k1_xboole_0 )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),sK0)
                    & v3_pre_topc(X3,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,sK0,X1) )
              & ( ! [X4] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X4),sK0)
                    | ~ v3_pre_topc(X4,X1)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,sK0,X1) )
              & ( k1_xboole_0 = k2_struct_0(sK0)
                | k2_struct_0(X1) != k1_xboole_0 )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),sK0)
                  & v3_pre_topc(X3,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ v5_pre_topc(X2,sK0,X1) )
            & ( ! [X4] :
                  ( v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X4),sK0)
                  | ~ v3_pre_topc(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              | v5_pre_topc(X2,sK0,X1) )
            & ( k1_xboole_0 = k2_struct_0(sK0)
              | k2_struct_0(X1) != k1_xboole_0 )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK0)
                & v3_pre_topc(X3,sK1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
            | ~ v5_pre_topc(X2,sK0,sK1) )
          & ( ! [X4] :
                ( v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X4),sK0)
                | ~ v3_pre_topc(X4,sK1)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
            | v5_pre_topc(X2,sK0,sK1) )
          & ( k1_xboole_0 = k2_struct_0(sK0)
            | k1_xboole_0 != k2_struct_0(sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK0)
              & v3_pre_topc(X3,sK1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          | ~ v5_pre_topc(X2,sK0,sK1) )
        & ( ! [X4] :
              ( v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X4),sK0)
              | ~ v3_pre_topc(X4,sK1)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
          | v5_pre_topc(X2,sK0,sK1) )
        & ( k1_xboole_0 = k2_struct_0(sK0)
          | k1_xboole_0 != k2_struct_0(sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( ? [X3] :
            ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK0)
            & v3_pre_topc(X3,sK1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        | ~ v5_pre_topc(sK2,sK0,sK1) )
      & ( ! [X4] :
            ( v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK0)
            | ~ v3_pre_topc(X4,sK1)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
        | v5_pre_topc(sK2,sK0,sK1) )
      & ( k1_xboole_0 = k2_struct_0(sK0)
        | k1_xboole_0 != k2_struct_0(sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X3] :
        ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK0)
        & v3_pre_topc(X3,sK1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK0)
      & v3_pre_topc(sK3,sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    & v3_pre_topc(X3,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X4] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                    | ~ v3_pre_topc(X4,X1)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,X0,X1) )
              & ( k2_struct_0(X0) = k1_xboole_0
                | k2_struct_0(X1) != k1_xboole_0 )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    & v3_pre_topc(X3,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,X0,X1) )
              & ( k2_struct_0(X0) = k1_xboole_0
                | k2_struct_0(X1) != k1_xboole_0 )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    & v3_pre_topc(X3,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,X0,X1) )
              & ( k2_struct_0(X0) = k1_xboole_0
                | k2_struct_0(X1) != k1_xboole_0 )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <~> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( k2_struct_0(X0) = k1_xboole_0
                | k2_struct_0(X1) != k1_xboole_0 )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <~> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( k2_struct_0(X0) = k1_xboole_0
                | k2_struct_0(X1) != k1_xboole_0 )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k2_struct_0(X1) = k1_xboole_0
                   => k2_struct_0(X0) = k1_xboole_0 )
                 => ( v5_pre_topc(X2,X0,X1)
                  <=> ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( v3_pre_topc(X3,X1)
                         => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k2_struct_0(X1) = k1_xboole_0
                 => k2_struct_0(X0) = k1_xboole_0 )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).

fof(f130,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f49,f127])).

fof(f49,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f125,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f50,f122])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f120,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f51,f117])).

fof(f51,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f115,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f52,f112])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f110,plain,
    ( ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f53,f107,f103])).

fof(f53,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,
    ( spl5_1
    | spl5_5 ),
    inference(avatar_split_clause,[],[f54,f99,f80])).

fof(f54,plain,(
    ! [X4] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK0)
      | ~ v3_pre_topc(X4,sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f97,plain,
    ( ~ spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f55,f94,f80])).

fof(f55,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f56,f89,f80])).

fof(f56,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f87,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f57,f84,f80])).

fof(f57,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

%------------------------------------------------------------------------------
