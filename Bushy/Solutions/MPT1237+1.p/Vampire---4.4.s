%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t48_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:29 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  343 ( 865 expanded)
%              Number of leaves         :   97 ( 384 expanded)
%              Depth                    :    9
%              Number of atoms          :  845 (2137 expanded)
%              Number of equality atoms :   49 (  94 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1148,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f115,f122,f129,f136,f143,f155,f165,f177,f184,f194,f208,f218,f231,f252,f262,f270,f280,f297,f305,f322,f346,f359,f366,f373,f380,f403,f419,f446,f463,f486,f498,f505,f522,f538,f597,f604,f618,f632,f642,f649,f656,f663,f670,f721,f728,f735,f742,f749,f766,f773,f791,f821,f840,f861,f868,f877,f902,f933,f940,f949,f959,f966,f973,f980,f987,f1004,f1011,f1032,f1039,f1060,f1095,f1117,f1134])).

fof(f1134,plain,
    ( ~ spl5_0
    | spl5_15
    | ~ spl5_44
    | ~ spl5_46
    | ~ spl5_62
    | ~ spl5_64
    | ~ spl5_86
    | ~ spl5_126
    | ~ spl5_130
    | ~ spl5_138
    | ~ spl5_142 ),
    inference(avatar_contradiction_clause,[],[f1133])).

fof(f1133,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_15
    | ~ spl5_44
    | ~ spl5_46
    | ~ spl5_62
    | ~ spl5_64
    | ~ spl5_86
    | ~ spl5_126
    | ~ spl5_130
    | ~ spl5_138
    | ~ spl5_142 ),
    inference(subsumption_resolution,[],[f1130,f506])).

fof(f506,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl5_15
    | ~ spl5_44
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f358,f164,f365,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',t31_subset_1)).

fof(f365,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f364])).

fof(f364,plain,
    ( spl5_46
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f164,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl5_15
  <=> ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f358,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl5_44
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f1130,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl5_0
    | ~ spl5_62
    | ~ spl5_64
    | ~ spl5_86
    | ~ spl5_126
    | ~ spl5_130
    | ~ spl5_138
    | ~ spl5_142 ),
    inference(backward_demodulation,[],[f1127,f1074])).

fof(f1074,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl5_0
    | ~ spl5_62
    | ~ spl5_64
    | ~ spl5_86
    | ~ spl5_126
    | ~ spl5_138 ),
    inference(backward_demodulation,[],[f1070,f702])).

fof(f702,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl5_0
    | ~ spl5_62
    | ~ spl5_64
    | ~ spl5_86 ),
    inference(unit_resulting_resolution,[],[f107,f504,f497,f669,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',t49_pre_topc)).

fof(f669,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl5_86 ),
    inference(avatar_component_clause,[],[f668])).

fof(f668,plain,
    ( spl5_86
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f497,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f496])).

fof(f496,plain,
    ( spl5_62
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f504,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f503])).

fof(f503,plain,
    ( spl5_64
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f107,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f1070,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl5_126
    | ~ spl5_138 ),
    inference(forward_demodulation,[],[f1068,f1038])).

fof(f1038,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl5_138 ),
    inference(avatar_component_clause,[],[f1037])).

fof(f1037,plain,
    ( spl5_138
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).

fof(f1068,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl5_126 ),
    inference(unit_resulting_resolution,[],[f972,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',involutiveness_k3_subset_1)).

fof(f972,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_126 ),
    inference(avatar_component_clause,[],[f971])).

fof(f971,plain,
    ( spl5_126
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).

fof(f1127,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl5_130
    | ~ spl5_142 ),
    inference(forward_demodulation,[],[f1125,f1094])).

fof(f1094,plain,
    ( k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
    | ~ spl5_142 ),
    inference(avatar_component_clause,[],[f1093])).

fof(f1093,plain,
    ( spl5_142
  <=> k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f1125,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl5_130 ),
    inference(unit_resulting_resolution,[],[f986,f88])).

fof(f986,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_130 ),
    inference(avatar_component_clause,[],[f985])).

fof(f985,plain,
    ( spl5_130
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).

fof(f1117,plain,
    ( spl5_144
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f1103,f978,f1115])).

fof(f1115,plain,
    ( spl5_144
  <=> r1_tarski(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).

fof(f978,plain,
    ( spl5_128
  <=> m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f1103,plain,
    ( r1_tarski(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl5_128 ),
    inference(unit_resulting_resolution,[],[f979,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',t3_subset)).

fof(f979,plain,
    ( m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_128 ),
    inference(avatar_component_clause,[],[f978])).

fof(f1095,plain,
    ( spl5_142
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f546,f141,f106,f1093])).

fof(f141,plain,
    ( spl5_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f546,plain,
    ( k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f107,f142,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',d1_tops_1)).

fof(f142,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f1060,plain,
    ( spl5_140
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f1048,f964,f1058])).

fof(f1058,plain,
    ( spl5_140
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).

fof(f964,plain,
    ( spl5_124
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f1048,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl5_124 ),
    inference(unit_resulting_resolution,[],[f965,f95])).

fof(f965,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_124 ),
    inference(avatar_component_clause,[],[f964])).

fof(f1039,plain,
    ( spl5_138
    | ~ spl5_0
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f545,f134,f106,f1037])).

fof(f134,plain,
    ( spl5_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f545,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl5_0
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f107,f135,f81])).

fof(f135,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f1032,plain,
    ( spl5_136
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f1020,f957,f1030])).

fof(f1030,plain,
    ( spl5_136
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).

fof(f957,plain,
    ( spl5_122
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f1020,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl5_122 ),
    inference(unit_resulting_resolution,[],[f958,f95])).

fof(f958,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_122 ),
    inference(avatar_component_clause,[],[f957])).

fof(f1011,plain,
    ( spl5_134
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f704,f668,f1009])).

fof(f1009,plain,
    ( spl5_134
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).

fof(f704,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl5_86 ),
    inference(unit_resulting_resolution,[],[f669,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f1004,plain,
    ( spl5_132
    | ~ spl5_0
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f527,f503,f106,f1002])).

fof(f1002,plain,
    ( spl5_132
  <=> m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f527,plain,
    ( m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f107,f504,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',dt_k1_tops_1)).

fof(f987,plain,
    ( spl5_130
    | ~ spl5_0
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f526,f503,f106,f985])).

fof(f526,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f107,f504,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',dt_k2_pre_topc)).

fof(f980,plain,
    ( spl5_128
    | ~ spl5_0
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f511,f496,f106,f978])).

fof(f511,plain,
    ( m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f107,f497,f91])).

fof(f973,plain,
    ( spl5_126
    | ~ spl5_0
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f510,f496,f106,f971])).

fof(f510,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f107,f497,f92])).

fof(f966,plain,
    ( spl5_124
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f409,f364,f964])).

fof(f409,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f365,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',dt_k3_subset_1)).

fof(f959,plain,
    ( spl5_122
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f384,f357,f957])).

fof(f384,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f358,f87])).

fof(f949,plain,
    ( ~ spl5_121
    | spl5_23 ),
    inference(avatar_split_clause,[],[f255,f206,f947])).

fof(f947,plain,
    ( spl5_121
  <=> ~ r2_hidden(k1_tops_1(sK0,sK1),sK3(k1_zfmisc_1(k1_zfmisc_1(k1_tops_1(sK0,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).

fof(f206,plain,
    ( spl5_23
  <=> ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f255,plain,
    ( ~ r2_hidden(k1_tops_1(sK0,sK1),sK3(k1_zfmisc_1(k1_zfmisc_1(k1_tops_1(sK0,sK2)))))
    | ~ spl5_23 ),
    inference(unit_resulting_resolution,[],[f207,f83,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',t4_subset)).

fof(f83,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',existence_m1_subset_1)).

fof(f207,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f206])).

fof(f940,plain,
    ( spl5_118
    | ~ spl5_114 ),
    inference(avatar_split_clause,[],[f921,f900,f938])).

fof(f938,plain,
    ( spl5_118
  <=> r1_tarski(k2_pre_topc(sK4,sK3(k1_zfmisc_1(u1_struct_0(sK4)))),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f900,plain,
    ( spl5_114
  <=> m1_subset_1(k2_pre_topc(sK4,sK3(k1_zfmisc_1(u1_struct_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f921,plain,
    ( r1_tarski(k2_pre_topc(sK4,sK3(k1_zfmisc_1(u1_struct_0(sK4)))),u1_struct_0(sK4))
    | ~ spl5_114 ),
    inference(unit_resulting_resolution,[],[f901,f95])).

fof(f901,plain,
    ( m1_subset_1(k2_pre_topc(sK4,sK3(k1_zfmisc_1(u1_struct_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_114 ),
    inference(avatar_component_clause,[],[f900])).

fof(f933,plain,
    ( spl5_116
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f910,f875,f931])).

fof(f931,plain,
    ( spl5_116
  <=> r1_tarski(k1_tops_1(sK4,sK3(k1_zfmisc_1(u1_struct_0(sK4)))),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).

fof(f875,plain,
    ( spl5_112
  <=> m1_subset_1(k1_tops_1(sK4,sK3(k1_zfmisc_1(u1_struct_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f910,plain,
    ( r1_tarski(k1_tops_1(sK4,sK3(k1_zfmisc_1(u1_struct_0(sK4)))),u1_struct_0(sK4))
    | ~ spl5_112 ),
    inference(unit_resulting_resolution,[],[f876,f95])).

fof(f876,plain,
    ( m1_subset_1(k1_tops_1(sK4,sK3(k1_zfmisc_1(u1_struct_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_112 ),
    inference(avatar_component_clause,[],[f875])).

fof(f902,plain,
    ( spl5_114
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f352,f120,f900])).

fof(f120,plain,
    ( spl5_4
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f352,plain,
    ( m1_subset_1(k2_pre_topc(sK4,sK3(k1_zfmisc_1(u1_struct_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f121,f83,f92])).

fof(f121,plain,
    ( l1_pre_topc(sK4)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f877,plain,
    ( spl5_112
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f314,f120,f875])).

fof(f314,plain,
    ( m1_subset_1(k1_tops_1(sK4,sK3(k1_zfmisc_1(u1_struct_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f121,f83,f91])).

fof(f868,plain,
    ( spl5_110
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f848,f764,f866])).

fof(f866,plain,
    ( spl5_110
  <=> r1_tarski(k2_pre_topc(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f764,plain,
    ( spl5_98
  <=> m1_subset_1(k2_pre_topc(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f848,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f765,f95])).

fof(f765,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_98 ),
    inference(avatar_component_clause,[],[f764])).

fof(f861,plain,
    ( spl5_108
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f800,f719,f859])).

fof(f859,plain,
    ( spl5_108
  <=> r1_tarski(k1_tops_1(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f719,plain,
    ( spl5_88
  <=> m1_subset_1(k1_tops_1(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f800,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl5_88 ),
    inference(unit_resulting_resolution,[],[f720,f95])).

fof(f720,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f719])).

fof(f840,plain,
    ( spl5_106
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f830,f747,f838])).

fof(f838,plain,
    ( spl5_106
  <=> r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f747,plain,
    ( spl5_96
  <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f830,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl5_96 ),
    inference(unit_resulting_resolution,[],[f748,f95])).

fof(f748,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_96 ),
    inference(avatar_component_clause,[],[f747])).

fof(f821,plain,
    ( spl5_104
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f811,f740,f819])).

fof(f819,plain,
    ( spl5_104
  <=> r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f740,plain,
    ( spl5_94
  <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f811,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl5_94 ),
    inference(unit_resulting_resolution,[],[f741,f95])).

fof(f741,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_94 ),
    inference(avatar_component_clause,[],[f740])).

fof(f791,plain,
    ( spl5_102
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f782,f733,f789])).

fof(f789,plain,
    ( spl5_102
  <=> r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f733,plain,
    ( spl5_92
  <=> m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f782,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl5_92 ),
    inference(unit_resulting_resolution,[],[f734,f95])).

fof(f734,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_92 ),
    inference(avatar_component_clause,[],[f733])).

fof(f773,plain,
    ( spl5_100
    | ~ spl5_90 ),
    inference(avatar_split_clause,[],[f757,f726,f771])).

fof(f771,plain,
    ( spl5_100
  <=> r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f726,plain,
    ( spl5_90
  <=> m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f757,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl5_90 ),
    inference(unit_resulting_resolution,[],[f727,f95])).

fof(f727,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_90 ),
    inference(avatar_component_clause,[],[f726])).

fof(f766,plain,
    ( spl5_98
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f351,f106,f764])).

fof(f351,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0 ),
    inference(unit_resulting_resolution,[],[f107,f83,f92])).

fof(f749,plain,
    ( spl5_96
    | ~ spl5_0
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f451,f378,f106,f747])).

fof(f378,plain,
    ( spl5_50
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f451,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_50 ),
    inference(unit_resulting_resolution,[],[f107,f379,f91])).

fof(f379,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f378])).

fof(f742,plain,
    ( spl5_94
    | ~ spl5_0
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f434,f371,f106,f740])).

fof(f371,plain,
    ( spl5_48
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f434,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f107,f372,f91])).

fof(f372,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f371])).

fof(f735,plain,
    ( spl5_92
    | ~ spl5_0
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f406,f364,f106,f733])).

fof(f406,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f107,f365,f92])).

fof(f728,plain,
    ( spl5_90
    | ~ spl5_0
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f381,f357,f106,f726])).

fof(f381,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f107,f358,f92])).

fof(f721,plain,
    ( spl5_88
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f313,f106,f719])).

fof(f313,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0 ),
    inference(unit_resulting_resolution,[],[f107,f83,f91])).

fof(f670,plain,
    ( spl5_86
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f466,f141,f134,f127,f668])).

fof(f127,plain,
    ( spl5_6
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f466,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f128,f135,f142,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f128,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f663,plain,
    ( spl5_84
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f424,f141,f106,f661])).

fof(f661,plain,
    ( spl5_84
  <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f424,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f107,f142,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',projectivity_k2_pre_topc)).

fof(f656,plain,
    ( spl5_82
    | ~ spl5_0
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f423,f134,f106,f654])).

fof(f654,plain,
    ( spl5_82
  <=> k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f423,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl5_0
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f107,f135,f94])).

fof(f649,plain,
    ( spl5_80
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f388,f141,f106,f647])).

fof(f647,plain,
    ( spl5_80
  <=> k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f388,plain,
    ( k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2))
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f107,f142,f93])).

fof(f93,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',projectivity_k1_tops_1)).

fof(f642,plain,
    ( spl5_78
    | ~ spl5_0
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f387,f134,f106,f640])).

fof(f640,plain,
    ( spl5_78
  <=> k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f387,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl5_0
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f107,f135,f93])).

fof(f632,plain,
    ( spl5_76
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f621,f616,f630])).

fof(f630,plain,
    ( spl5_76
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f616,plain,
    ( spl5_74
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f621,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK2)))
    | ~ spl5_74 ),
    inference(unit_resulting_resolution,[],[f617,f96])).

fof(f617,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f616])).

fof(f618,plain,
    ( spl5_74
    | ~ spl5_0
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f605,f141,f134,f127,f106,f616])).

fof(f605,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    | ~ spl5_0
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f107,f128,f135,f142,f82])).

fof(f604,plain,
    ( spl5_72
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f284,f141,f602])).

fof(f602,plain,
    ( spl5_72
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f284,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f142,f88])).

fof(f597,plain,
    ( spl5_70
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f282,f134,f595])).

fof(f595,plain,
    ( spl5_70
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f282,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f135,f88])).

fof(f538,plain,
    ( spl5_68
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f530,f503,f536])).

fof(f536,plain,
    ( spl5_68
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f530,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f504,f95])).

fof(f522,plain,
    ( spl5_66
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f514,f496,f520])).

fof(f520,plain,
    ( spl5_66
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f514,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f497,f95])).

fof(f505,plain,
    ( spl5_64
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f223,f141,f503])).

fof(f223,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f142,f87])).

fof(f498,plain,
    ( spl5_62
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f221,f134,f496])).

fof(f221,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f135,f87])).

fof(f486,plain,
    ( spl5_60
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f283,f192,f484])).

fof(f484,plain,
    ( spl5_60
  <=> k3_subset_1(sK2,k3_subset_1(sK2,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f192,plain,
    ( spl5_20
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f283,plain,
    ( k3_subset_1(sK2,k3_subset_1(sK2,sK1)) = sK1
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f193,f88])).

fof(f193,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f192])).

fof(f463,plain,
    ( spl5_58
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f454,f378,f461])).

fof(f461,plain,
    ( spl5_58
  <=> r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f454,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0))
    | ~ spl5_50 ),
    inference(unit_resulting_resolution,[],[f379,f95])).

fof(f446,plain,
    ( spl5_56
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f437,f371,f444])).

fof(f444,plain,
    ( spl5_56
  <=> r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f437,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f372,f95])).

fof(f419,plain,
    ( spl5_54
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f410,f364,f417])).

fof(f417,plain,
    ( spl5_54
  <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f410,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f365,f95])).

fof(f403,plain,
    ( spl5_52
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f385,f357,f401])).

fof(f401,plain,
    ( spl5_52
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f385,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f358,f95])).

fof(f380,plain,
    ( spl5_50
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f350,f141,f106,f378])).

fof(f350,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f107,f142,f92])).

fof(f373,plain,
    ( spl5_48
    | ~ spl5_0
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f349,f134,f106,f371])).

fof(f349,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f107,f135,f92])).

fof(f366,plain,
    ( spl5_46
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f312,f141,f106,f364])).

fof(f312,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f107,f142,f91])).

fof(f359,plain,
    ( spl5_44
    | ~ spl5_0
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f311,f134,f106,f357])).

fof(f311,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f107,f135,f91])).

fof(f346,plain,
    ( spl5_42
    | ~ spl5_2
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f328,f320,f113,f344])).

fof(f344,plain,
    ( spl5_42
  <=> k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f113,plain,
    ( spl5_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f320,plain,
    ( spl5_40
  <=> v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f328,plain,
    ( k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_2
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f321,f146])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f144,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',t6_boole)).

fof(f144,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f114,f80])).

fof(f114,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f321,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f320])).

fof(f322,plain,
    ( spl5_40
    | ~ spl5_2
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f315,f303,f113,f320])).

fof(f303,plain,
    ( spl5_38
  <=> m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f315,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_2
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f83,f308,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',t2_subset)).

fof(f308,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_2
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f114,f304,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',t5_subset)).

fof(f304,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f303])).

fof(f305,plain,
    ( spl5_38
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f271,f268,f303])).

fof(f268,plain,
    ( spl5_32
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f271,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_32 ),
    inference(unit_resulting_resolution,[],[f269,f87])).

fof(f269,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f268])).

fof(f297,plain,
    ( spl5_36
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f289,f278,f295])).

fof(f295,plain,
    ( spl5_36
  <=> r1_tarski(k3_subset_1(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f278,plain,
    ( spl5_34
  <=> m1_subset_1(k3_subset_1(sK2,sK1),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f289,plain,
    ( r1_tarski(k3_subset_1(sK2,sK1),sK2)
    | ~ spl5_34 ),
    inference(unit_resulting_resolution,[],[f279,f95])).

fof(f279,plain,
    ( m1_subset_1(k3_subset_1(sK2,sK1),k1_zfmisc_1(sK2))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f278])).

fof(f280,plain,
    ( spl5_34
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f222,f192,f278])).

fof(f222,plain,
    ( m1_subset_1(k3_subset_1(sK2,sK1),k1_zfmisc_1(sK2))
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f193,f87])).

fof(f270,plain,
    ( spl5_32
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f254,f250,f268])).

fof(f250,plain,
    ( spl5_28
  <=> o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f254,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_28 ),
    inference(superposition,[],[f83,f251])).

fof(f251,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f250])).

fof(f262,plain,
    ( spl5_30
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f253,f250,f260])).

fof(f260,plain,
    ( spl5_30
  <=> r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f253,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_28 ),
    inference(superposition,[],[f167,f251])).

fof(f167,plain,(
    ! [X0] : r1_tarski(sK3(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f83,f95])).

fof(f252,plain,
    ( spl5_28
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f237,f229,f113,f250])).

fof(f229,plain,
    ( spl5_26
  <=> v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f237,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(unit_resulting_resolution,[],[f230,f146])).

fof(f230,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f229])).

fof(f231,plain,
    ( spl5_26
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f224,f113,f229])).

fof(f224,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f83,f219,f86])).

fof(f219,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f114,f83,f100])).

fof(f218,plain,
    ( ~ spl5_25
    | spl5_23 ),
    inference(avatar_split_clause,[],[f210,f206,f216])).

fof(f216,plain,
    ( spl5_25
  <=> ~ r2_hidden(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f210,plain,
    ( ~ r2_hidden(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl5_23 ),
    inference(unit_resulting_resolution,[],[f207,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',t1_subset)).

fof(f208,plain,
    ( ~ spl5_23
    | spl5_15 ),
    inference(avatar_split_clause,[],[f166,f163,f206])).

fof(f166,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f164,f95])).

fof(f194,plain,
    ( spl5_20
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f185,f127,f192])).

fof(f185,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f128,f96])).

fof(f184,plain,
    ( spl5_18
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f169,f141,f182])).

fof(f182,plain,
    ( spl5_18
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f169,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f142,f95])).

fof(f177,plain,
    ( spl5_16
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f168,f134,f175])).

fof(f175,plain,
    ( spl5_16
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f168,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f135,f95])).

fof(f165,plain,(
    ~ spl5_15 ),
    inference(avatar_split_clause,[],[f76,f163])).

fof(f76,plain,(
    ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f64,f63,f62])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k1_tops_1(X0,sK1),k1_tops_1(X0,X2))
            & r1_tarski(sK1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,sK2))
        & r1_tarski(X1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X1,X2)
                 => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',t48_tops_1)).

fof(f155,plain,
    ( spl5_12
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f144,f113,f153])).

fof(f153,plain,
    ( spl5_12
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f143,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f74,f141])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f65])).

fof(f136,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f73,f134])).

fof(f73,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f65])).

fof(f129,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f75,f127])).

fof(f75,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f122,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f101,f120])).

fof(f101,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f70])).

fof(f70,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK4) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',existence_l1_pre_topc)).

fof(f115,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f77,f113])).

fof(f77,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t48_tops_1.p',dt_o_0_0_xboole_0)).

fof(f108,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f72,f106])).

fof(f72,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).
%------------------------------------------------------------------------------
