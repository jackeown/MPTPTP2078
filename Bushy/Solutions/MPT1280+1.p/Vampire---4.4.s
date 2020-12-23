%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t102_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:25 EDT 2019

% Result     : Theorem 0.36s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  309 (1158 expanded)
%              Number of leaves         :   87 ( 473 expanded)
%              Depth                    :   10
%              Number of atoms          :  784 (2565 expanded)
%              Number of equality atoms :   89 ( 323 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2424,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f133,f140,f147,f154,f167,f190,f199,f220,f230,f239,f253,f277,f285,f316,f374,f503,f537,f555,f562,f599,f630,f680,f687,f694,f804,f853,f862,f918,f1062,f1137,f1144,f1151,f1194,f1255,f1287,f1361,f1368,f1375,f1474,f1481,f1492,f1538,f1545,f1552,f1595,f1602,f1609,f1807,f1854,f1861,f1889,f1896,f1903,f1931,f1938,f1945,f1952,f2347,f2354,f2361,f2371,f2401])).

fof(f2401,plain,
    ( ~ spl4_0
    | ~ spl4_8
    | spl4_13
    | ~ spl4_26
    | ~ spl4_34
    | ~ spl4_52
    | ~ spl4_54
    | ~ spl4_116 ),
    inference(avatar_contradiction_clause,[],[f2400])).

fof(f2400,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_26
    | ~ spl4_34
    | ~ spl4_52
    | ~ spl4_54
    | ~ spl4_116 ),
    inference(subsumption_resolution,[],[f2399,f189])).

fof(f189,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl4_13
  <=> k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f2399,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_26
    | ~ spl4_34
    | ~ spl4_52
    | ~ spl4_54
    | ~ spl4_116 ),
    inference(backward_demodulation,[],[f2391,f2397])).

fof(f2397,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_26
    | ~ spl4_34
    | ~ spl4_54
    | ~ spl4_116 ),
    inference(backward_demodulation,[],[f2389,f1130])).

fof(f1130,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))))
    | ~ spl4_0
    | ~ spl4_34
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f1082,f861])).

fof(f861,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f860])).

fof(f860,plain,
    ( spl4_54
  <=> k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f1082,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))))
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f125,f536,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',d2_tops_1)).

fof(f536,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f535])).

fof(f535,plain,
    ( spl4_34
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f125,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f2389,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_26
    | ~ spl4_116 ),
    inference(backward_demodulation,[],[f2388,f651])).

fof(f651,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_0
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f125,f284,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',projectivity_k2_pre_topc)).

fof(f284,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl4_26
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f2388,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_116 ),
    inference(forward_demodulation,[],[f2380,f971])).

fof(f971,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f125,f153,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',d1_tops_1)).

fof(f153,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl4_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f2380,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_116 ),
    inference(unit_resulting_resolution,[],[f2346,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',involutiveness_k3_subset_1)).

fof(f2346,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_116 ),
    inference(avatar_component_clause,[],[f2345])).

fof(f2345,plain,
    ( spl4_116
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).

fof(f2391,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_52
    | ~ spl4_116 ),
    inference(backward_demodulation,[],[f2388,f1118])).

fof(f1118,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f1113,f852])).

fof(f852,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f851])).

fof(f851,plain,
    ( spl4_52
  <=> k2_pre_topc(sK0,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f1113,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f125,f153,f95])).

fof(f2371,plain,
    ( spl4_122
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f603,f597,f2369])).

fof(f2369,plain,
    ( spl4_122
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_122])])).

fof(f597,plain,
    ( spl4_40
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f603,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_40 ),
    inference(unit_resulting_resolution,[],[f598,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',dt_k3_subset_1)).

fof(f598,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f597])).

fof(f2361,plain,
    ( spl4_120
    | ~ spl4_0
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f579,f283,f124,f2359])).

fof(f2359,plain,
    ( spl4_120
  <=> m1_subset_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).

fof(f579,plain,
    ( m1_subset_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f125,f284,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',dt_k2_tops_1)).

fof(f2354,plain,
    ( spl4_118
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f540,f535,f2352])).

fof(f2352,plain,
    ( spl4_118
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).

fof(f540,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f536,f104])).

fof(f2347,plain,
    ( spl4_116
    | ~ spl4_0
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f466,f283,f124,f2345])).

fof(f466,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f125,f284,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',dt_k2_pre_topc)).

fof(f1952,plain,
    ( spl4_114
    | ~ spl4_4
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f760,f692,f138,f1950])).

fof(f1950,plain,
    ( spl4_114
  <=> m1_subset_1(k2_pre_topc(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_114])])).

fof(f138,plain,
    ( spl4_4
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f692,plain,
    ( spl4_48
  <=> m1_subset_1(k2_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f760,plain,
    ( m1_subset_1(k2_pre_topc(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_48 ),
    inference(unit_resulting_resolution,[],[f139,f693,f106])).

fof(f693,plain,
    ( m1_subset_1(k2_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f692])).

fof(f139,plain,
    ( l1_pre_topc(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f138])).

fof(f1945,plain,
    ( spl4_112
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f591,f138,f1943])).

fof(f1943,plain,
    ( spl4_112
  <=> m1_subset_1(k2_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).

fof(f591,plain,
    ( m1_subset_1(k2_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f139,f98,f108])).

fof(f98,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',existence_m1_subset_1)).

fof(f1938,plain,
    ( spl4_110
    | ~ spl4_4
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f759,f692,f138,f1936])).

fof(f1936,plain,
    ( spl4_110
  <=> m1_subset_1(k1_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_110])])).

fof(f759,plain,
    ( m1_subset_1(k1_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_48 ),
    inference(unit_resulting_resolution,[],[f139,f693,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',dt_k1_tops_1)).

fof(f1931,plain,
    ( spl4_108
    | ~ spl4_4
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f758,f692,f138,f1929])).

fof(f1929,plain,
    ( spl4_108
  <=> m1_subset_1(k2_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).

fof(f758,plain,
    ( m1_subset_1(k2_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_48 ),
    inference(unit_resulting_resolution,[],[f139,f693,f108])).

fof(f1903,plain,
    ( spl4_106
    | ~ spl4_4
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f744,f685,f138,f1901])).

fof(f1901,plain,
    ( spl4_106
  <=> m1_subset_1(k2_pre_topc(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f685,plain,
    ( spl4_46
  <=> m1_subset_1(k1_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f744,plain,
    ( m1_subset_1(k2_pre_topc(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f139,f686,f106])).

fof(f686,plain,
    ( m1_subset_1(k1_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f685])).

fof(f1896,plain,
    ( spl4_104
    | ~ spl4_4
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f742,f685,f138,f1894])).

fof(f1894,plain,
    ( spl4_104
  <=> m1_subset_1(k2_tops_1(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).

fof(f742,plain,
    ( m1_subset_1(k2_tops_1(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f139,f686,f108])).

fof(f1889,plain,
    ( spl4_102
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f529,f138,f1887])).

fof(f1887,plain,
    ( spl4_102
  <=> m1_subset_1(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f529,plain,
    ( m1_subset_1(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f139,f98,f107])).

fof(f1861,plain,
    ( spl4_100
    | ~ spl4_4
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f697,f678,f138,f1859])).

fof(f1859,plain,
    ( spl4_100
  <=> m1_subset_1(k1_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).

fof(f678,plain,
    ( spl4_44
  <=> m1_subset_1(k2_pre_topc(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f697,plain,
    ( m1_subset_1(k1_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f139,f679,f107])).

fof(f679,plain,
    ( m1_subset_1(k2_pre_topc(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f678])).

fof(f1854,plain,
    ( spl4_98
    | ~ spl4_4
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f696,f678,f138,f1852])).

fof(f1852,plain,
    ( spl4_98
  <=> m1_subset_1(k2_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f696,plain,
    ( m1_subset_1(k2_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f139,f679,f108])).

fof(f1807,plain,
    ( spl4_96
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f474,f138,f1805])).

fof(f1805,plain,
    ( spl4_96
  <=> m1_subset_1(k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f474,plain,
    ( m1_subset_1(k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f139,f98,f106])).

fof(f1609,plain,
    ( spl4_94
    | ~ spl4_0
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f633,f628,f124,f1607])).

fof(f1607,plain,
    ( spl4_94
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f628,plain,
    ( spl4_42
  <=> m1_subset_1(k2_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f633,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_42 ),
    inference(unit_resulting_resolution,[],[f125,f629,f106])).

fof(f629,plain,
    ( m1_subset_1(k2_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f628])).

fof(f1602,plain,
    ( spl4_92
    | ~ spl4_0
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f632,f628,f124,f1600])).

fof(f1600,plain,
    ( spl4_92
  <=> m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f632,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_42 ),
    inference(unit_resulting_resolution,[],[f125,f629,f107])).

fof(f1595,plain,
    ( spl4_90
    | ~ spl4_0
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f631,f628,f124,f1593])).

fof(f1593,plain,
    ( spl4_90
  <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f631,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_42 ),
    inference(unit_resulting_resolution,[],[f125,f629,f108])).

fof(f1552,plain,
    ( spl4_88
    | ~ spl4_0
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f614,f560,f124,f1550])).

fof(f1550,plain,
    ( spl4_88
  <=> m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f560,plain,
    ( spl4_38
  <=> m1_subset_1(k1_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f614,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_38 ),
    inference(unit_resulting_resolution,[],[f125,f561,f106])).

fof(f561,plain,
    ( m1_subset_1(k1_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f560])).

fof(f1545,plain,
    ( spl4_86
    | ~ spl4_0
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f612,f560,f124,f1543])).

fof(f1543,plain,
    ( spl4_86
  <=> m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f612,plain,
    ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_38 ),
    inference(unit_resulting_resolution,[],[f125,f561,f108])).

fof(f1538,plain,
    ( spl4_84
    | ~ spl4_0
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f585,f553,f124,f1536])).

fof(f1536,plain,
    ( spl4_84
  <=> m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f553,plain,
    ( spl4_36
  <=> m1_subset_1(k2_pre_topc(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f585,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f125,f554,f108])).

fof(f554,plain,
    ( m1_subset_1(k2_pre_topc(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f553])).

fof(f1492,plain,
    ( spl4_82
    | ~ spl4_0
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f563,f553,f124,f1490])).

fof(f1490,plain,
    ( spl4_82
  <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f563,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f125,f554,f107])).

fof(f1481,plain,
    ( spl4_80
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f728,f138,f131,f1479])).

fof(f1479,plain,
    ( spl4_80
  <=> k1_tops_1(sK3,o_0_0_xboole_0) = k1_tops_1(sK3,k1_tops_1(sK3,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f131,plain,
    ( spl4_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f728,plain,
    ( k1_tops_1(sK3,o_0_0_xboole_0) = k1_tops_1(sK3,k1_tops_1(sK3,o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f139,f444,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',projectivity_k1_tops_1)).

fof(f444,plain,
    ( ! [X5] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X5))
    | ~ spl4_2 ),
    inference(superposition,[],[f341,f171])).

fof(f171,plain,
    ( ! [X1] : k3_xboole_0(o_0_0_xboole_0,X1) = o_0_0_xboole_0
    | ~ spl4_2 ),
    inference(superposition,[],[f100,f158])).

fof(f158,plain,
    ( ! [X0] : k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f155,f92])).

fof(f92,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',t2_boole)).

fof(f155,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f132,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',t6_boole)).

fof(f132,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f131])).

fof(f100,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',commutativity_k3_xboole_0)).

fof(f341,plain,(
    ! [X0,X1] : m1_subset_1(k3_xboole_0(X1,sK2(k1_zfmisc_1(X0))),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f335,f323])).

fof(f323,plain,(
    ! [X0,X1] : m1_subset_1(k9_subset_1(X0,X1,sK2(k1_zfmisc_1(X0))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f98,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',dt_k9_subset_1)).

fof(f335,plain,(
    ! [X0,X1] : k3_xboole_0(X0,sK2(k1_zfmisc_1(X1))) = k9_subset_1(X1,X0,sK2(k1_zfmisc_1(X1))) ),
    inference(unit_resulting_resolution,[],[f98,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',redefinition_k9_subset_1)).

fof(f1474,plain,
    ( spl4_78
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f660,f138,f131,f1472])).

fof(f1472,plain,
    ( spl4_78
  <=> k2_pre_topc(sK3,o_0_0_xboole_0) = k2_pre_topc(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f660,plain,
    ( k2_pre_topc(sK3,o_0_0_xboole_0) = k2_pre_topc(sK3,k2_pre_topc(sK3,o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f139,f444,f109])).

fof(f1375,plain,
    ( spl4_76
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f590,f124,f1373])).

fof(f1373,plain,
    ( spl4_76
  <=> m1_subset_1(k2_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f590,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f125,f98,f108])).

fof(f1368,plain,
    ( spl4_74
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f727,f131,f124,f1366])).

fof(f1366,plain,
    ( spl4_74
  <=> k1_tops_1(sK0,o_0_0_xboole_0) = k1_tops_1(sK0,k1_tops_1(sK0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f727,plain,
    ( k1_tops_1(sK0,o_0_0_xboole_0) = k1_tops_1(sK0,k1_tops_1(sK0,o_0_0_xboole_0))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f125,f444,f110])).

fof(f1361,plain,
    ( spl4_72
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f659,f131,f124,f1359])).

fof(f1359,plain,
    ( spl4_72
  <=> k2_pre_topc(sK0,o_0_0_xboole_0) = k2_pre_topc(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f659,plain,
    ( k2_pre_topc(sK0,o_0_0_xboole_0) = k2_pre_topc(sK0,k2_pre_topc(sK0,o_0_0_xboole_0))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f125,f444,f109])).

fof(f1287,plain,
    ( spl4_70
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f528,f124,f1285])).

fof(f1285,plain,
    ( spl4_70
  <=> m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f528,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f125,f98,f107])).

fof(f1255,plain,
    ( spl4_68
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f377,f372,f1253])).

fof(f1253,plain,
    ( spl4_68
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f372,plain,
    ( spl4_30
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f377,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl4_30 ),
    inference(unit_resulting_resolution,[],[f373,f105])).

fof(f373,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f372])).

fof(f1194,plain,
    ( spl4_66
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f473,f124,f1192])).

fof(f1192,plain,
    ( spl4_66
  <=> m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f473,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f125,f98,f106])).

fof(f1151,plain,
    ( spl4_64
    | ~ spl4_0
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f602,f597,f124,f1149])).

fof(f1149,plain,
    ( spl4_64
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f602,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_40 ),
    inference(unit_resulting_resolution,[],[f125,f598,f106])).

fof(f1144,plain,
    ( spl4_62
    | ~ spl4_0
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f601,f597,f124,f1142])).

fof(f1142,plain,
    ( spl4_62
  <=> m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f601,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_40 ),
    inference(unit_resulting_resolution,[],[f125,f598,f107])).

fof(f1137,plain,
    ( spl4_60
    | ~ spl4_0
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f600,f597,f124,f1135])).

fof(f1135,plain,
    ( spl4_60
  <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f600,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_40 ),
    inference(unit_resulting_resolution,[],[f125,f598,f108])).

fof(f1062,plain,
    ( spl4_58
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f574,f535,f124,f1060])).

fof(f1060,plain,
    ( spl4_58
  <=> m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f574,plain,
    ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f125,f536,f108])).

fof(f918,plain,
    ( spl4_56
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f729,f152,f124,f916])).

fof(f916,plain,
    ( spl4_56
  <=> k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f729,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f125,f153,f110])).

fof(f862,plain,
    ( spl4_54
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f833,f152,f145,f124,f860])).

fof(f145,plain,
    ( spl4_6
  <=> v5_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f833,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f125,f146,f153,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v5_tops_1(X1,X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',d7_tops_1)).

fof(f146,plain,
    ( v5_tops_1(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f853,plain,
    ( spl4_52
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f835,f535,f152,f145,f124,f851])).

fof(f835,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_34 ),
    inference(backward_demodulation,[],[f833,f643])).

fof(f643,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f125,f536,f109])).

fof(f804,plain,
    ( spl4_50
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f378,f372,f802])).

fof(f802,plain,
    ( spl4_50
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f378,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_30 ),
    inference(unit_resulting_resolution,[],[f373,f104])).

fof(f694,plain,
    ( spl4_48
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f588,f138,f131,f692])).

fof(f588,plain,
    ( m1_subset_1(k2_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f139,f444,f108])).

fof(f687,plain,
    ( spl4_46
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f526,f138,f131,f685])).

fof(f526,plain,
    ( m1_subset_1(k1_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f139,f444,f107])).

fof(f680,plain,
    ( spl4_44
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f471,f138,f131,f678])).

fof(f471,plain,
    ( m1_subset_1(k2_pre_topc(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f139,f444,f106])).

fof(f630,plain,
    ( spl4_42
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f587,f131,f124,f628])).

fof(f587,plain,
    ( m1_subset_1(k2_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f125,f444,f108])).

fof(f599,plain,
    ( spl4_40
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f589,f152,f124,f597])).

fof(f589,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f125,f153,f108])).

fof(f562,plain,
    ( spl4_38
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f525,f131,f124,f560])).

fof(f525,plain,
    ( m1_subset_1(k1_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f125,f444,f107])).

fof(f555,plain,
    ( spl4_36
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f470,f131,f124,f553])).

fof(f470,plain,
    ( m1_subset_1(k2_pre_topc(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f125,f444,f106])).

fof(f537,plain,
    ( spl4_34
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f527,f152,f124,f535])).

fof(f527,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f125,f153,f107])).

fof(f503,plain,
    ( spl4_32
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f472,f152,f124,f501])).

fof(f501,plain,
    ( spl4_32
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f472,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f125,f153,f106])).

fof(f374,plain,
    ( spl4_30
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f366,f152,f131,f372])).

fof(f366,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(superposition,[],[f342,f171])).

fof(f342,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f334,f322])).

fof(f322,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f153,f114])).

fof(f334,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),X0,sK1)
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f153,f115])).

fof(f316,plain,
    ( spl4_28
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f303,f152,f314])).

fof(f314,plain,
    ( spl4_28
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f303,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f153,f105])).

fof(f285,plain,
    ( spl4_26
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f222,f152,f283])).

fof(f222,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f153,f104])).

fof(f277,plain,
    ( spl4_24
    | ~ spl4_2
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f259,f251,f131,f275])).

fof(f275,plain,
    ( spl4_24
  <=> k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f251,plain,
    ( spl4_22
  <=> v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f259,plain,
    ( k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl4_2
    | ~ spl4_22 ),
    inference(unit_resulting_resolution,[],[f252,f157])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f155,f93])).

fof(f252,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f251])).

fof(f253,plain,
    ( spl4_22
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f246,f237,f131,f251])).

fof(f237,plain,
    ( spl4_20
  <=> m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f246,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f98,f241,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',t2_subset)).

fof(f241,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f132,f238,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',t5_subset)).

fof(f238,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f237])).

fof(f239,plain,
    ( spl4_20
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f231,f228,f237])).

fof(f228,plain,
    ( spl4_18
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f231,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f229,f104])).

fof(f229,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f228])).

fof(f230,plain,
    ( spl4_18
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f223,f218,f228])).

fof(f218,plain,
    ( spl4_16
  <=> o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f223,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_16 ),
    inference(superposition,[],[f98,f219])).

fof(f219,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f218])).

fof(f220,plain,
    ( spl4_16
    | ~ spl4_2
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f205,f197,f131,f218])).

fof(f197,plain,
    ( spl4_14
  <=> v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f205,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f198,f157])).

fof(f198,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f197])).

fof(f199,plain,
    ( spl4_14
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f192,f131,f197])).

fof(f192,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f98,f191,f103])).

fof(f191,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f132,f98,f118])).

fof(f190,plain,(
    ~ spl4_13 ),
    inference(avatar_split_clause,[],[f88,f188])).

fof(f88,plain,(
    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k1_tops_1(sK0,sK1))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f78,f77])).

fof(f77,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_tops_1(X0,X1) != k2_tops_1(X0,k1_tops_1(X0,X1))
            & v5_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( k2_tops_1(sK0,X1) != k2_tops_1(sK0,k1_tops_1(sK0,X1))
          & v5_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,X1) != k2_tops_1(X0,k1_tops_1(X0,X1))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k2_tops_1(X0,sK1) != k2_tops_1(X0,k1_tops_1(X0,sK1))
        & v5_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,X1) != k2_tops_1(X0,k1_tops_1(X0,X1))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,X1) != k2_tops_1(X0,k1_tops_1(X0,X1))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',t102_tops_1)).

fof(f167,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f155,f131,f165])).

fof(f165,plain,
    ( spl4_10
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f154,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f86,f152])).

fof(f86,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f79])).

fof(f147,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f87,f145])).

fof(f87,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f140,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f119,f138])).

fof(f119,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f83])).

fof(f83,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK3) ),
    introduced(choice_axiom,[])).

fof(f23,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',existence_l1_pre_topc)).

fof(f133,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f89,f131])).

fof(f89,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t102_tops_1.p',dt_o_0_0_xboole_0)).

fof(f126,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f85,f124])).

fof(f85,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f79])).
%------------------------------------------------------------------------------
