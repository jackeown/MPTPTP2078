%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t101_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:25 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  278 ( 794 expanded)
%              Number of leaves         :   69 ( 333 expanded)
%              Depth                    :   13
%              Number of atoms          :  828 (2134 expanded)
%              Number of equality atoms :   91 ( 235 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f903,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f112,f119,f126,f138,f159,f160,f169,f192,f200,f209,f219,f243,f257,f275,f288,f306,f320,f335,f342,f364,f373,f417,f426,f433,f456,f463,f481,f497,f504,f513,f520,f562,f569,f576,f649,f666,f705,f722,f729,f746,f753,f758,f767,f774,f838,f845,f884,f896])).

fof(f896,plain,
    ( ~ spl4_0
    | spl4_13
    | ~ spl4_26
    | ~ spl4_28
    | ~ spl4_34
    | ~ spl4_36
    | ~ spl4_54
    | ~ spl4_88 ),
    inference(avatar_contradiction_clause,[],[f895])).

fof(f895,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_13
    | ~ spl4_26
    | ~ spl4_28
    | ~ spl4_34
    | ~ spl4_36
    | ~ spl4_54
    | ~ spl4_88 ),
    inference(subsumption_resolution,[],[f894,f709])).

fof(f709,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_13
    | ~ spl4_26
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f708,f651])).

fof(f651,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_0
    | ~ spl4_26
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f577,f274])).

fof(f274,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl4_28
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f577,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_0
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f104,f256,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t101_tops_1.p',d1_tops_1)).

fof(f256,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl4_26
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f104,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f708,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_0
    | ~ spl4_13
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f104,f256,f155,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t101_tops_1.p',d7_tops_1)).

fof(f155,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl4_13
  <=> ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f894,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_34
    | ~ spl4_36
    | ~ spl4_54
    | ~ spl4_88 ),
    inference(forward_demodulation,[],[f891,f696])).

fof(f696,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = sK1
    | ~ spl4_0
    | ~ spl4_34
    | ~ spl4_36
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f688,f477])).

fof(f477,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f476])).

fof(f476,plain,
    ( spl4_54
  <=> k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f688,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_34
    | ~ spl4_36
    | ~ spl4_54 ),
    inference(backward_demodulation,[],[f671,f588])).

fof(f588,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))) = k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f104,f334,f79])).

fof(f334,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl4_36
  <=> m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f671,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | ~ spl4_0
    | ~ spl4_34
    | ~ spl4_54 ),
    inference(backward_demodulation,[],[f477,f392])).

fof(f392,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f104,f319,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t101_tops_1.p',projectivity_k1_tops_1)).

fof(f319,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl4_34
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f891,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_88 ),
    inference(unit_resulting_resolution,[],[f883,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t101_tops_1.p',involutiveness_k3_subset_1)).

fof(f883,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_88 ),
    inference(avatar_component_clause,[],[f882])).

fof(f882,plain,
    ( spl4_88
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f884,plain,
    ( spl4_88
    | ~ spl4_0
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f541,f518,f103,f882])).

fof(f518,plain,
    ( spl4_62
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f541,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_62 ),
    inference(unit_resulting_resolution,[],[f104,f519,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t101_tops_1.p',dt_k2_pre_topc)).

fof(f519,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f518])).

fof(f845,plain,
    ( spl4_86
    | ~ spl4_4
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f486,f461,f117,f843])).

fof(f843,plain,
    ( spl4_86
  <=> m1_subset_1(k1_tops_1(sK3,k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f117,plain,
    ( spl4_4
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f461,plain,
    ( spl4_52
  <=> m1_subset_1(k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f486,plain,
    ( m1_subset_1(k1_tops_1(sK3,k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_52 ),
    inference(unit_resulting_resolution,[],[f118,f462,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t101_tops_1.p',dt_k1_tops_1)).

fof(f462,plain,
    ( m1_subset_1(k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f461])).

fof(f118,plain,
    ( l1_pre_topc(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f838,plain,
    ( spl4_84
    | ~ spl4_4
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f466,f454,f117,f836])).

fof(f836,plain,
    ( spl4_84
  <=> m1_subset_1(k2_pre_topc(sK3,k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f454,plain,
    ( spl4_50
  <=> m1_subset_1(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f466,plain,
    ( m1_subset_1(k2_pre_topc(sK3,k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_50 ),
    inference(unit_resulting_resolution,[],[f118,f455,f91])).

fof(f455,plain,
    ( m1_subset_1(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f454])).

fof(f774,plain,
    ( spl4_82
    | ~ spl4_0
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f445,f431,f103,f772])).

fof(f772,plain,
    ( spl4_82
  <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f431,plain,
    ( spl4_48
  <=> m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f445,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_48 ),
    inference(unit_resulting_resolution,[],[f104,f432,f90])).

fof(f432,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f431])).

fof(f767,plain,
    ( spl4_80
    | ~ spl4_0
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f436,f424,f103,f765])).

fof(f765,plain,
    ( spl4_80
  <=> m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f424,plain,
    ( spl4_46
  <=> m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f436,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f104,f425,f91])).

fof(f425,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f424])).

fof(f758,plain,
    ( spl4_68
    | ~ spl4_60
    | ~ spl4_72 ),
    inference(avatar_split_clause,[],[f754,f720,f511,f574])).

fof(f574,plain,
    ( spl4_68
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f511,plain,
    ( spl4_60
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f720,plain,
    ( spl4_72
  <=> k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f754,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_60
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f749,f512])).

fof(f512,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f511])).

fof(f749,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_72 ),
    inference(superposition,[],[f89,f721])).

fof(f721,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = sK1
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f720])).

fof(f753,plain,
    ( ~ spl4_60
    | spl4_69
    | ~ spl4_72 ),
    inference(avatar_contradiction_clause,[],[f752])).

fof(f752,plain,
    ( $false
    | ~ spl4_60
    | ~ spl4_69
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f751,f512])).

fof(f751,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_69
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f749,f572])).

fof(f572,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f571])).

fof(f571,plain,
    ( spl4_69
  <=> k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f746,plain,
    ( ~ spl4_77
    | spl4_78
    | ~ spl4_0
    | ~ spl4_30
    | ~ spl4_34
    | ~ spl4_44
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f694,f476,f415,f318,f286,f103,f744,f738])).

fof(f738,plain,
    ( spl4_77
  <=> k2_pre_topc(sK0,sK1) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f744,plain,
    ( spl4_78
  <=> v5_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f286,plain,
    ( spl4_30
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f415,plain,
    ( spl4_44
  <=> k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f694,plain,
    ( v5_tops_1(sK1,sK0)
    | k2_pre_topc(sK0,sK1) != sK1
    | ~ spl4_0
    | ~ spl4_30
    | ~ spl4_34
    | ~ spl4_44
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f686,f671])).

fof(f686,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | v5_tops_1(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_0
    | ~ spl4_30
    | ~ spl4_34
    | ~ spl4_44
    | ~ spl4_54 ),
    inference(backward_demodulation,[],[f671,f549])).

fof(f549,plain,
    ( k1_tops_1(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | v5_tops_1(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_0
    | ~ spl4_30
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f548,f104])).

fof(f548,plain,
    ( k1_tops_1(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | v5_tops_1(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_30
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f547,f287])).

fof(f287,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f286])).

fof(f547,plain,
    ( k1_tops_1(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | v5_tops_1(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_44 ),
    inference(superposition,[],[f83,f416])).

fof(f416,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f415])).

fof(f729,plain,
    ( spl4_74
    | ~ spl4_0
    | ~ spl4_34
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f715,f476,f318,f103,f727])).

fof(f727,plain,
    ( spl4_74
  <=> v5_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f715,plain,
    ( v5_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl4_0
    | ~ spl4_34
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f714,f104])).

fof(f714,plain,
    ( v5_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_34
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f713,f319])).

fof(f713,plain,
    ( v5_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_54 ),
    inference(trivial_inequality_removal,[],[f711])).

fof(f711,plain,
    ( k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,sK1)
    | v5_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_54 ),
    inference(superposition,[],[f83,f477])).

fof(f722,plain,
    ( spl4_72
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_34
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f689,f476,f318,f124,f103,f720])).

fof(f124,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f689,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = sK1
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_34
    | ~ spl4_54 ),
    inference(backward_demodulation,[],[f671,f591])).

fof(f591,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1)
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f104,f125,f79])).

fof(f125,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f705,plain,
    ( spl4_70
    | ~ spl4_0
    | ~ spl4_34
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f671,f476,f318,f103,f703])).

fof(f703,plain,
    ( spl4_70
  <=> k1_tops_1(sK0,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f666,plain,
    ( ~ spl4_0
    | ~ spl4_6
    | ~ spl4_10
    | spl4_55 ),
    inference(avatar_contradiction_clause,[],[f665])).

fof(f665,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_55 ),
    inference(subsumption_resolution,[],[f152,f482])).

fof(f482,plain,
    ( ~ v6_tops_1(sK1,sK0)
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_55 ),
    inference(unit_resulting_resolution,[],[f104,f125,f480,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t101_tops_1.p',d8_tops_1)).

fof(f480,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) != sK1
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f479])).

fof(f479,plain,
    ( spl4_55
  <=> k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f152,plain,
    ( v6_tops_1(sK1,sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl4_10
  <=> v6_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f649,plain,
    ( ~ spl4_0
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_26
    | ~ spl4_28
    | ~ spl4_36
    | spl4_55
    | ~ spl4_58
    | ~ spl4_68 ),
    inference(avatar_contradiction_clause,[],[f648])).

fof(f648,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_26
    | ~ spl4_28
    | ~ spl4_36
    | ~ spl4_55
    | ~ spl4_58
    | ~ spl4_68 ),
    inference(subsumption_resolution,[],[f647,f480])).

fof(f647,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_26
    | ~ spl4_28
    | ~ spl4_36
    | ~ spl4_58
    | ~ spl4_68 ),
    inference(forward_demodulation,[],[f644,f274])).

fof(f644,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_26
    | ~ spl4_28
    | ~ spl4_36
    | ~ spl4_58
    | ~ spl4_68 ),
    inference(backward_demodulation,[],[f639,f616])).

fof(f616,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_28
    | ~ spl4_36
    | ~ spl4_68 ),
    inference(forward_demodulation,[],[f588,f597])).

fof(f597,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_28
    | ~ spl4_68 ),
    inference(forward_demodulation,[],[f596,f274])).

fof(f596,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_tops_1(sK0,sK1)
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_68 ),
    inference(forward_demodulation,[],[f591,f575])).

fof(f575,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f574])).

fof(f639,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_26
    | ~ spl4_28
    | ~ spl4_58
    | ~ spl4_68 ),
    inference(backward_demodulation,[],[f635,f505])).

fof(f505,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_0
    | ~ spl4_12
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f104,f158,f256,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v5_tops_1(X1,X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f158,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl4_12
  <=> v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f635,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_28
    | ~ spl4_58
    | ~ spl4_68 ),
    inference(forward_demodulation,[],[f634,f274])).

fof(f634,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_28
    | ~ spl4_58
    | ~ spl4_68 ),
    inference(forward_demodulation,[],[f578,f597])).

fof(f578,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_58 ),
    inference(unit_resulting_resolution,[],[f104,f503,f79])).

fof(f503,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f502])).

fof(f502,plain,
    ( spl4_58
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f576,plain,
    ( spl4_68
    | ~ spl4_0
    | ~ spl4_12
    | ~ spl4_26
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f528,f495,f255,f157,f103,f574])).

fof(f495,plain,
    ( spl4_56
  <=> m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f528,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_0
    | ~ spl4_12
    | ~ spl4_26
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f523,f505])).

fof(f523,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl4_0
    | ~ spl4_56 ),
    inference(unit_resulting_resolution,[],[f104,f496,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t101_tops_1.p',projectivity_k2_pre_topc)).

fof(f496,plain,
    ( m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f495])).

fof(f569,plain,
    ( spl4_66
    | ~ spl4_0
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f382,f371,f103,f567])).

fof(f567,plain,
    ( spl4_66
  <=> m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f371,plain,
    ( spl4_42
  <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f382,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_42 ),
    inference(unit_resulting_resolution,[],[f104,f372,f91])).

fof(f372,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f371])).

fof(f562,plain,
    ( spl4_64
    | ~ spl4_0
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f376,f333,f103,f560])).

fof(f560,plain,
    ( spl4_64
  <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f376,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f104,f334,f90])).

fof(f520,plain,
    ( spl4_62
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f324,f318,f518])).

fof(f324,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f319,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t101_tops_1.p',dt_k3_subset_1)).

fof(f513,plain,
    ( spl4_60
    | ~ spl4_0
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f307,f255,f103,f511])).

fof(f307,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f104,f256,f91])).

fof(f504,plain,
    ( spl4_58
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f291,f286,f502])).

fof(f291,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_30 ),
    inference(unit_resulting_resolution,[],[f287,f88])).

fof(f497,plain,
    ( spl4_56
    | ~ spl4_0
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f276,f255,f103,f495])).

fof(f276,plain,
    ( m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f104,f256,f90])).

fof(f481,plain,
    ( ~ spl4_55
    | ~ spl4_0
    | ~ spl4_6
    | spl4_11 ),
    inference(avatar_split_clause,[],[f472,f148,f124,f103,f479])).

fof(f148,plain,
    ( spl4_11
  <=> ~ v6_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f472,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) != sK1
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f104,f149,f125,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v6_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f149,plain,
    ( ~ v6_tops_1(sK1,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f148])).

fof(f463,plain,
    ( spl4_52
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f313,f117,f461])).

fof(f313,plain,
    ( m1_subset_1(k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f118,f84,f91])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t101_tops_1.p',existence_m1_subset_1)).

fof(f456,plain,
    ( spl4_50
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f281,f117,f454])).

fof(f281,plain,
    ( m1_subset_1(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f118,f84,f90])).

fof(f433,plain,
    ( spl4_48
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f312,f103,f431])).

fof(f312,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f104,f84,f91])).

fof(f426,plain,
    ( spl4_46
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f280,f103,f424])).

fof(f280,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f104,f84,f90])).

fof(f417,plain,
    ( spl4_44
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f394,f124,f103,f415])).

fof(f394,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f104,f125,f93])).

fof(f373,plain,
    ( spl4_42
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f322,f318,f103,f371])).

fof(f322,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f104,f319,f90])).

fof(f364,plain,
    ( spl4_40
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f349,f124,f103,f362])).

fof(f362,plain,
    ( spl4_40
  <=> k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f349,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f104,f125,f92])).

fof(f342,plain,
    ( spl4_38
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f321,f318,f103,f340])).

fof(f340,plain,
    ( spl4_38
  <=> m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f321,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f104,f319,f91])).

fof(f335,plain,
    ( spl4_36
    | ~ spl4_0
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f310,f286,f103,f333])).

fof(f310,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_30 ),
    inference(unit_resulting_resolution,[],[f104,f287,f91])).

fof(f320,plain,
    ( spl4_34
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f311,f124,f103,f318])).

fof(f311,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f104,f125,f91])).

fof(f306,plain,
    ( spl4_32
    | ~ spl4_0
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f289,f286,f103,f304])).

fof(f304,plain,
    ( spl4_32
  <=> m1_subset_1(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f289,plain,
    ( m1_subset_1(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_30 ),
    inference(unit_resulting_resolution,[],[f104,f287,f90])).

fof(f288,plain,
    ( spl4_30
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f279,f124,f103,f286])).

fof(f279,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f104,f125,f90])).

fof(f275,plain,
    ( spl4_28
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f245,f124,f273])).

fof(f245,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f125,f89])).

fof(f257,plain,
    ( spl4_26
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f185,f124,f255])).

fof(f185,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f125,f88])).

fof(f243,plain,
    ( spl4_24
    | ~ spl4_2
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f225,f217,f110,f241])).

fof(f241,plain,
    ( spl4_24
  <=> k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f110,plain,
    ( spl4_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f217,plain,
    ( spl4_22
  <=> v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f225,plain,
    ( k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl4_2
    | ~ spl4_22 ),
    inference(unit_resulting_resolution,[],[f218,f129])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f127,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t101_tops_1.p',t6_boole)).

fof(f127,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f111,f78])).

fof(f111,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f218,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f217])).

fof(f219,plain,
    ( spl4_22
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f212,f207,f110,f217])).

fof(f207,plain,
    ( spl4_20
  <=> m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f212,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f84,f211,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t101_tops_1.p',t2_subset)).

fof(f211,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f111,f208,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
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
    file('/export/starexec/sandbox/benchmark/tops_1__t101_tops_1.p',t5_subset)).

fof(f208,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f207])).

fof(f209,plain,
    ( spl4_20
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f201,f198,f207])).

fof(f198,plain,
    ( spl4_18
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f201,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f199,f88])).

fof(f199,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f198])).

fof(f200,plain,
    ( spl4_18
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f193,f190,f198])).

fof(f190,plain,
    ( spl4_16
  <=> o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f193,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_16 ),
    inference(superposition,[],[f84,f191])).

fof(f191,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f190])).

fof(f192,plain,
    ( spl4_16
    | ~ spl4_2
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f175,f167,f110,f190])).

fof(f167,plain,
    ( spl4_14
  <=> v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f175,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f168,f129])).

fof(f168,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f167])).

fof(f169,plain,
    ( spl4_14
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f162,f110,f167])).

fof(f162,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f84,f161,f87])).

fof(f161,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f111,f84,f97])).

fof(f160,plain,
    ( ~ spl4_11
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f74,f154,f148])).

fof(f74,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
    ( ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v6_tops_1(sK1,sK0) )
    & ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | v6_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f61,f63,f62])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v6_tops_1(X1,X0) )
            & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v6_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | ~ v6_tops_1(X1,sK0) )
          & ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | v6_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v6_tops_1(X1,X0) )
          & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v6_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),sK1),X0)
          | ~ v6_tops_1(sK1,X0) )
        & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),sK1),X0)
          | v6_tops_1(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v6_tops_1(X1,X0) )
          & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v6_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v6_tops_1(X1,X0) )
          & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v6_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v6_tops_1(X1,X0)
          <~> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v6_tops_1(X1,X0)
            <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t101_tops_1.p',t101_tops_1)).

fof(f159,plain,
    ( spl4_10
    | spl4_12 ),
    inference(avatar_split_clause,[],[f73,f157,f151])).

fof(f73,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f138,plain,
    ( spl4_8
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f127,f110,f136])).

fof(f136,plain,
    ( spl4_8
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f126,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f72,f124])).

fof(f72,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f64])).

fof(f119,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f98,f117])).

fof(f98,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f69])).

fof(f69,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK3) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t101_tops_1.p',existence_l1_pre_topc)).

fof(f112,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f75,f110])).

fof(f75,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t101_tops_1.p',dt_o_0_0_xboole_0)).

fof(f105,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f71,f103])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).
%------------------------------------------------------------------------------
