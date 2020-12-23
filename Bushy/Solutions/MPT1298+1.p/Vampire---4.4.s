%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t16_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:35 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 303 expanded)
%              Number of leaves         :   28 ( 120 expanded)
%              Depth                    :   13
%              Number of atoms          :  555 ( 960 expanded)
%              Number of equality atoms :   16 (  27 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1986,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f99,f136,f142,f163,f172,f216,f248,f461,f1199,f1426,f1519,f1636,f1665,f1706,f1712,f1877,f1983])).

fof(f1983,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_8
    | spl7_25
    | ~ spl7_28
    | ~ spl7_236
    | ~ spl7_324 ),
    inference(avatar_contradiction_clause,[],[f1982])).

fof(f1982,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_236
    | ~ spl7_324 ),
    inference(subsumption_resolution,[],[f1981,f215])).

fof(f215,plain,
    ( ~ v3_pre_topc(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl7_25
  <=> ~ v3_pre_topc(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f1981,plain,
    ( v3_pre_topc(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_28
    | ~ spl7_236
    | ~ spl7_324 ),
    inference(forward_demodulation,[],[f1980,f256])).

fof(f256,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)))) = sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl7_28 ),
    inference(resolution,[],[f247,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t16_tops_2.p',involutiveness_k3_subset_1)).

fof(f247,plain,
    ( m1_subset_1(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl7_28
  <=> m1_subset_1(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f1980,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_236
    | ~ spl7_324 ),
    inference(subsumption_resolution,[],[f1979,f1973])).

fof(f1973,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_236
    | ~ spl7_324 ),
    inference(subsumption_resolution,[],[f1965,f1198])).

fof(f1198,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK1)
    | ~ spl7_236 ),
    inference(avatar_component_clause,[],[f1197])).

fof(f1197,plain,
    ( spl7_236
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_236])])).

fof(f1965,plain,
    ( ~ r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_324 ),
    inference(resolution,[],[f1876,f1713])).

fof(f1713,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,sK1)
        | v4_pre_topc(X1,sK0) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f119,f132])).

fof(f132,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl7_8
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f119,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,sK1)
        | v4_pre_topc(X1,sK0)
        | ~ v2_tops_2(sK1,sK0) )
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f104,f94])).

fof(f94,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f104,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,sK1)
        | v4_pre_topc(X1,sK0)
        | ~ v2_tops_2(sK1,sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f98,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v4_pre_topc(X2,X0)
      | ~ v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t16_tops_2.p',d2_tops_2)).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl7_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1876,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_324 ),
    inference(avatar_component_clause,[],[f1875])).

fof(f1875,plain,
    ( spl7_324
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_324])])).

fof(f1979,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK0)
    | ~ spl7_0
    | ~ spl7_324 ),
    inference(subsumption_resolution,[],[f1969,f94])).

fof(f1969,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK0)
    | ~ spl7_324 ),
    inference(resolution,[],[f1876,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t16_tops_2.p',t29_tops_1)).

fof(f1877,plain,
    ( spl7_324
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f255,f246,f1875])).

fof(f255,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_28 ),
    inference(resolution,[],[f247,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t16_tops_2.p',dt_k3_subset_1)).

fof(f1712,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | spl7_9
    | ~ spl7_10
    | ~ spl7_22
    | ~ spl7_280
    | ~ spl7_292
    | ~ spl7_316 ),
    inference(avatar_contradiction_clause,[],[f1711])).

fof(f1711,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_22
    | ~ spl7_280
    | ~ spl7_292
    | ~ spl7_316 ),
    inference(subsumption_resolution,[],[f1651,f1709])).

fof(f1709,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_9
    | ~ spl7_280
    | ~ spl7_292 ),
    inference(subsumption_resolution,[],[f1663,f1708])).

fof(f1708,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1),sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f122,f1358])).

fof(f1358,plain,
    ( ~ v2_tops_2(sK1,sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f1357])).

fof(f1357,plain,
    ( spl7_9
  <=> ~ v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f122,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1),sK0)
    | v2_tops_2(sK1,sK0)
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f107,f94])).

fof(f107,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK4(sK0,sK1),sK0)
    | v2_tops_2(sK1,sK0)
    | ~ spl7_2 ),
    inference(resolution,[],[f98,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(sK4(X0,X1),X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1663,plain,
    ( v4_pre_topc(sK4(sK0,sK1),sK0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),sK0)
    | ~ spl7_0
    | ~ spl7_280
    | ~ spl7_292 ),
    inference(forward_demodulation,[],[f1442,f1518])).

fof(f1518,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1))) = sK4(sK0,sK1)
    | ~ spl7_292 ),
    inference(avatar_component_clause,[],[f1517])).

fof(f1517,plain,
    ( spl7_292
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1))) = sK4(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_292])])).

fof(f1442,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1))),sK0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),sK0)
    | ~ spl7_0
    | ~ spl7_280 ),
    inference(subsumption_resolution,[],[f1434,f94])).

fof(f1434,plain,
    ( ~ l1_pre_topc(sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1))),sK0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),sK0)
    | ~ spl7_280 ),
    inference(resolution,[],[f1425,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t16_tops_2.p',t30_tops_1)).

fof(f1425,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_280 ),
    inference(avatar_component_clause,[],[f1424])).

fof(f1424,plain,
    ( spl7_280
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_280])])).

fof(f1651,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),sK0)
    | ~ spl7_0
    | ~ spl7_10
    | ~ spl7_22
    | ~ spl7_280
    | ~ spl7_316 ),
    inference(subsumption_resolution,[],[f1643,f1425])).

fof(f1643,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),sK0)
    | ~ spl7_0
    | ~ spl7_10
    | ~ spl7_22
    | ~ spl7_316 ),
    inference(resolution,[],[f1635,f1475])).

fof(f1475,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k7_setfam_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X2,sK0) )
    | ~ spl7_0
    | ~ spl7_10
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f1347,f135])).

fof(f135,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl7_10
  <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f1347,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,k7_setfam_1(u1_struct_0(sK0),sK1))
        | v3_pre_topc(X2,sK0)
        | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl7_0
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f183,f94])).

fof(f183,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,k7_setfam_1(u1_struct_0(sK0),sK1))
        | v3_pre_topc(X2,sK0)
        | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl7_22 ),
    inference(resolution,[],[f171,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v3_pre_topc(X2,X0)
      | ~ v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t16_tops_2.p',d1_tops_2)).

fof(f171,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl7_22
  <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f1635,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl7_316 ),
    inference(avatar_component_clause,[],[f1634])).

fof(f1634,plain,
    ( spl7_316
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_316])])).

fof(f1706,plain,
    ( spl7_268
    | ~ spl7_0
    | ~ spl7_2
    | spl7_9 ),
    inference(avatar_split_clause,[],[f1704,f1357,f97,f93,f1373])).

fof(f1373,plain,
    ( spl7_268
  <=> r2_hidden(sK4(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_268])])).

fof(f1704,plain,
    ( r2_hidden(sK4(sK0,sK1),sK1)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f121,f1358])).

fof(f121,plain,
    ( r2_hidden(sK4(sK0,sK1),sK1)
    | v2_tops_2(sK1,sK0)
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f106,f94])).

fof(f106,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK4(sK0,sK1),sK1)
    | v2_tops_2(sK1,sK0)
    | ~ spl7_2 ),
    inference(resolution,[],[f98,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK4(X0,X1),X1)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1665,plain,
    ( spl7_266
    | ~ spl7_0
    | ~ spl7_2
    | spl7_9 ),
    inference(avatar_split_clause,[],[f1660,f1357,f97,f93,f1369])).

fof(f1369,plain,
    ( spl7_266
  <=> m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_266])])).

fof(f1660,plain,
    ( m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f120,f1358])).

fof(f120,plain,
    ( m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_2(sK1,sK0)
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f105,f94])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_2(sK1,sK0)
    | ~ spl7_2 ),
    inference(resolution,[],[f98,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1636,plain,
    ( spl7_316
    | ~ spl7_2
    | ~ spl7_18
    | ~ spl7_22
    | ~ spl7_266
    | ~ spl7_268 ),
    inference(avatar_split_clause,[],[f1385,f1373,f1369,f170,f161,f97,f1634])).

fof(f161,plain,
    ( spl7_18
  <=> k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f1385,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl7_2
    | ~ spl7_18
    | ~ spl7_22
    | ~ spl7_266
    | ~ spl7_268 ),
    inference(subsumption_resolution,[],[f1377,f1374])).

fof(f1374,plain,
    ( r2_hidden(sK4(sK0,sK1),sK1)
    | ~ spl7_268 ),
    inference(avatar_component_clause,[],[f1373])).

fof(f1377,plain,
    ( ~ r2_hidden(sK4(sK0,sK1),sK1)
    | r2_hidden(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl7_2
    | ~ spl7_18
    | ~ spl7_22
    | ~ spl7_266 ),
    inference(resolution,[],[f1370,f180])).

fof(f180,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,sK1)
        | r2_hidden(k3_subset_1(u1_struct_0(sK0),X1),k7_setfam_1(u1_struct_0(sK0),sK1)) )
    | ~ spl7_2
    | ~ spl7_18
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f179,f162])).

fof(f162,plain,
    ( k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f179,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k3_subset_1(u1_struct_0(sK0),X1),k7_setfam_1(u1_struct_0(sK0),sK1))
        | ~ r2_hidden(X1,k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))) )
    | ~ spl7_2
    | ~ spl7_18
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f178,f171])).

fof(f178,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k3_subset_1(u1_struct_0(sK0),X1),k7_setfam_1(u1_struct_0(sK0),sK1))
        | ~ r2_hidden(X1,k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))) )
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f174,f98])).

fof(f174,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k3_subset_1(u1_struct_0(sK0),X1),k7_setfam_1(u1_struct_0(sK0),sK1))
        | ~ r2_hidden(X1,k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))) )
    | ~ spl7_18 ),
    inference(superposition,[],[f90,f162])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X3),X1)
      | ~ r2_hidden(X3,k7_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k7_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t16_tops_2.p',d8_setfam_1)).

fof(f1370,plain,
    ( m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_266 ),
    inference(avatar_component_clause,[],[f1369])).

fof(f1519,plain,
    ( spl7_292
    | ~ spl7_266 ),
    inference(avatar_split_clause,[],[f1382,f1369,f1517])).

fof(f1382,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1))) = sK4(sK0,sK1)
    | ~ spl7_266 ),
    inference(resolution,[],[f1370,f86])).

fof(f1426,plain,
    ( spl7_280
    | ~ spl7_266 ),
    inference(avatar_split_clause,[],[f1381,f1369,f1424])).

fof(f1381,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_266 ),
    inference(resolution,[],[f1370,f87])).

fof(f1199,plain,
    ( spl7_236
    | ~ spl7_2
    | ~ spl7_22
    | ~ spl7_28
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f609,f459,f246,f170,f97,f1197])).

fof(f459,plain,
    ( spl7_64
  <=> r2_hidden(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f609,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK1)
    | ~ spl7_2
    | ~ spl7_22
    | ~ spl7_28
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f608,f247])).

fof(f608,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK1)
    | ~ m1_subset_1(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_2
    | ~ spl7_22
    | ~ spl7_64 ),
    inference(resolution,[],[f199,f460])).

fof(f460,plain,
    ( r2_hidden(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f459])).

fof(f199,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k7_setfam_1(u1_struct_0(sK0),sK1))
        | r2_hidden(k3_subset_1(u1_struct_0(sK0),X1),sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f182,f98])).

fof(f182,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k3_subset_1(u1_struct_0(sK0),X1),sK1)
        | ~ r2_hidden(X1,k7_setfam_1(u1_struct_0(sK0),sK1)) )
    | ~ spl7_22 ),
    inference(resolution,[],[f171,f90])).

fof(f461,plain,
    ( spl7_64
    | ~ spl7_0
    | spl7_11
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f203,f170,f140,f93,f459])).

fof(f140,plain,
    ( spl7_11
  <=> ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f203,plain,
    ( r2_hidden(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl7_0
    | ~ spl7_11
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f202,f141])).

fof(f141,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f202,plain,
    ( r2_hidden(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl7_0
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f185,f94])).

fof(f185,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl7_22 ),
    inference(resolution,[],[f171,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f248,plain,
    ( spl7_28
    | ~ spl7_0
    | spl7_11
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f201,f170,f140,f93,f246])).

fof(f201,plain,
    ( m1_subset_1(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_0
    | ~ spl7_11
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f200,f141])).

fof(f200,plain,
    ( m1_subset_1(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl7_0
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f184,f94])).

fof(f184,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl7_22 ),
    inference(resolution,[],[f171,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f216,plain,
    ( ~ spl7_25
    | ~ spl7_0
    | spl7_11
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f205,f170,f140,f93,f214])).

fof(f205,plain,
    ( ~ v3_pre_topc(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl7_0
    | ~ spl7_11
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f204,f141])).

fof(f204,plain,
    ( ~ v3_pre_topc(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl7_0
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f186,f94])).

fof(f186,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl7_22 ),
    inference(resolution,[],[f171,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(sK2(X0,X1),X0)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f172,plain,
    ( spl7_22
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f109,f97,f170])).

fof(f109,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_2 ),
    inference(resolution,[],[f98,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t16_tops_2.p',dt_k7_setfam_1)).

fof(f163,plain,
    ( spl7_18
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f108,f97,f161])).

fof(f108,plain,
    ( k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl7_2 ),
    inference(resolution,[],[f98,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t16_tops_2.p',involutiveness_k7_setfam_1)).

fof(f142,plain,
    ( ~ spl7_11
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f138,f131,f140])).

fof(f138,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f56,f132])).

fof(f56,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_2(X1,X0)
          <~> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v2_tops_2(X1,X0)
            <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t16_tops_2.p',t16_tops_2)).

fof(f136,plain,
    ( spl7_8
    | spl7_10 ),
    inference(avatar_split_clause,[],[f55,f134,f131])).

fof(f55,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f99,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f57,f97])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f95,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f58,f93])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
