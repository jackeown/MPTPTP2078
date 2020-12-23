%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1349+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:47 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  399 (1130 expanded)
%              Number of leaves         :   64 ( 485 expanded)
%              Depth                    :   23
%              Number of atoms          : 2556 (7855 expanded)
%              Number of equality atoms :  275 (1437 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (25600)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f1445,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f101,f106,f111,f116,f121,f126,f135,f140,f146,f152,f163,f168,f176,f193,f197,f218,f224,f226,f236,f243,f255,f355,f359,f371,f375,f386,f390,f424,f430,f433,f580,f662,f746,f762,f774,f831,f940,f965,f1179,f1233,f1264,f1348,f1354,f1366,f1370,f1386,f1393,f1399,f1406,f1444])).

fof(f1444,plain,
    ( ~ spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | spl6_25 ),
    inference(avatar_contradiction_clause,[],[f1440])).

fof(f1440,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | spl6_25 ),
    inference(unit_resulting_resolution,[],[f100,f115,f120,f130,f125,f139,f337,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
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
             => ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).

fof(f337,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl6_25 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl6_25
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f139,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl6_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f125,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl6_7
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f130,plain,
    ( v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl6_8
  <=> v3_tops_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f120,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f115,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl6_5
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f100,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl6_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1406,plain,
    ( ~ spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f1405])).

fof(f1405,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f100,f115,f120,f130,f125,f139,f133,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f133,plain,
    ( ~ v2_funct_1(sK2)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl6_9
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f1399,plain,
    ( ~ spl6_17
    | ~ spl6_36
    | spl6_128 ),
    inference(avatar_contradiction_clause,[],[f1398])).

fof(f1398,plain,
    ( $false
    | ~ spl6_17
    | ~ spl6_36
    | spl6_128 ),
    inference(subsumption_resolution,[],[f1396,f188])).

fof(f188,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl6_17
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f1396,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_36
    | spl6_128 ),
    inference(resolution,[],[f1392,f429])).

fof(f429,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k9_relat_1(sK2,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl6_36
  <=> ! [X0] :
        ( r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k9_relat_1(sK2,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f1392,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k9_relat_1(sK2,sK3)))
    | spl6_128 ),
    inference(avatar_component_clause,[],[f1390])).

fof(f1390,plain,
    ( spl6_128
  <=> r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k9_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_128])])).

fof(f1393,plain,
    ( ~ spl6_128
    | spl6_123
    | ~ spl6_127 ),
    inference(avatar_split_clause,[],[f1388,f1383,f1351,f1390])).

fof(f1351,plain,
    ( spl6_123
  <=> k2_pre_topc(sK1,k9_relat_1(sK2,sK3)) = k9_relat_1(sK2,k2_pre_topc(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).

fof(f1383,plain,
    ( spl6_127
  <=> r1_tarski(k2_pre_topc(sK1,k9_relat_1(sK2,sK3)),k9_relat_1(sK2,k2_pre_topc(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_127])])).

fof(f1388,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k9_relat_1(sK2,sK3)))
    | spl6_123
    | ~ spl6_127 ),
    inference(subsumption_resolution,[],[f1387,f1353])).

fof(f1353,plain,
    ( k2_pre_topc(sK1,k9_relat_1(sK2,sK3)) != k9_relat_1(sK2,k2_pre_topc(sK0,sK3))
    | spl6_123 ),
    inference(avatar_component_clause,[],[f1351])).

fof(f1387,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k9_relat_1(sK2,sK3)))
    | k2_pre_topc(sK1,k9_relat_1(sK2,sK3)) = k9_relat_1(sK2,k2_pre_topc(sK0,sK3))
    | ~ spl6_127 ),
    inference(resolution,[],[f1385,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1385,plain,
    ( r1_tarski(k2_pre_topc(sK1,k9_relat_1(sK2,sK3)),k9_relat_1(sK2,k2_pre_topc(sK0,sK3)))
    | ~ spl6_127 ),
    inference(avatar_component_clause,[],[f1383])).

fof(f1386,plain,
    ( spl6_127
    | ~ spl6_17
    | ~ spl6_122
    | ~ spl6_125
    | ~ spl6_126 ),
    inference(avatar_split_clause,[],[f1377,f1368,f1363,f1345,f186,f1383])).

fof(f1345,plain,
    ( spl6_122
  <=> k9_relat_1(sK2,sK3) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_122])])).

fof(f1363,plain,
    ( spl6_125
  <=> k9_relat_1(sK2,k2_pre_topc(sK0,sK3)) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_125])])).

fof(f1368,plain,
    ( spl6_126
  <=> ! [X1] :
        ( r1_tarski(k2_pre_topc(sK1,k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_126])])).

fof(f1377,plain,
    ( r1_tarski(k2_pre_topc(sK1,k9_relat_1(sK2,sK3)),k9_relat_1(sK2,k2_pre_topc(sK0,sK3)))
    | ~ spl6_17
    | ~ spl6_122
    | ~ spl6_125
    | ~ spl6_126 ),
    inference(forward_demodulation,[],[f1376,f1347])).

fof(f1347,plain,
    ( k9_relat_1(sK2,sK3) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    | ~ spl6_122 ),
    inference(avatar_component_clause,[],[f1345])).

fof(f1376,plain,
    ( r1_tarski(k2_pre_topc(sK1,k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),k9_relat_1(sK2,k2_pre_topc(sK0,sK3)))
    | ~ spl6_17
    | ~ spl6_125
    | ~ spl6_126 ),
    inference(forward_demodulation,[],[f1372,f1365])).

fof(f1365,plain,
    ( k9_relat_1(sK2,k2_pre_topc(sK0,sK3)) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3))
    | ~ spl6_125 ),
    inference(avatar_component_clause,[],[f1363])).

fof(f1372,plain,
    ( r1_tarski(k2_pre_topc(sK1,k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3)))
    | ~ spl6_17
    | ~ spl6_126 ),
    inference(resolution,[],[f1369,f188])).

fof(f1369,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK1,k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1))) )
    | ~ spl6_126 ),
    inference(avatar_component_clause,[],[f1368])).

fof(f1370,plain,
    ( spl6_126
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f1292,f373,f137,f128,f123,f118,f113,f108,f98,f93,f1368])).

fof(f93,plain,
    ( spl6_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f108,plain,
    ( spl6_4
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f373,plain,
    ( spl6_32
  <=> ! [X1] : k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f1292,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK1,k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f1291,f374])).

fof(f374,plain,
    ( ! [X1] : k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f373])).

fof(f1291,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f1290,f374])).

fof(f1290,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f1289,f120])).

fof(f1289,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_1(sK2) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f1288,f125])).

fof(f1288,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f1287,f139])).

fof(f1287,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f1286,f110])).

fof(f110,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f1286,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1)))
        | ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f1285,f115])).

fof(f1285,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f1284,f95])).

fof(f95,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f1284,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1)))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2) )
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f1282,f100])).

fof(f1282,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2) )
    | ~ spl6_8 ),
    inference(resolution,[],[f130,f279])).

fof(f279,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v3_tops_2(X3,X1,X2)
      | r1_tarski(k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X0)),k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),k2_pre_topc(X1,X0)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f278,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f278,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_tarski(k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X0)),k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),k2_pre_topc(X1,X0)))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),u1_struct_0(X2),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v3_tops_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f277,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f277,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_tarski(k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X0)),k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),k2_pre_topc(X1,X0)))
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),u1_struct_0(X2),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v3_tops_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f276,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_funct_1(k2_tops_2(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f276,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_tarski(k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X0)),k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),k2_pre_topc(X1,X0)))
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v3_tops_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_tarski(k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X0)),k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),k2_pre_topc(X1,X0)))
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v3_tops_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f77,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK5(X0,X1,X2))))
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK5(X0,X1,X2))))
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_2)).

fof(f1366,plain,
    ( spl6_125
    | ~ spl6_17
    | ~ spl6_67 ),
    inference(avatar_split_clause,[],[f1334,f772,f186,f1363])).

fof(f772,plain,
    ( spl6_67
  <=> ! [X0] :
        ( k9_relat_1(sK2,k2_pre_topc(sK0,X0)) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f1334,plain,
    ( k9_relat_1(sK2,k2_pre_topc(sK0,sK3)) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3))
    | ~ spl6_17
    | ~ spl6_67 ),
    inference(resolution,[],[f188,f773])).

fof(f773,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_relat_1(sK2,k2_pre_topc(sK0,X0)) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0)) )
    | ~ spl6_67 ),
    inference(avatar_component_clause,[],[f772])).

fof(f1354,plain,
    ( ~ spl6_123
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f1349,f221,f161,f143,f132,f128,f1351])).

fof(f143,plain,
    ( spl6_11
  <=> k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f161,plain,
    ( spl6_14
  <=> ! [X0] : k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k9_relat_1(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f221,plain,
    ( spl6_20
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f1349,plain,
    ( k2_pre_topc(sK1,k9_relat_1(sK2,sK3)) != k9_relat_1(sK2,k2_pre_topc(sK0,sK3))
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f1274,f130])).

fof(f1274,plain,
    ( k2_pre_topc(sK1,k9_relat_1(sK2,sK3)) != k9_relat_1(sK2,k2_pre_topc(sK0,sK3))
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f1273,f162])).

fof(f162,plain,
    ( ! [X0] : k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f1273,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k9_relat_1(sK2,sK3))
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f1272,f162])).

fof(f1272,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f1271,f145])).

fof(f145,plain,
    ( k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f143])).

fof(f1271,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_9
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f1270,f223])).

fof(f223,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f221])).

fof(f1270,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f65,f134])).

fof(f134,plain,
    ( v2_funct_1(sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f132])).

fof(f65,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_funct_1(sK2)
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      | ~ v3_tops_2(sK2,sK0,sK1) )
    & ( ( ! [X4] :
            ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        & v2_funct_1(sK2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) )
      | v3_tops_2(sK2,sK0,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f38,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                  | ~ v3_tops_2(X2,X0,X1) )
                & ( ( ! [X4] :
                        ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | v3_tops_2(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(sK0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) != k2_struct_0(sK0)
                | ~ v3_tops_2(X2,sK0,X1) )
              & ( ( ! [X4] :
                      ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(sK0,X4)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(sK0) )
                | v3_tops_2(X2,sK0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(sK0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              | k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) != k2_struct_0(sK0)
              | ~ v3_tops_2(X2,sK0,X1) )
            & ( ( ! [X4] :
                    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(sK0,X4)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                & v2_funct_1(X2)
                & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                & k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(sK0) )
              | v3_tops_2(X2,sK0,X1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_pre_topc(sK0,X3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v2_funct_1(X2)
            | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) != k2_struct_0(sK1)
            | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
            | ~ v3_tops_2(X2,sK0,sK1) )
          & ( ( ! [X4] :
                  ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X4))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
              & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) )
            | v3_tops_2(X2,sK0,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_pre_topc(sK0,X3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ v2_funct_1(X2)
          | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) != k2_struct_0(sK1)
          | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
          | ~ v3_tops_2(X2,sK0,sK1) )
        & ( ( ! [X4] :
                ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X4))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) )
          | v3_tops_2(X2,sK0,sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( ? [X3] :
            ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ v2_funct_1(sK2)
        | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        | ~ v3_tops_2(sK2,sK0,sK1) )
      & ( ( ! [X4] :
              ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          & v2_funct_1(sK2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
          & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) )
        | v3_tops_2(sK2,sK0,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X4] :
                      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_tops_2(X2,X0,X1)
                <=> ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_2)).

fof(f1348,plain,
    ( spl6_122
    | ~ spl6_17
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f1333,f760,f186,f1345])).

fof(f760,plain,
    ( spl6_66
  <=> ! [X0] :
        ( k9_relat_1(sK2,X0) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f1333,plain,
    ( k9_relat_1(sK2,sK3) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    | ~ spl6_17
    | ~ spl6_66 ),
    inference(resolution,[],[f188,f761])).

fof(f761,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_relat_1(sK2,X0) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) )
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f760])).

fof(f1264,plain,
    ( ~ spl6_16
    | ~ spl6_22
    | spl6_35
    | ~ spl6_48
    | ~ spl6_58
    | spl6_88
    | ~ spl6_116 ),
    inference(avatar_contradiction_clause,[],[f1263])).

fof(f1263,plain,
    ( $false
    | ~ spl6_16
    | ~ spl6_22
    | spl6_35
    | ~ spl6_48
    | ~ spl6_58
    | spl6_88
    | ~ spl6_116 ),
    inference(subsumption_resolution,[],[f1257,f90])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1257,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k2_pre_topc(sK1,k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ spl6_16
    | ~ spl6_22
    | spl6_35
    | ~ spl6_48
    | ~ spl6_58
    | spl6_88
    | ~ spl6_116 ),
    inference(backward_demodulation,[],[f964,f1255])).

fof(f1255,plain,
    ( k2_pre_topc(sK1,k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_16
    | ~ spl6_22
    | spl6_35
    | ~ spl6_48
    | ~ spl6_58
    | ~ spl6_116 ),
    inference(forward_demodulation,[],[f1254,f661])).

fof(f661,plain,
    ( k2_pre_topc(sK1,k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f659])).

fof(f659,plain,
    ( spl6_58
  <=> k2_pre_topc(sK1,k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f1254,plain,
    ( k9_relat_1(sK2,k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_16
    | ~ spl6_22
    | spl6_35
    | ~ spl6_48
    | ~ spl6_116 ),
    inference(subsumption_resolution,[],[f1253,f175])).

fof(f175,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl6_16
  <=> v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f1253,plain,
    ( ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k9_relat_1(sK2,k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_22
    | spl6_35
    | ~ spl6_48
    | ~ spl6_116 ),
    inference(subsumption_resolution,[],[f1252,f570])).

fof(f570,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f569])).

fof(f569,plain,
    ( spl6_48
  <=> v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f1252,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k9_relat_1(sK2,k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_22
    | spl6_35
    | ~ spl6_116 ),
    inference(subsumption_resolution,[],[f1250,f423])).

fof(f423,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | spl6_35 ),
    inference(avatar_component_clause,[],[f421])).

fof(f421,plain,
    ( spl6_35
  <=> v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f1250,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k9_relat_1(sK2,k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_22
    | ~ spl6_116 ),
    inference(resolution,[],[f1232,f254])).

fof(f254,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl6_22
  <=> m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f1232,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v5_pre_topc(X1,sK1,sK0)
        | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | k9_relat_1(sK2,k2_pre_topc(sK0,sK5(sK1,sK0,X1))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,X1))) )
    | ~ spl6_116 ),
    inference(avatar_component_clause,[],[f1231])).

fof(f1231,plain,
    ( spl6_116
  <=> ! [X1] :
        ( v5_pre_topc(X1,sK1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | k9_relat_1(sK2,k2_pre_topc(sK0,sK5(sK1,sK0,X1))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).

fof(f964,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | spl6_88 ),
    inference(avatar_component_clause,[],[f962])).

fof(f962,plain,
    ( spl6_88
  <=> r1_tarski(k2_pre_topc(sK1,k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f1233,plain,
    ( spl6_116
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_111 ),
    inference(avatar_split_clause,[],[f1217,f1177,f113,f108,f1231])).

fof(f1177,plain,
    ( spl6_111
  <=> ! [X3,X4] :
        ( k9_relat_1(sK2,k2_pre_topc(sK0,sK5(X3,sK0,X4))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(X3,sK0,X4)))
        | v5_pre_topc(X4,X3,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ v1_funct_1(X4)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).

fof(f1217,plain,
    ( ! [X1] :
        ( v5_pre_topc(X1,sK1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | k9_relat_1(sK2,k2_pre_topc(sK0,sK5(sK1,sK0,X1))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,X1))) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_111 ),
    inference(subsumption_resolution,[],[f1215,f115])).

fof(f1215,plain,
    ( ! [X1] :
        ( v5_pre_topc(X1,sK1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(sK1)
        | k9_relat_1(sK2,k2_pre_topc(sK0,sK5(sK1,sK0,X1))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,X1))) )
    | ~ spl6_4
    | ~ spl6_111 ),
    inference(resolution,[],[f1178,f110])).

fof(f1178,plain,
    ( ! [X4,X3] :
        ( ~ v2_pre_topc(X3)
        | v5_pre_topc(X4,X3,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ v1_funct_1(X4)
        | ~ l1_pre_topc(X3)
        | k9_relat_1(sK2,k2_pre_topc(sK0,sK5(X3,sK0,X4))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(X3,sK0,X4))) )
    | ~ spl6_111 ),
    inference(avatar_component_clause,[],[f1177])).

fof(f1179,plain,
    ( spl6_111
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_67 ),
    inference(avatar_split_clause,[],[f785,f772,f98,f93,f1177])).

fof(f785,plain,
    ( ! [X4,X3] :
        ( k9_relat_1(sK2,k2_pre_topc(sK0,sK5(X3,sK0,X4))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(X3,sK0,X4)))
        | v5_pre_topc(X4,X3,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ v1_funct_1(X4)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_67 ),
    inference(subsumption_resolution,[],[f784,f95])).

fof(f784,plain,
    ( ! [X4,X3] :
        ( k9_relat_1(sK2,k2_pre_topc(sK0,sK5(X3,sK0,X4))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(X3,sK0,X4)))
        | v5_pre_topc(X4,X3,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ v1_funct_1(X4)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_2
    | ~ spl6_67 ),
    inference(subsumption_resolution,[],[f780,f100])).

fof(f780,plain,
    ( ! [X4,X3] :
        ( k9_relat_1(sK2,k2_pre_topc(sK0,sK5(X3,sK0,X4))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(X3,sK0,X4)))
        | v5_pre_topc(X4,X3,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ v1_funct_1(X4)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_67 ),
    inference(resolution,[],[f773,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f965,plain,
    ( ~ spl6_88
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22
    | spl6_35
    | ~ spl6_48
    | spl6_73
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f955,f938,f828,f569,f421,f252,f173,f113,f108,f962])).

fof(f828,plain,
    ( spl6_73
  <=> r1_tarski(k2_pre_topc(sK1,k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f938,plain,
    ( spl6_84
  <=> ! [X3,X4] :
        ( k9_relat_1(sK2,sK5(X3,sK0,X4)) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(X3,sK0,X4))
        | v5_pre_topc(X4,X3,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ v1_funct_1(X4)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f955,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22
    | spl6_35
    | ~ spl6_48
    | spl6_73
    | ~ spl6_84 ),
    inference(backward_demodulation,[],[f830,f950])).

fof(f950,plain,
    ( k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22
    | spl6_35
    | ~ spl6_48
    | ~ spl6_84 ),
    inference(subsumption_resolution,[],[f949,f110])).

fof(f949,plain,
    ( k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | ~ v2_pre_topc(sK1)
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22
    | spl6_35
    | ~ spl6_48
    | ~ spl6_84 ),
    inference(subsumption_resolution,[],[f948,f115])).

fof(f948,plain,
    ( k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_16
    | ~ spl6_22
    | spl6_35
    | ~ spl6_48
    | ~ spl6_84 ),
    inference(subsumption_resolution,[],[f947,f175])).

fof(f947,plain,
    ( k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_22
    | spl6_35
    | ~ spl6_48
    | ~ spl6_84 ),
    inference(subsumption_resolution,[],[f946,f570])).

fof(f946,plain,
    ( k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_22
    | spl6_35
    | ~ spl6_84 ),
    inference(subsumption_resolution,[],[f945,f423])).

fof(f945,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_22
    | ~ spl6_84 ),
    inference(resolution,[],[f939,f254])).

fof(f939,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | v5_pre_topc(X4,X3,sK0)
        | k9_relat_1(sK2,sK5(X3,sK0,X4)) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(X3,sK0,X4))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ v1_funct_1(X4)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_84 ),
    inference(avatar_component_clause,[],[f938])).

fof(f830,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | spl6_73 ),
    inference(avatar_component_clause,[],[f828])).

fof(f940,plain,
    ( spl6_84
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f770,f760,f98,f93,f938])).

fof(f770,plain,
    ( ! [X4,X3] :
        ( k9_relat_1(sK2,sK5(X3,sK0,X4)) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(X3,sK0,X4))
        | v5_pre_topc(X4,X3,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ v1_funct_1(X4)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f769,f95])).

fof(f769,plain,
    ( ! [X4,X3] :
        ( k9_relat_1(sK2,sK5(X3,sK0,X4)) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(X3,sK0,X4))
        | v5_pre_topc(X4,X3,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ v1_funct_1(X4)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_2
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f765,f100])).

fof(f765,plain,
    ( ! [X4,X3] :
        ( k9_relat_1(sK2,sK5(X3,sK0,X4)) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(X3,sK0,X4))
        | v5_pre_topc(X4,X3,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ v1_funct_1(X4)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl6_66 ),
    inference(resolution,[],[f761,f78])).

fof(f831,plain,
    ( ~ spl6_73
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_32
    | spl6_35
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f818,f569,f421,f373,f252,f173,f113,f108,f98,f93,f828])).

fof(f818,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_32
    | spl6_35
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f530,f570])).

fof(f530,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_32
    | spl6_35 ),
    inference(forward_demodulation,[],[f529,f374])).

fof(f529,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_32
    | spl6_35 ),
    inference(subsumption_resolution,[],[f528,f110])).

fof(f528,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_32
    | spl6_35 ),
    inference(subsumption_resolution,[],[f527,f115])).

fof(f527,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_32
    | spl6_35 ),
    inference(subsumption_resolution,[],[f526,f95])).

fof(f526,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_32
    | spl6_35 ),
    inference(subsumption_resolution,[],[f525,f100])).

fof(f525,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_32
    | spl6_35 ),
    inference(subsumption_resolution,[],[f524,f175])).

fof(f524,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_22
    | ~ spl6_32
    | spl6_35 ),
    inference(subsumption_resolution,[],[f523,f254])).

fof(f523,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_32
    | spl6_35 ),
    inference(subsumption_resolution,[],[f521,f423])).

fof(f521,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_32 ),
    inference(superposition,[],[f79,f374])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK5(X0,X1,X2))))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f774,plain,
    ( spl6_67
    | ~ spl6_2
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f766,f760,f98,f772])).

fof(f766,plain,
    ( ! [X0] :
        ( k9_relat_1(sK2,k2_pre_topc(sK0,X0)) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_2
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f763,f100])).

fof(f763,plain,
    ( ! [X0] :
        ( k9_relat_1(sK2,k2_pre_topc(sK0,X0)) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl6_66 ),
    inference(resolution,[],[f761,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f762,plain,
    ( spl6_66
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_20
    | ~ spl6_32
    | ~ spl6_64 ),
    inference(avatar_split_clause,[],[f758,f744,f373,f221,f161,f137,f123,f113,f98,f760])).

fof(f744,plain,
    ( spl6_64
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X2))
        | k2_struct_0(X2) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),sK2)
        | k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),sK2,X0) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),sK2),X0)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f758,plain,
    ( ! [X0] :
        ( k9_relat_1(sK2,X0) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_20
    | ~ spl6_32
    | ~ spl6_64 ),
    inference(forward_demodulation,[],[f757,f162])).

fof(f757,plain,
    ( ! [X0] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_32
    | ~ spl6_64 ),
    inference(forward_demodulation,[],[f756,f374])).

fof(f756,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) )
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f755,f115])).

fof(f755,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ l1_pre_topc(sK1) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f754,f100])).

fof(f754,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(sK1) )
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f753,f223])).

fof(f753,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(sK1) )
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f752,f125])).

fof(f752,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(sK1) )
    | ~ spl6_10
    | ~ spl6_64 ),
    inference(resolution,[],[f745,f139])).

fof(f745,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X2))
        | k2_struct_0(X2) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),sK2)
        | k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),sK2,X0) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),sK2),X0)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X2) )
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f744])).

fof(f746,plain,
    ( spl6_64
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f501,f132,f118,f744])).

fof(f501,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X2))
        | k2_struct_0(X2) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),sK2)
        | k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),sK2,X0) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),sK2),X0)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X2) )
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f500,f120])).

fof(f500,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_1(sK2)
        | k2_struct_0(X2) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),sK2)
        | k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),sK2,X0) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),sK2),X0)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X2) )
    | ~ spl6_9 ),
    inference(resolution,[],[f425,f134])).

fof(f425,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f344,f67])).

fof(f67,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f344,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X2)
      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f66,f67])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v2_funct_1(X2)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                   => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tops_2)).

fof(f662,plain,
    ( spl6_58
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_29
    | spl6_35
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f656,f569,f421,f357,f252,f173,f113,f108,f659])).

fof(f357,plain,
    ( spl6_29
  <=> ! [X1,X0] :
        ( v5_pre_topc(X0,X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | k2_pre_topc(sK1,k9_relat_1(sK2,sK5(X1,sK0,X0))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK5(X1,sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f656,plain,
    ( k2_pre_topc(sK1,k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_29
    | spl6_35
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f655,f570])).

fof(f655,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | k2_pre_topc(sK1,k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_29
    | spl6_35 ),
    inference(subsumption_resolution,[],[f363,f423])).

fof(f363,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | k2_pre_topc(sK1,k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f362,f110])).

fof(f362,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK1)
    | k2_pre_topc(sK1,k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f361,f115])).

fof(f361,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | k2_pre_topc(sK1,k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f360,f175])).

fof(f360,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | k2_pre_topc(sK1,k9_relat_1(sK2,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK5(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_22
    | ~ spl6_29 ),
    inference(resolution,[],[f358,f254])).

fof(f358,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | v5_pre_topc(X0,X1,sK0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | k2_pre_topc(sK1,k9_relat_1(sK2,sK5(X1,sK0,X0))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK5(X1,sK0,X0))) )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f357])).

fof(f580,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | spl6_48 ),
    inference(avatar_contradiction_clause,[],[f579])).

fof(f579,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | spl6_48 ),
    inference(subsumption_resolution,[],[f578,f120])).

fof(f578,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl6_7
    | ~ spl6_10
    | spl6_48 ),
    inference(subsumption_resolution,[],[f577,f125])).

fof(f577,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl6_10
    | spl6_48 ),
    inference(subsumption_resolution,[],[f575,f139])).

fof(f575,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | spl6_48 ),
    inference(resolution,[],[f571,f86])).

fof(f571,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | spl6_48 ),
    inference(avatar_component_clause,[],[f569])).

fof(f433,plain,
    ( spl6_28
    | ~ spl6_33 ),
    inference(avatar_contradiction_clause,[],[f432])).

fof(f432,plain,
    ( $false
    | spl6_28
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f431,f90])).

fof(f431,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,sK1,sK2))))
    | spl6_28
    | ~ spl6_33 ),
    inference(backward_demodulation,[],[f354,f385])).

fof(f385,plain,
    ( k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))) = k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,sK1,sK2)))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f383])).

fof(f383,plain,
    ( spl6_33
  <=> k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))) = k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f354,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))),k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,sK1,sK2))))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl6_28
  <=> r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))),k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f430,plain,
    ( spl6_36
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f402,f336,f161,f137,f123,f118,f113,f108,f103,f98,f93,f428])).

fof(f103,plain,
    ( spl6_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f402,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k9_relat_1(sK2,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_25 ),
    inference(forward_demodulation,[],[f401,f162])).

fof(f401,plain,
    ( ! [X0] :
        ( r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k9_relat_1(sK2,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_25 ),
    inference(forward_demodulation,[],[f400,f162])).

fof(f400,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0))) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f399,f95])).

fof(f399,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)))
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f398,f100])).

fof(f398,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f397,f105])).

fof(f105,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f397,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f396,f110])).

fof(f396,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)))
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f395,f115])).

fof(f395,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f394,f120])).

fof(f394,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f393,f125])).

fof(f393,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_10
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f391,f139])).

fof(f391,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_25 ),
    inference(resolution,[],[f338,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK4(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))))
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK4(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))))
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tops_2)).

fof(f338,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f336])).

fof(f424,plain,
    ( ~ spl6_35
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f419,f388,f336,f221,f143,f137,f128,f123,f113,f98,f421])).

fof(f388,plain,
    ( spl6_34
  <=> ! [X1,X0] :
        ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),X1,X0)
        | ~ v5_pre_topc(sK2,X0,X1)
        | v3_tops_2(sK2,X0,X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f419,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f418,f100])).

fof(f418,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f417,f115])).

fof(f417,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f416,f125])).

fof(f416,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f415,f145])).

fof(f415,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | spl6_8
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f414,f223])).

fof(f414,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | spl6_8
    | ~ spl6_10
    | ~ spl6_25
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f413,f129])).

fof(f129,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f413,plain,
    ( v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_10
    | ~ spl6_25
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f412,f338])).

fof(f412,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_10
    | ~ spl6_34 ),
    inference(resolution,[],[f389,f139])).

fof(f389,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(sK2,X0,X1)
        | v3_tops_2(sK2,X0,X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),X1,X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f388])).

fof(f390,plain,
    ( spl6_34
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f346,f132,f118,f388])).

fof(f346,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),X1,X0)
        | ~ v5_pre_topc(sK2,X0,X1)
        | v3_tops_2(sK2,X0,X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f345,f120])).

fof(f345,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),X1,X0)
        | ~ v5_pre_topc(sK2,X0,X1)
        | v3_tops_2(sK2,X0,X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_9 ),
    inference(resolution,[],[f73,f134])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v5_pre_topc(X2,X0,X1)
      | v3_tops_2(X2,X0,X1)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f386,plain,
    ( spl6_33
    | spl6_25
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f381,f369,f137,f123,f118,f113,f108,f103,f336,f383])).

fof(f369,plain,
    ( spl6_31
  <=> ! [X1,X0] :
        ( v5_pre_topc(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,X1,X0))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f381,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))) = k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,sK1,sK2)))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f380,f105])).

fof(f380,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))) = k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,sK1,sK2)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f379,f110])).

fof(f379,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))) = k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,sK1,sK2)))
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f378,f115])).

fof(f378,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))) = k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,sK1,sK2)))
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f377,f120])).

fof(f377,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))) = k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,sK1,sK2)))
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f376,f125])).

fof(f376,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))) = k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,sK1,sK2)))
    | ~ spl6_10
    | ~ spl6_31 ),
    inference(resolution,[],[f370,f139])).

fof(f370,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | v5_pre_topc(X0,sK0,X1)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,X1,X0))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,X1,X0))) )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f369])).

fof(f375,plain,
    ( spl6_32
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f262,f252,f373])).

fof(f262,plain,
    ( ! [X1] : k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1) = k10_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)
    | ~ spl6_22 ),
    inference(resolution,[],[f254,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f371,plain,
    ( spl6_31
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f258,f241,f98,f93,f369])).

fof(f241,plain,
    ( spl6_21
  <=> ! [X4] :
        ( k2_pre_topc(sK1,k9_relat_1(sK2,X4)) = k9_relat_1(sK2,k2_pre_topc(sK0,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f258,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,X1,X0))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,X1,X0))) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f257,f95])).

fof(f257,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(sK0)
        | k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,X1,X0))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,X1,X0))) )
    | ~ spl6_2
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f256,f100])).

fof(f256,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,X1,X0))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,X1,X0))) )
    | ~ spl6_21 ),
    inference(resolution,[],[f75,f242])).

fof(f242,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK1,k9_relat_1(sK2,X4)) = k9_relat_1(sK2,k2_pre_topc(sK0,X4)) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f241])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f359,plain,
    ( spl6_29
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f250,f241,f98,f93,f357])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X0,X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | k2_pre_topc(sK1,k9_relat_1(sK2,sK5(X1,sK0,X0))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK5(X1,sK0,X0))) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f249,f95])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X0,X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | k2_pre_topc(sK1,k9_relat_1(sK2,sK5(X1,sK0,X0))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK5(X1,sK0,X0))) )
    | ~ spl6_2
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f248,f100])).

fof(f248,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X0,X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | k2_pre_topc(sK1,k9_relat_1(sK2,sK5(X1,sK0,X0))) = k9_relat_1(sK2,k2_pre_topc(sK0,sK5(X1,sK0,X0))) )
    | ~ spl6_21 ),
    inference(resolution,[],[f78,f242])).

fof(f355,plain,
    ( spl6_25
    | ~ spl6_28
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f325,f161,f137,f123,f118,f113,f108,f103,f98,f93,f352,f336])).

fof(f325,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))),k2_pre_topc(sK1,k9_relat_1(sK2,sK4(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f324,f162])).

fof(f324,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f323,f95])).

fof(f323,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f322,f100])).

fof(f322,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f321,f105])).

fof(f321,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f320,f110])).

fof(f320,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f319,f115])).

fof(f319,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f318,f120])).

fof(f318,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f317,f125])).

fof(f317,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f315,f139])).

fof(f315,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK4(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_14 ),
    inference(superposition,[],[f76,f162])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK4(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f255,plain,
    ( spl6_22
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f247,f195,f137,f123,f252])).

fof(f195,plain,
    ( spl6_19
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | m1_subset_1(k2_tops_2(X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f247,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f246,f125])).

fof(f246,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl6_10
    | ~ spl6_19 ),
    inference(resolution,[],[f196,f139])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | m1_subset_1(k2_tops_2(X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f195])).

fof(f243,plain,
    ( spl6_21
    | spl6_8
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f239,f161,f128,f241])).

fof(f239,plain,
    ( ! [X4] :
        ( k2_pre_topc(sK1,k9_relat_1(sK2,X4)) = k9_relat_1(sK2,k2_pre_topc(sK0,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_8
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f233,f129])).

fof(f233,plain,
    ( ! [X4] :
        ( k2_pre_topc(sK1,k9_relat_1(sK2,X4)) = k9_relat_1(sK2,k2_pre_topc(sK0,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tops_2(sK2,sK0,sK1) )
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f232,f162])).

fof(f232,plain,
    ( ! [X4] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k9_relat_1(sK2,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tops_2(sK2,sK0,sK1) )
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f63,f162])).

fof(f63,plain,(
    ! [X4] :
      ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tops_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f236,plain,
    ( spl6_20
    | spl6_8 ),
    inference(avatar_split_clause,[],[f234,f128,f221])).

fof(f234,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f61,f129])).

fof(f61,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f226,plain,
    ( ~ spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12
    | spl6_18 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12
    | spl6_18 ),
    inference(subsumption_resolution,[],[f219,f192])).

fof(f192,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl6_18
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f219,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f151,f217])).

fof(f217,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f216,f100])).

fof(f216,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f215,f115])).

fof(f215,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f214,f120])).

fof(f214,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f213,f125])).

fof(f213,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f212,f130])).

fof(f212,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f69,f139])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_tops_2(X2,X0,X1)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f151,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl6_12
  <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f224,plain,
    ( spl6_20
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f217,f137,f128,f123,f118,f113,f98,f221])).

fof(f218,plain,
    ( spl6_11
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f211,f137,f128,f123,f118,f113,f98,f143])).

fof(f211,plain,
    ( k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f210,f100])).

fof(f210,plain,
    ( k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f209,f115])).

fof(f209,plain,
    ( k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f208,f120])).

fof(f208,plain,
    ( k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f201,f125])).

fof(f201,plain,
    ( k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f199,f130])).

fof(f199,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f68,f139])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_tops_2(X2,X0,X1)
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f197,plain,
    ( spl6_19
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f164,f118,f195])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | m1_subset_1(k2_tops_2(X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl6_6 ),
    inference(resolution,[],[f87,f120])).

fof(f193,plain,
    ( ~ spl6_11
    | spl6_17
    | ~ spl6_18
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f184,f149,f132,f128,f190,f186,f143])).

fof(f184,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f183,f151])).

fof(f183,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f182,f130])).

fof(f182,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f64,f134])).

fof(f64,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f176,plain,
    ( spl6_16
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f171,f166,f137,f123,f173])).

fof(f166,plain,
    ( spl6_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_funct_1(k2_tops_2(X0,X1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f171,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f170,f125])).

fof(f170,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(resolution,[],[f167,f139])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_funct_1(k2_tops_2(X0,X1,sK2)) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f166])).

fof(f168,plain,
    ( spl6_15
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f159,f118,f166])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_funct_1(k2_tops_2(X0,X1,sK2)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f85,f120])).

fof(f163,plain,
    ( spl6_14
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f158,f137,f161])).

fof(f158,plain,
    ( ! [X0] : k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl6_10 ),
    inference(resolution,[],[f89,f139])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f152,plain,
    ( spl6_12
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f147,f137,f149])).

fof(f147,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl6_10 ),
    inference(resolution,[],[f84,f139])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f146,plain,
    ( spl6_8
    | spl6_11 ),
    inference(avatar_split_clause,[],[f60,f143,f128])).

fof(f60,plain,
    ( k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f140,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f59,f137])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f135,plain,
    ( spl6_8
    | spl6_9 ),
    inference(avatar_split_clause,[],[f62,f132,f128])).

fof(f62,plain,
    ( v2_funct_1(sK2)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f126,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f58,f123])).

fof(f58,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f121,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f57,f118])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f116,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f56,f113])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f111,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f55,f108])).

fof(f55,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f106,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f54,f103])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f101,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f53,f98])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f96,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f52,f93])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

%------------------------------------------------------------------------------
