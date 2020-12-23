%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1334+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 4.66s
% Output     : Refutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :  285 ( 583 expanded)
%              Number of leaves         :   54 ( 217 expanded)
%              Depth                    :   19
%              Number of atoms          : 1085 (2128 expanded)
%              Number of equality atoms :   42 (  84 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5310,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f103,f108,f113,f118,f123,f131,f137,f146,f172,f176,f211,f222,f239,f293,f304,f309,f321,f491,f500,f1385,f1396,f1419,f1424,f1446,f1457,f1511,f1624,f1730,f3402,f3408,f3512,f3790,f5303,f5309])).

fof(f5309,plain,
    ( ~ spl5_8
    | ~ spl5_69
    | spl5_206 ),
    inference(avatar_contradiction_clause,[],[f5308])).

fof(f5308,plain,
    ( $false
    | ~ spl5_8
    | ~ spl5_69
    | spl5_206 ),
    inference(subsumption_resolution,[],[f5307,f136])).

fof(f136,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl5_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f5307,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_69
    | spl5_206 ),
    inference(subsumption_resolution,[],[f5306,f1456])).

fof(f1456,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,k9_relat_1(sK2,sK3)))
    | ~ spl5_69 ),
    inference(avatar_component_clause,[],[f1454])).

fof(f1454,plain,
    ( spl5_69
  <=> r1_tarski(sK3,k10_relat_1(sK2,k9_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f5306,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,k9_relat_1(sK2,sK3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl5_206 ),
    inference(superposition,[],[f5302,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f5302,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)))
    | spl5_206 ),
    inference(avatar_component_clause,[],[f5300])).

fof(f5300,plain,
    ( spl5_206
  <=> r1_tarski(sK3,k10_relat_1(sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_206])])).

fof(f5303,plain,
    ( ~ spl5_206
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_85 ),
    inference(avatar_split_clause,[],[f4669,f1727,f143,f139,f134,f128,f120,f115,f110,f105,f95,f5300])).

fof(f95,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f105,plain,
    ( spl5_3
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f110,plain,
    ( spl5_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f115,plain,
    ( spl5_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f120,plain,
    ( spl5_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f128,plain,
    ( spl5_7
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f139,plain,
    ( spl5_9
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f143,plain,
    ( spl5_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f1727,plain,
    ( spl5_85
  <=> r1_tarski(k2_pre_topc(sK0,sK3),k10_relat_1(sK2,k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f4669,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_85 ),
    inference(subsumption_resolution,[],[f4665,f199])).

fof(f199,plain,
    ( ! [X0] : m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f180,f136])).

fof(f180,plain,
    ( ! [X0] :
        ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )
    | ~ spl5_8 ),
    inference(superposition,[],[f85,f148])).

fof(f148,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
    | ~ spl5_8 ),
    inference(resolution,[],[f136,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f4665,plain,
    ( ~ m1_subset_1(k10_relat_1(sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK3,k10_relat_1(sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_85 ),
    inference(resolution,[],[f4664,f3826])).

fof(f3826,plain,
    ( ! [X0] : r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0))),k10_relat_1(sK2,k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0))))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(resolution,[],[f3807,f136])).

fof(f3807,plain,
    ( ! [X8,X7,X9] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,u1_struct_0(sK1))))
        | r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,k7_relset_1(X7,u1_struct_0(sK1),X8,X9))),k10_relat_1(sK2,k2_pre_topc(sK1,k7_relset_1(X7,u1_struct_0(sK1),X8,X9)))) )
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(resolution,[],[f3798,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f3798,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,X0)),k10_relat_1(sK2,k2_pre_topc(sK1,X0))) )
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f3797,f148])).

fof(f3797,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k10_relat_1(sK2,k2_pre_topc(sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f3796,f148])).

fof(f3796,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0))) )
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f3795,f107])).

fof(f107,plain,
    ( v2_pre_topc(sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f3795,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)))
        | ~ v2_pre_topc(sK1) )
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f3794,f136])).

fof(f3794,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)))
        | ~ v2_pre_topc(sK1) )
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f3793,f130])).

fof(f130,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f128])).

fof(f3793,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)))
        | ~ v2_pre_topc(sK1) )
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f3792,f97])).

fof(f97,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f3792,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)))
        | ~ v2_pre_topc(sK1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f3791,f112])).

fof(f112,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f3791,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)))
        | ~ v2_pre_topc(sK1) )
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(resolution,[],[f140,f226])).

fof(f226,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_pre_topc(X1,sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,X2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
        | ~ v2_pre_topc(X0) )
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f126,f122])).

fof(f122,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f126,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,X2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
        | ~ v5_pre_topc(X1,sK0,X0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f117,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_2)).

fof(f117,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f140,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f4664,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_pre_topc(sK0,X0),k10_relat_1(sK2,k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK3,X0) )
    | ~ spl5_6
    | ~ spl5_10
    | spl5_85 ),
    inference(subsumption_resolution,[],[f3440,f145])).

fof(f145,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f3440,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_pre_topc(sK0,X0),k10_relat_1(sK2,k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK3,X0) )
    | ~ spl5_6
    | spl5_85 ),
    inference(subsumption_resolution,[],[f1798,f122])).

fof(f1798,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_pre_topc(sK0,X0),k10_relat_1(sK2,k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK3,X0)
        | ~ l1_pre_topc(sK0) )
    | spl5_85 ),
    inference(resolution,[],[f1731,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f1731,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_pre_topc(sK0,sK3),X0)
        | ~ r1_tarski(X0,k10_relat_1(sK2,k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)))) )
    | spl5_85 ),
    inference(resolution,[],[f1729,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1729,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK3),k10_relat_1(sK2,k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))))
    | spl5_85 ),
    inference(avatar_component_clause,[],[f1727])).

fof(f3790,plain,
    ( ~ spl5_12
    | ~ spl5_67
    | spl5_142 ),
    inference(avatar_contradiction_clause,[],[f3789])).

fof(f3789,plain,
    ( $false
    | ~ spl5_12
    | ~ spl5_67
    | spl5_142 ),
    inference(subsumption_resolution,[],[f3788,f167])).

fof(f167,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl5_12
  <=> ! [X0] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f3788,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),sK4(sK0,sK1,sK2))
    | ~ spl5_67
    | spl5_142 ),
    inference(resolution,[],[f1439,f3513])).

fof(f3513,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK1))
        | ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),X0) )
    | spl5_142 ),
    inference(resolution,[],[f3511,f84])).

fof(f3511,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),u1_struct_0(sK1))
    | spl5_142 ),
    inference(avatar_component_clause,[],[f3509])).

fof(f3509,plain,
    ( spl5_142
  <=> r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f1439,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f1438])).

fof(f1438,plain,
    ( spl5_67
  <=> r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f3512,plain,
    ( ~ spl5_142
    | spl5_140 ),
    inference(avatar_split_clause,[],[f3403,f3395,f3509])).

fof(f3395,plain,
    ( spl5_140
  <=> m1_subset_1(k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).

fof(f3403,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),u1_struct_0(sK1))
    | spl5_140 ),
    inference(resolution,[],[f3397,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f3397,plain,
    ( ~ m1_subset_1(k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_140 ),
    inference(avatar_component_clause,[],[f3395])).

fof(f3408,plain,
    ( ~ spl5_8
    | spl5_9
    | spl5_141 ),
    inference(avatar_contradiction_clause,[],[f3407])).

fof(f3407,plain,
    ( $false
    | ~ spl5_8
    | spl5_9
    | spl5_141 ),
    inference(subsumption_resolution,[],[f3404,f199])).

fof(f3404,plain,
    ( ~ m1_subset_1(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8
    | spl5_9
    | spl5_141 ),
    inference(resolution,[],[f3401,f1498])).

fof(f1498,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k9_relat_1(sK2,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_8
    | spl5_9 ),
    inference(subsumption_resolution,[],[f1497,f136])).

fof(f1497,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k9_relat_1(sK2,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )
    | ~ spl5_8
    | spl5_9 ),
    inference(superposition,[],[f1465,f87])).

fof(f1465,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_8
    | spl5_9 ),
    inference(subsumption_resolution,[],[f1463,f136])).

fof(f1463,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )
    | spl5_9 ),
    inference(superposition,[],[f1461,f87])).

fof(f1461,plain,
    ( ! [X3] :
        ( r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_9 ),
    inference(subsumption_resolution,[],[f53,f141])).

fof(f141,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f53,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3)))
      | v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <~> ! [X3] :
                    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <~> ! [X3] :
                    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_2)).

fof(f3401,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),k2_pre_topc(sK1,k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))))
    | spl5_141 ),
    inference(avatar_component_clause,[],[f3399])).

fof(f3399,plain,
    ( spl5_141
  <=> r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),k2_pre_topc(sK1,k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_141])])).

fof(f3402,plain,
    ( ~ spl5_140
    | ~ spl5_141
    | ~ spl5_12
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f2032,f1383,f166,f3399,f3395])).

fof(f1383,plain,
    ( spl5_65
  <=> ! [X3] :
        ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),k2_pre_topc(sK1,X3))
        | ~ r1_tarski(X3,sK4(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f2032,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),k2_pre_topc(sK1,k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))))
    | ~ m1_subset_1(k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_12
    | ~ spl5_65 ),
    inference(resolution,[],[f1384,f167])).

fof(f1384,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,sK4(sK0,sK1,sK2))
        | ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),k2_pre_topc(sK1,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f1383])).

fof(f1730,plain,
    ( ~ spl5_85
    | ~ spl5_13
    | spl5_80 ),
    inference(avatar_split_clause,[],[f1630,f1621,f169,f1727])).

fof(f169,plain,
    ( spl5_13
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f1621,plain,
    ( spl5_80
  <=> r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK3)),k9_relat_1(sK2,k10_relat_1(sK2,k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f1630,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK3),k10_relat_1(sK2,k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))))
    | ~ spl5_13
    | spl5_80 ),
    inference(subsumption_resolution,[],[f1626,f170])).

fof(f170,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f169])).

fof(f1626,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK3),k10_relat_1(sK2,k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))))
    | ~ v1_relat_1(sK2)
    | spl5_80 ),
    inference(resolution,[],[f1623,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(f1623,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK3)),k9_relat_1(sK2,k10_relat_1(sK2,k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)))))
    | spl5_80 ),
    inference(avatar_component_clause,[],[f1621])).

fof(f1624,plain,
    ( ~ spl5_80
    | ~ spl5_12
    | spl5_68 ),
    inference(avatar_split_clause,[],[f1555,f1443,f166,f1621])).

fof(f1443,plain,
    ( spl5_68
  <=> r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f1555,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK3)),k9_relat_1(sK2,k10_relat_1(sK2,k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)))))
    | ~ spl5_12
    | spl5_68 ),
    inference(resolution,[],[f1449,f167])).

fof(f1449,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)))
        | ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK3)),X0) )
    | spl5_68 ),
    inference(resolution,[],[f1445,f84])).

fof(f1445,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)))
    | spl5_68 ),
    inference(avatar_component_clause,[],[f1443])).

fof(f1511,plain,
    ( ~ spl5_64
    | spl5_67 ),
    inference(avatar_contradiction_clause,[],[f1510])).

fof(f1510,plain,
    ( $false
    | ~ spl5_64
    | spl5_67 ),
    inference(subsumption_resolution,[],[f1448,f1380])).

fof(f1380,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f1379])).

fof(f1379,plain,
    ( spl5_64
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f1448,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_67 ),
    inference(resolution,[],[f1440,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1440,plain,
    ( ~ r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1))
    | spl5_67 ),
    inference(avatar_component_clause,[],[f1438])).

fof(f1457,plain,
    ( spl5_69
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1430,f219,f169,f151,f1454])).

fof(f151,plain,
    ( spl5_11
  <=> r1_tarski(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f219,plain,
    ( spl5_16
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f1430,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,k9_relat_1(sK2,sK3)))
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(resolution,[],[f152,f506])).

fof(f506,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) )
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f177,f221])).

fof(f221,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f219])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) )
    | ~ spl5_13 ),
    inference(resolution,[],[f170,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f152,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f1446,plain,
    ( ~ spl5_68
    | ~ spl5_8
    | spl5_66 ),
    inference(avatar_split_clause,[],[f1435,f1421,f134,f1443])).

fof(f1421,plain,
    ( spl5_66
  <=> r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f1435,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)))
    | ~ spl5_8
    | spl5_66 ),
    inference(subsumption_resolution,[],[f1433,f136])).

fof(f1433,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl5_66 ),
    inference(superposition,[],[f1423,f87])).

fof(f1423,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)))
    | spl5_66 ),
    inference(avatar_component_clause,[],[f1421])).

fof(f1424,plain,
    ( ~ spl5_66
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f1417,f139,f1421])).

fof(f1417,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)))
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f52,f140])).

fof(f52,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f1419,plain,
    ( ~ spl5_10
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f1418])).

fof(f1418,plain,
    ( $false
    | ~ spl5_10
    | spl5_11 ),
    inference(subsumption_resolution,[],[f156,f145])).

fof(f156,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_11 ),
    inference(resolution,[],[f153,f73])).

fof(f153,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK0))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f1396,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9
    | spl5_64 ),
    inference(avatar_contradiction_clause,[],[f1395])).

fof(f1395,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9
    | spl5_64 ),
    inference(subsumption_resolution,[],[f1394,f141])).

fof(f1394,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_64 ),
    inference(subsumption_resolution,[],[f1393,f117])).

fof(f1393,plain,
    ( ~ v2_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_64 ),
    inference(subsumption_resolution,[],[f1392,f136])).

fof(f1392,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | spl5_64 ),
    inference(subsumption_resolution,[],[f1391,f130])).

fof(f1391,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | spl5_64 ),
    inference(subsumption_resolution,[],[f1390,f97])).

fof(f1390,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | spl5_64 ),
    inference(subsumption_resolution,[],[f1389,f112])).

fof(f1389,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_3
    | ~ spl5_6
    | spl5_64 ),
    inference(subsumption_resolution,[],[f1388,f107])).

fof(f1388,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_6
    | spl5_64 ),
    inference(subsumption_resolution,[],[f1386,f122])).

fof(f1386,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | spl5_64 ),
    inference(resolution,[],[f1381,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1381,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_64 ),
    inference(avatar_component_clause,[],[f1379])).

fof(f1385,plain,
    ( ~ spl5_64
    | spl5_65
    | ~ spl5_4
    | spl5_24 ),
    inference(avatar_split_clause,[],[f366,f318,f110,f1383,f1379])).

fof(f318,plain,
    ( spl5_24
  <=> r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),k2_pre_topc(sK1,sK4(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f366,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),k2_pre_topc(sK1,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X3,sK4(sK0,sK1,sK2)) )
    | ~ spl5_4
    | spl5_24 ),
    inference(subsumption_resolution,[],[f364,f112])).

fof(f364,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),k2_pre_topc(sK1,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X3,sK4(sK0,sK1,sK2))
        | ~ l1_pre_topc(sK1) )
    | spl5_24 ),
    inference(resolution,[],[f322,f64])).

fof(f322,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))
        | ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),X0) )
    | spl5_24 ),
    inference(resolution,[],[f320,f84])).

fof(f320,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f318])).

fof(f500,plain,
    ( ~ spl5_4
    | spl5_34 ),
    inference(avatar_contradiction_clause,[],[f499])).

fof(f499,plain,
    ( $false
    | ~ spl5_4
    | spl5_34 ),
    inference(subsumption_resolution,[],[f498,f112])).

fof(f498,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_34 ),
    inference(resolution,[],[f490,f63])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f490,plain,
    ( ~ l1_struct_0(sK1)
    | spl5_34 ),
    inference(avatar_component_clause,[],[f488])).

fof(f488,plain,
    ( spl5_34
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f491,plain,
    ( ~ spl5_34
    | spl5_2
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f486,f208,f100,f488])).

fof(f100,plain,
    ( spl5_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f208,plain,
    ( spl5_15
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f486,plain,
    ( ~ l1_struct_0(sK1)
    | spl5_2
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f485,f102])).

fof(f102,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f485,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f475,f62])).

fof(f62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f475,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_15 ),
    inference(superposition,[],[f65,f210])).

fof(f210,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f208])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f321,plain,
    ( ~ spl5_24
    | ~ spl5_13
    | spl5_22 ),
    inference(avatar_split_clause,[],[f299,f290,f169,f318])).

fof(f290,plain,
    ( spl5_22
  <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))))),k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f299,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))
    | ~ spl5_13
    | spl5_22 ),
    inference(subsumption_resolution,[],[f296,f170])).

fof(f296,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))
    | ~ v1_relat_1(sK2)
    | spl5_22 ),
    inference(resolution,[],[f292,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f292,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))))),k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f290])).

fof(f309,plain,
    ( ~ spl5_6
    | ~ spl5_8
    | spl5_23 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_8
    | spl5_23 ),
    inference(subsumption_resolution,[],[f307,f122])).

fof(f307,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_8
    | spl5_23 ),
    inference(subsumption_resolution,[],[f305,f199])).

fof(f305,plain,
    ( ~ m1_subset_1(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_23 ),
    inference(resolution,[],[f303,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f303,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_23 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl5_23
  <=> m1_subset_1(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f304,plain,
    ( ~ spl5_23
    | spl5_21 ),
    inference(avatar_split_clause,[],[f295,f286,f301])).

fof(f286,plain,
    ( spl5_21
  <=> r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f295,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_21 ),
    inference(resolution,[],[f288,f73])).

fof(f288,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),u1_struct_0(sK0))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f286])).

fof(f293,plain,
    ( ~ spl5_21
    | ~ spl5_22
    | ~ spl5_13
    | ~ spl5_16
    | spl5_17 ),
    inference(avatar_split_clause,[],[f258,f236,f219,f169,f290,f286])).

fof(f236,plain,
    ( spl5_17
  <=> r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f258,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))))),k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),u1_struct_0(sK0))
    | ~ spl5_13
    | ~ spl5_16
    | spl5_17 ),
    inference(resolution,[],[f243,f227])).

fof(f227,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f177,f221])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),X0)
        | ~ r1_tarski(X0,k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))) )
    | spl5_17 ),
    inference(resolution,[],[f238,f84])).

fof(f238,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f236])).

fof(f239,plain,
    ( ~ spl5_17
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f189,f139,f134,f128,f120,f115,f110,f105,f95,f236])).

fof(f189,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(forward_demodulation,[],[f188,f148])).

fof(f188,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(subsumption_resolution,[],[f187,f141])).

fof(f187,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f186,f117])).

fof(f186,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f185,f136])).

fof(f185,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f184,f130])).

fof(f184,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f183,f97])).

fof(f183,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f182,f112])).

fof(f182,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f181,f107])).

fof(f181,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f178,f122])).

fof(f178,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_8 ),
    inference(superposition,[],[f68,f148])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK4(X0,X1,X2))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f222,plain,
    ( spl5_16
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f214,f204,f134,f219])).

fof(f204,plain,
    ( spl5_14
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f214,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f212,f136])).

fof(f212,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_14 ),
    inference(superposition,[],[f206,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f206,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f204])).

fof(f211,plain,
    ( spl5_14
    | spl5_15
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f200,f134,f128,f208,f204])).

fof(f200,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f132,f136])).

fof(f132,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_7 ),
    inference(resolution,[],[f130,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f176,plain,
    ( ~ spl5_8
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl5_8
    | spl5_13 ),
    inference(resolution,[],[f173,f136])).

fof(f173,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_13 ),
    inference(resolution,[],[f171,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f171,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f169])).

fof(f172,plain,
    ( spl5_12
    | ~ spl5_13
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f124,f95,f169,f166])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f97,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f146,plain,
    ( ~ spl5_9
    | spl5_10 ),
    inference(avatar_split_clause,[],[f51,f143,f139])).

fof(f51,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f137,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f56,f134])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f23])).

fof(f131,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f55,f128])).

fof(f55,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f123,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f61,f120])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f118,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f60,f115])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f113,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f59,f110])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f108,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f58,f105])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f103,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f57,f100])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f98,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f54,f95])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------
