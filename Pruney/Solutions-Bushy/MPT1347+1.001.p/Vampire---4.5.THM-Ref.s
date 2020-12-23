%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1347+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:47 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  390 (1336 expanded)
%              Number of leaves         :   71 ( 557 expanded)
%              Depth                    :   23
%              Number of atoms          : 2133 (8650 expanded)
%              Number of equality atoms :  212 (1139 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1542,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f123,f128,f133,f142,f152,f165,f173,f178,f190,f195,f199,f216,f221,f234,f268,f294,f320,f331,f340,f388,f410,f456,f462,f477,f479,f484,f486,f487,f492,f498,f517,f539,f545,f698,f709,f725,f748,f932,f1165,f1166,f1239,f1255,f1266,f1324,f1328,f1329,f1395,f1400,f1419,f1538,f1541])).

fof(f1541,plain,
    ( ~ spl5_3
    | ~ spl5_15
    | ~ spl5_25
    | ~ spl5_63
    | ~ spl5_67
    | spl5_70 ),
    inference(avatar_contradiction_clause,[],[f1540])).

fof(f1540,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_15
    | ~ spl5_25
    | ~ spl5_63
    | ~ spl5_67
    | spl5_70 ),
    inference(subsumption_resolution,[],[f1539,f1394])).

fof(f1394,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f1392])).

fof(f1392,plain,
    ( spl5_63
  <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f1539,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ spl5_3
    | ~ spl5_15
    | ~ spl5_25
    | ~ spl5_67
    | spl5_70 ),
    inference(forward_demodulation,[],[f1537,f1420])).

fof(f1420,plain,
    ( sK4(sK0,sK1,sK2) = k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))
    | ~ spl5_3
    | ~ spl5_15
    | ~ spl5_25
    | ~ spl5_67 ),
    inference(unit_resulting_resolution,[],[f1418,f815])).

fof(f815,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK1))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl5_3
    | ~ spl5_15
    | ~ spl5_25 ),
    inference(superposition,[],[f315,f418])).

fof(f418,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl5_25
  <=> u1_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f315,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl5_3
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f311,f127])).

fof(f127,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f311,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl5_15 ),
    inference(resolution,[],[f220,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f220,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl5_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f1418,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f1416])).

fof(f1416,plain,
    ( spl5_67
  <=> r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f1537,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),sK1)
    | spl5_70 ),
    inference(avatar_component_clause,[],[f1535])).

fof(f1535,plain,
    ( spl5_70
  <=> v4_pre_topc(k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f1538,plain,
    ( ~ spl5_70
    | ~ spl5_7
    | ~ spl5_13
    | spl5_64 ),
    inference(avatar_split_clause,[],[f1406,f1397,f197,f149,f1535])).

fof(f149,plain,
    ( spl5_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f197,plain,
    ( spl5_13
  <=> ! [X4] :
        ( v4_pre_topc(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f1397,plain,
    ( spl5_64
  <=> v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f1406,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),sK1)
    | ~ spl5_7
    | ~ spl5_13
    | spl5_64 ),
    inference(unit_resulting_resolution,[],[f527,f1399,f1203])).

fof(f1203,plain,
    ( ! [X4] :
        ( ~ v4_pre_topc(k9_relat_1(sK2,X4),sK1)
        | v4_pre_topc(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f198,f206])).

fof(f206,plain,
    ( ! [X0] : k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f151,f110])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f151,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f149])).

fof(f198,plain,
    ( ! [X4] :
        ( v4_pre_topc(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK1) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f197])).

fof(f1399,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | spl5_64 ),
    inference(avatar_component_clause,[],[f1397])).

fof(f527,plain,
    ( ! [X0] : m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_7 ),
    inference(superposition,[],[f200,f209])).

fof(f209,plain,
    ( ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f151,f111])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f200,plain,
    ( ! [X0] : m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f151,f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f1419,plain,
    ( spl5_67
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | spl5_19 ),
    inference(avatar_split_clause,[],[f1357,f317,f149,f130,f125,f120,f115,f1416])).

fof(f115,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f120,plain,
    ( spl5_2
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f130,plain,
    ( spl5_4
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f317,plain,
    ( spl5_19
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f1357,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | spl5_19 ),
    inference(subsumption_resolution,[],[f1332,f318])).

fof(f318,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl5_19 ),
    inference(avatar_component_clause,[],[f317])).

fof(f1332,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1331,f117])).

fof(f117,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f1331,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1330,f122])).

fof(f122,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f1330,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f933,f151])).

fof(f933,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f642,f132])).

fof(f132,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f642,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | v5_pre_topc(sK2,X0,X1)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | r1_tarski(sK4(X0,X1,sK2),u1_struct_0(X1)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f244,f127])).

fof(f244,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | v5_pre_topc(X0,X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | r1_tarski(sK4(X1,X2,X0),u1_struct_0(X2)) ) ),
    inference(resolution,[],[f89,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
        & v4_pre_topc(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

fof(f1400,plain,
    ( ~ spl5_64
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | spl5_19 ),
    inference(avatar_split_clause,[],[f1355,f317,f149,f130,f125,f120,f115,f1397])).

fof(f1355,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | spl5_19 ),
    inference(subsumption_resolution,[],[f1344,f318])).

fof(f1344,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1343,f117])).

fof(f1343,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1342,f122])).

fof(f1342,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1341,f127])).

fof(f1341,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1340,f132])).

fof(f1340,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f528,f151])).

fof(f528,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_7 ),
    inference(superposition,[],[f91,f209])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1395,plain,
    ( spl5_63
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | spl5_19 ),
    inference(avatar_split_clause,[],[f1356,f317,f149,f130,f125,f120,f115,f1392])).

fof(f1356,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | spl5_19 ),
    inference(subsumption_resolution,[],[f1339,f318])).

fof(f1339,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1338,f117])).

fof(f1338,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1337,f122])).

fof(f1337,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f619,f151])).

fof(f619,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f243,f132])).

fof(f243,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | v4_pre_topc(sK4(X0,X1,sK2),X1)
        | v5_pre_topc(sK2,X0,X1)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f90,f127])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | v4_pre_topc(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1329,plain,
    ( k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1328,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_15
    | ~ spl5_29
    | spl5_33
    | ~ spl5_37
    | ~ spl5_39
    | ~ spl5_42
    | ~ spl5_62 ),
    inference(avatar_contradiction_clause,[],[f1327])).

fof(f1327,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_15
    | ~ spl5_29
    | spl5_33
    | ~ spl5_37
    | ~ spl5_39
    | ~ spl5_42
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f1326,f1265])).

fof(f1265,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_15
    | ~ spl5_29
    | spl5_33
    | ~ spl5_37
    | ~ spl5_39
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f1264,f412])).

fof(f412,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f220,f127,f141,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f141,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl5_6
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1264,plain,
    ( ~ v4_pre_topc(k10_relat_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_29
    | spl5_33
    | ~ spl5_37
    | ~ spl5_39
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f1257,f765])).

fof(f765,plain,
    ( ! [X3] : k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),X3) = k10_relat_1(k2_funct_1(sK2),X3)
    | ~ spl5_42 ),
    inference(resolution,[],[f747,f211])).

fof(f211,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r1_tarski(X3,k2_zfmisc_1(X1,X2))
      | k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    inference(resolution,[],[f111,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f747,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f745])).

fof(f745,plain,
    ( spl5_42
  <=> r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f1257,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_29
    | spl5_33
    | ~ spl5_37
    | ~ spl5_39 ),
    inference(unit_resulting_resolution,[],[f122,f117,f461,f697,f544,f496,f91])).

fof(f496,plain,
    ( ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | spl5_33 ),
    inference(avatar_component_clause,[],[f495])).

fof(f495,plain,
    ( spl5_33
  <=> v5_pre_topc(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f544,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f542])).

fof(f542,plain,
    ( spl5_37
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f697,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f695])).

fof(f695,plain,
    ( spl5_39
  <=> v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f461,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl5_29
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f1326,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_29
    | spl5_33
    | ~ spl5_37
    | ~ spl5_39
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f1325,f1258])).

fof(f1258,plain,
    ( m1_subset_1(sK4(sK1,sK0,k2_funct_1(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_29
    | spl5_33
    | ~ spl5_37
    | ~ spl5_39 ),
    inference(unit_resulting_resolution,[],[f122,f117,f461,f697,f544,f496,f89])).

fof(f1325,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,k2_funct_1(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k9_relat_1(sK2,sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_62 ),
    inference(resolution,[],[f1323,f1204])).

fof(f1204,plain,
    ( ! [X4] :
        ( ~ v4_pre_topc(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(k9_relat_1(sK2,X4),sK1) )
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f189,f206])).

fof(f189,plain,
    ( ! [X4] :
        ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X4,sK0) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl5_11
  <=> ! [X4] :
        ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X4,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f1323,plain,
    ( v4_pre_topc(sK4(sK1,sK0,k2_funct_1(sK2)),sK0)
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f1321])).

fof(f1321,plain,
    ( spl5_62
  <=> v4_pre_topc(sK4(sK1,sK0,k2_funct_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f1324,plain,
    ( spl5_62
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_23
    | ~ spl5_29
    | ~ spl5_37
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f1237,f695,f542,f459,f342,f337,f328,f317,f192,f149,f139,f135,f130,f125,f120,f115,f1321])).

fof(f135,plain,
    ( spl5_5
  <=> v3_tops_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f192,plain,
    ( spl5_12
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f328,plain,
    ( spl5_20
  <=> u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f337,plain,
    ( spl5_22
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f342,plain,
    ( spl5_23
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f1237,plain,
    ( v4_pre_topc(sK4(sK1,sK0,k2_funct_1(sK2)),sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_23
    | ~ spl5_29
    | ~ spl5_37
    | ~ spl5_39 ),
    inference(subsumption_resolution,[],[f1236,f122])).

fof(f1236,plain,
    ( v4_pre_topc(sK4(sK1,sK0,k2_funct_1(sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_23
    | ~ spl5_29
    | ~ spl5_37
    | ~ spl5_39 ),
    inference(subsumption_resolution,[],[f1235,f117])).

fof(f1235,plain,
    ( v4_pre_topc(sK4(sK1,sK0,k2_funct_1(sK2)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_23
    | ~ spl5_29
    | ~ spl5_37
    | ~ spl5_39 ),
    inference(subsumption_resolution,[],[f1234,f1229])).

fof(f1229,plain,
    ( ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f1228,f344])).

fof(f344,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f342])).

fof(f1228,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f1212,f339])).

fof(f339,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f337])).

fof(f1212,plain,
    ( ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f1211,f1210])).

fof(f1210,plain,
    ( k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f1209,f127])).

fof(f1209,plain,
    ( k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f1208,f132])).

fof(f1208,plain,
    ( k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f1207,f151])).

fof(f1207,plain,
    ( k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl5_6
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f348,f141])).

fof(f348,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl5_20 ),
    inference(trivial_inequality_removal,[],[f347])).

fof(f347,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl5_20 ),
    inference(superposition,[],[f107,f330])).

fof(f330,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f328])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f1211,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f1192,f136])).

fof(f136,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f1192,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f1191,f117])).

fof(f1191,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f1190,f122])).

fof(f1190,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f1189,f127])).

fof(f1189,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f1188,f132])).

fof(f1188,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f1187,f151])).

fof(f1187,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f350,f141])).

fof(f350,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v2_funct_1(sK2)
    | v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f349,f319])).

fof(f319,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f317])).

fof(f349,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_funct_1(sK2)
    | v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_12
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f346,f298])).

fof(f298,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f194,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f194,plain,
    ( l1_struct_0(sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f192])).

fof(f346,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_funct_1(sK2)
    | v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_20 ),
    inference(superposition,[],[f87,f330])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v2_funct_1(X2)
      | v3_tops_2(X2,X0,X1)
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).

fof(f1234,plain,
    ( v4_pre_topc(sK4(sK1,sK0,k2_funct_1(sK2)),sK0)
    | v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl5_29
    | ~ spl5_37
    | ~ spl5_39 ),
    inference(subsumption_resolution,[],[f934,f544])).

fof(f934,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v4_pre_topc(sK4(sK1,sK0,k2_funct_1(sK2)),sK0)
    | v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl5_29
    | ~ spl5_39 ),
    inference(resolution,[],[f468,f697])).

fof(f468,plain,
    ( ! [X12,X11] :
        ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(X11),u1_struct_0(X12))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12))))
        | v4_pre_topc(sK4(X11,X12,k2_funct_1(sK2)),X12)
        | v5_pre_topc(k2_funct_1(sK2),X11,X12)
        | ~ l1_pre_topc(X12)
        | ~ l1_pre_topc(X11) )
    | ~ spl5_29 ),
    inference(resolution,[],[f461,f90])).

fof(f1266,plain,
    ( spl5_34
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f1210,f328,f149,f139,f130,f125,f500])).

fof(f500,plain,
    ( spl5_34
  <=> k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f1255,plain,
    ( ~ spl5_33
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f1229,f342,f337,f328,f317,f192,f149,f139,f135,f130,f125,f120,f115,f495])).

fof(f1239,plain,
    ( ~ spl5_18
    | ~ spl5_7
    | spl5_17 ),
    inference(avatar_split_clause,[],[f1200,f230,f149,f301])).

fof(f301,plain,
    ( spl5_18
  <=> v4_pre_topc(k9_relat_1(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f230,plain,
    ( spl5_17
  <=> v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f1200,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK3),sK1)
    | ~ spl5_7
    | spl5_17 ),
    inference(forward_demodulation,[],[f231,f206])).

fof(f231,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f230])).

fof(f1166,plain,
    ( sK3 != k10_relat_1(sK2,k9_relat_1(sK2,sK3))
    | v4_pre_topc(sK3,sK0)
    | ~ v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK3)),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1165,plain,
    ( spl5_60
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_15
    | ~ spl5_24
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f1130,f421,f385,f218,f149,f135,f130,f125,f120,f115,f1162])).

fof(f1162,plain,
    ( spl5_60
  <=> sK3 = k10_relat_1(sK2,k9_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f385,plain,
    ( spl5_24
  <=> r1_tarski(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f421,plain,
    ( spl5_26
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f1130,plain,
    ( sK3 = k10_relat_1(sK2,k9_relat_1(sK2,sK3))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_15
    | ~ spl5_24
    | ~ spl5_26 ),
    inference(unit_resulting_resolution,[],[f387,f810])).

fof(f810,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_15
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f809,f422])).

fof(f422,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f421])).

fof(f809,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f806,f394])).

fof(f394,plain,
    ( ! [X2] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X2)),X2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f393,f127])).

fof(f393,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK2)
        | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X2)),X2) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f313,f379])).

fof(f379,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f117,f122,f127,f132,f151,f137,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f137,plain,
    ( v3_tops_2(sK2,sK0,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f313,plain,
    ( ! [X2] :
        ( ~ v2_funct_1(sK2)
        | ~ v1_funct_1(sK2)
        | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X2)),X2) )
    | ~ spl5_15 ),
    inference(resolution,[],[f220,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f806,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl5_15 ),
    inference(resolution,[],[f314,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f314,plain,
    ( ! [X3] :
        ( r1_tarski(X3,k10_relat_1(sK2,k9_relat_1(sK2,X3)))
        | ~ r1_tarski(X3,k1_relat_1(sK2)) )
    | ~ spl5_15 ),
    inference(resolution,[],[f220,f92])).

fof(f92,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f387,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f385])).

fof(f932,plain,
    ( spl5_54
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f732,f317,f301,f149,f130,f125,f120,f115,f929])).

fof(f929,plain,
    ( spl5_54
  <=> v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f732,plain,
    ( v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK3)),sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f731,f209])).

fof(f731,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k9_relat_1(sK2,sK3)),sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f117,f122,f127,f319,f132,f151,f526,f302,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f302,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK3),sK1)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f301])).

fof(f526,plain,
    ( ! [X0] : m1_subset_1(k9_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_7 ),
    inference(superposition,[],[f203,f206])).

fof(f203,plain,
    ( ! [X0] : m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f151,f109])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f748,plain,
    ( spl5_42
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f555,f542,f745])).

fof(f555,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl5_37 ),
    inference(unit_resulting_resolution,[],[f544,f99])).

fof(f725,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_16
    | spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_22
    | ~ spl5_23 ),
    inference(avatar_contradiction_clause,[],[f724])).

fof(f724,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_16
    | spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_22
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f227,f720])).

fof(f720,plain,
    ( v4_pre_topc(sK3,sK0)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_22
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f719,f344])).

fof(f719,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | v4_pre_topc(sK3,sK0)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f718,f339])).

fof(f718,plain,
    ( v4_pre_topc(sK3,sK0)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_18
    | ~ spl5_20
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f717,f335])).

fof(f335,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl5_21
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f717,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | v4_pre_topc(sK3,sK0)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_18
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f716,f330])).

fof(f716,plain,
    ( v4_pre_topc(sK3,sK0)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_18 ),
    inference(subsumption_resolution,[],[f715,f303])).

fof(f303,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK3),sK1)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f301])).

fof(f715,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK3),sK1)
    | v4_pre_topc(sK3,sK0)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f714,f206])).

fof(f714,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | v4_pre_topc(sK3,sK0)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f713,f137])).

fof(f713,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | v4_pre_topc(sK3,sK0)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f78,f141])).

fof(f78,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | v4_pre_topc(sK3,sK0)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
          | ~ v4_pre_topc(sK3,sK0) )
        & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
          | v4_pre_topc(sK3,sK0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_funct_1(sK2)
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      | ~ v3_tops_2(sK2,sK0,sK1) )
    & ( ( ! [X4] :
            ( ( ( v4_pre_topc(X4,sK0)
                | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK1) )
              & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK1)
                | ~ v4_pre_topc(X4,sK0) ) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        & v2_funct_1(sK2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) )
      | v3_tops_2(sK2,sK0,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f52,f56,f55,f54,f53])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | ~ v4_pre_topc(X3,X0) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | v4_pre_topc(X3,X0) )
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ v3_tops_2(X2,X0,X1) )
                & ( ( ! [X4] :
                        ( ( ( v4_pre_topc(X4,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                            | ~ v4_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | v3_tops_2(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1)
                      | ~ v4_pre_topc(X3,sK0) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1)
                      | v4_pre_topc(X3,sK0) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                | ~ v3_tops_2(X2,sK0,X1) )
              & ( ( ! [X4] :
                      ( ( ( v4_pre_topc(X4,sK0)
                          | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X4),X1) )
                        & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X4),X1)
                          | ~ v4_pre_topc(X4,sK0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                  & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) )
                | v3_tops_2(X2,sK0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1)
                    | ~ v4_pre_topc(X3,sK0) )
                  & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1)
                    | v4_pre_topc(X3,sK0) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              | ~ v3_tops_2(X2,sK0,X1) )
            & ( ( ! [X4] :
                    ( ( ( v4_pre_topc(X4,sK0)
                        | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X4),X1) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X4),X1)
                        | ~ v4_pre_topc(X4,sK0) ) )
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                & v2_funct_1(X2)
                & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) )
              | v3_tops_2(X2,sK0,X1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK1)
                  | ~ v4_pre_topc(X3,sK0) )
                & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK1)
                  | v4_pre_topc(X3,sK0) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v2_funct_1(X2)
            | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) != k2_struct_0(sK1)
            | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
            | ~ v3_tops_2(X2,sK0,sK1) )
          & ( ( ! [X4] :
                  ( ( ( v4_pre_topc(X4,sK0)
                      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X4),sK1) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X4),sK1)
                      | ~ v4_pre_topc(X4,sK0) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
              & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) )
            | v3_tops_2(X2,sK0,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK1)
                | ~ v4_pre_topc(X3,sK0) )
              & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK1)
                | v4_pre_topc(X3,sK0) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ v2_funct_1(X2)
          | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) != k2_struct_0(sK1)
          | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
          | ~ v3_tops_2(X2,sK0,sK1) )
        & ( ( ! [X4] :
                ( ( ( v4_pre_topc(X4,sK0)
                    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X4),sK1) )
                  & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X4),sK1)
                    | ~ v4_pre_topc(X4,sK0) ) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) )
          | v3_tops_2(X2,sK0,sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( ? [X3] :
            ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK1)
              | ~ v4_pre_topc(X3,sK0) )
            & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK1)
              | v4_pre_topc(X3,sK0) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ v2_funct_1(sK2)
        | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        | ~ v3_tops_2(sK2,sK0,sK1) )
      & ( ( ! [X4] :
              ( ( ( v4_pre_topc(X4,sK0)
                  | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK1) )
                & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK1)
                  | ~ v4_pre_topc(X4,sK0) ) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          & v2_funct_1(sK2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
          & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) )
        | v3_tops_2(sK2,sK0,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X3] :
        ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK1)
          | ~ v4_pre_topc(X3,sK0) )
        & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK1)
          | v4_pre_topc(X3,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
        | ~ v4_pre_topc(sK3,sK0) )
      & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
        | v4_pre_topc(sK3,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | v4_pre_topc(X3,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X4] :
                      ( ( ( v4_pre_topc(X4,X0)
                          | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                        & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                          | ~ v4_pre_topc(X4,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | v4_pre_topc(X3,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( ( ( v4_pre_topc(X3,X0)
                          | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                        & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                          | ~ v4_pre_topc(X3,X0) ) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | v4_pre_topc(X3,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( ( ( v4_pre_topc(X3,X0)
                          | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                        & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                          | ~ v4_pre_topc(X3,X0) ) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_tops_2(X2,X0,X1)
                <=> ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( v4_pre_topc(X3,X0)
                        <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_tops_2(X2,X0,X1)
                <=> ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( v4_pre_topc(X3,X0)
                        <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_2)).

fof(f227,plain,
    ( ~ v4_pre_topc(sK3,sK0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl5_16
  <=> v4_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f709,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16
    | spl5_18
    | ~ spl5_29
    | ~ spl5_33
    | ~ spl5_37
    | ~ spl5_39 ),
    inference(avatar_contradiction_clause,[],[f708])).

fof(f708,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16
    | spl5_18
    | ~ spl5_29
    | ~ spl5_33
    | ~ spl5_37
    | ~ spl5_39 ),
    inference(subsumption_resolution,[],[f707,f303])).

fof(f707,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK3),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_29
    | ~ spl5_33
    | ~ spl5_37
    | ~ spl5_39 ),
    inference(forward_demodulation,[],[f703,f564])).

fof(f564,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),X0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_15
    | ~ spl5_37 ),
    inference(forward_demodulation,[],[f554,f396])).

fof(f396,plain,
    ( ! [X1] : k9_relat_1(sK2,X1) = k10_relat_1(k2_funct_1(sK2),X1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f395,f127])).

fof(f395,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK2)
        | k9_relat_1(sK2,X1) = k10_relat_1(k2_funct_1(sK2),X1) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f312,f379])).

fof(f312,plain,
    ( ! [X1] :
        ( ~ v2_funct_1(sK2)
        | ~ v1_funct_1(sK2)
        | k9_relat_1(sK2,X1) = k10_relat_1(k2_funct_1(sK2),X1) )
    | ~ spl5_15 ),
    inference(resolution,[],[f220,f94])).

fof(f554,plain,
    ( ! [X0] : k10_relat_1(k2_funct_1(sK2),X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),X0)
    | ~ spl5_37 ),
    inference(unit_resulting_resolution,[],[f544,f111])).

fof(f703,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),sK3),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_29
    | ~ spl5_33
    | ~ spl5_37
    | ~ spl5_39 ),
    inference(unit_resulting_resolution,[],[f122,f117,f228,f461,f215,f497,f544,f697,f88])).

fof(f497,plain,
    ( v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f495])).

fof(f215,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl5_14
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f228,plain,
    ( v4_pre_topc(sK3,sK0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f226])).

fof(f698,plain,
    ( spl5_39
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f508,f500,f149,f130,f125,f695])).

fof(f508,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f507,f127])).

fof(f507,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f506,f132])).

fof(f506,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl5_7
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f505,f151])).

fof(f505,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl5_34 ),
    inference(superposition,[],[f105,f502])).

fof(f502,plain,
    ( k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f500])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f545,plain,
    ( spl5_37
    | ~ spl5_34
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f540,f536,f500,f542])).

fof(f536,plain,
    ( spl5_36
  <=> m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f540,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_34
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f538,f502])).

fof(f538,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f536])).

fof(f539,plain,
    ( spl5_36
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f235,f149,f130,f125,f536])).

fof(f235,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f127,f132,f151,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f517,plain,
    ( spl5_21
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f298,f192,f333])).

fof(f498,plain,
    ( spl5_33
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_20
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f493,f489,f328,f149,f135,f130,f125,f120,f115,f495])).

fof(f489,plain,
    ( spl5_32
  <=> v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f493,plain,
    ( v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_20
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f491,f392])).

fof(f392,plain,
    ( k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f391,f127])).

fof(f391,plain,
    ( k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f390,f132])).

fof(f390,plain,
    ( k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f389,f151])).

fof(f389,plain,
    ( k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f348,f379])).

fof(f491,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f489])).

fof(f492,plain,
    ( spl5_32
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f375,f149,f135,f130,f125,f120,f115,f489])).

fof(f375,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f117,f122,f127,f132,f151,f137,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f487,plain,
    ( spl5_23
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f239,f170,f342])).

fof(f170,plain,
    ( spl5_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f239,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f172,f80])).

fof(f172,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f170])).

fof(f486,plain,
    ( spl5_25
    | ~ spl5_20
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f485,f481,f328,f417])).

fof(f481,plain,
    ( spl5_31
  <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f485,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl5_20
    | ~ spl5_31 ),
    inference(forward_demodulation,[],[f483,f330])).

fof(f483,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f481])).

fof(f484,plain,
    ( spl5_31
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f184,f149,f481])).

fof(f184,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f151,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f479,plain,
    ( spl5_26
    | ~ spl5_22
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f478,f474,f337,f421])).

fof(f474,plain,
    ( spl5_30
  <=> k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f478,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl5_22
    | ~ spl5_30 ),
    inference(forward_demodulation,[],[f476,f339])).

fof(f476,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f474])).

fof(f477,plain,
    ( spl5_30
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f181,f149,f474])).

fof(f181,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f151,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f462,plain,
    ( spl5_29
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_20
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f457,f453,f328,f149,f135,f130,f125,f120,f115,f459])).

fof(f453,plain,
    ( spl5_28
  <=> v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f457,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_20
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f455,f392])).

fof(f455,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f453])).

fof(f456,plain,
    ( spl5_28
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f222,f149,f130,f125,f453])).

fof(f222,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f127,f132,f151,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_funct_1(k2_tops_2(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f410,plain,
    ( spl5_6
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f379,f149,f135,f130,f125,f120,f115,f139])).

fof(f388,plain,
    ( spl5_24
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f296,f213,f385])).

fof(f296,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f215,f99])).

fof(f340,plain,
    ( spl5_22
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f322,f170,f162,f337])).

fof(f162,plain,
    ( spl5_8
  <=> k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f322,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f164,f239])).

fof(f164,plain,
    ( k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f162])).

fof(f331,plain,
    ( spl5_20
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f321,f192,f175,f328])).

fof(f175,plain,
    ( spl5_10
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f321,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f177,f298])).

fof(f177,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f175])).

fof(f320,plain,
    ( spl5_19
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f241,f149,f135,f130,f125,f120,f115,f317])).

fof(f241,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f117,f122,f127,f137,f132,f151,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f294,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_10 ),
    inference(subsumption_resolution,[],[f271,f176])).

fof(f176,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f175])).

fof(f271,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f117,f122,f127,f137,f132,f151,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f268,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(subsumption_resolution,[],[f245,f163])).

fof(f163,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f162])).

fof(f245,plain,
    ( k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f117,f122,f127,f137,f132,f151,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f234,plain,
    ( ~ spl5_8
    | ~ spl5_10
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f168,f139,f135,f230,f226,f175,f162])).

fof(f168,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ v4_pre_topc(sK3,sK0)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f145,f137])).

fof(f145,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ v4_pre_topc(sK3,sK0)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f79,f141])).

fof(f79,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ v4_pre_topc(sK3,sK0)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f221,plain,
    ( spl5_15
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f158,f149,f218])).

fof(f158,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f151,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f216,plain,
    ( ~ spl5_8
    | ~ spl5_10
    | spl5_14
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f166,f139,f135,f213,f175,f162])).

fof(f166,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f143,f137])).

fof(f143,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f77,f141])).

fof(f77,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f199,plain,
    ( spl5_5
    | spl5_13 ),
    inference(avatar_split_clause,[],[f76,f197,f135])).

fof(f76,plain,(
    ! [X4] :
      ( v4_pre_topc(X4,sK0)
      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tops_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f195,plain,
    ( spl5_12
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f147,f120,f192])).

fof(f147,plain,
    ( l1_struct_0(sK1)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f122,f81])).

fof(f81,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f190,plain,
    ( spl5_5
    | spl5_11 ),
    inference(avatar_split_clause,[],[f75,f188,f135])).

fof(f75,plain,(
    ! [X4] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK1)
      | ~ v4_pre_topc(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tops_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f178,plain,
    ( spl5_5
    | spl5_10 ),
    inference(avatar_split_clause,[],[f73,f175,f135])).

fof(f73,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f173,plain,
    ( spl5_9
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f146,f115,f170])).

fof(f146,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f117,f81])).

fof(f165,plain,
    ( spl5_5
    | spl5_8 ),
    inference(avatar_split_clause,[],[f72,f162,f135])).

fof(f72,plain,
    ( k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f152,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f71,f149])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f142,plain,
    ( spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f74,f139,f135])).

fof(f74,plain,
    ( v2_funct_1(sK2)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f133,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f70,f130])).

fof(f70,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f128,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f69,f125])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f123,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f68,f120])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f118,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f67,f115])).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

%------------------------------------------------------------------------------
