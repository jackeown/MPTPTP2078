%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:29 EST 2020

% Result     : Theorem 2.64s
% Output     : Refutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :  485 (1683 expanded)
%              Number of leaves         :   73 ( 679 expanded)
%              Depth                    :   35
%              Number of atoms          : 3078 (7359 expanded)
%              Number of equality atoms :  132 ( 762 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6047,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f110,f115,f120,f127,f146,f214,f245,f258,f284,f289,f348,f380,f385,f441,f465,f467,f472,f483,f520,f525,f546,f632,f842,f867,f873,f994,f1102,f1113,f1158,f1167,f1179,f1180,f1181,f1318,f1356,f1362,f1554,f1596,f2498,f2990,f2992,f2993,f3018,f3027,f3471,f3480,f3709,f3876,f3951,f3965,f4637,f4646,f4913,f5251,f5883,f6035])).

fof(f6035,plain,
    ( ~ spl3_3
    | spl3_12
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_57
    | spl3_61
    | ~ spl3_85
    | ~ spl3_281
    | ~ spl3_313 ),
    inference(avatar_contradiction_clause,[],[f6034])).

fof(f6034,plain,
    ( $false
    | ~ spl3_3
    | spl3_12
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_57
    | spl3_61
    | ~ spl3_85
    | ~ spl3_281
    | ~ spl3_313 ),
    inference(subsumption_resolution,[],[f6033,f5395])).

fof(f5395,plain,
    ( v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0)
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_85
    | ~ spl3_281 ),
    inference(subsumption_resolution,[],[f5394,f1317])).

fof(f1317,plain,
    ( m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_85 ),
    inference(avatar_component_clause,[],[f1315])).

fof(f1315,plain,
    ( spl3_85
  <=> m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).

fof(f5394,plain,
    ( ~ m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0)
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_281 ),
    inference(forward_demodulation,[],[f5393,f519])).

fof(f519,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f517])).

fof(f517,plain,
    ( spl3_30
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f5393,plain,
    ( v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_281 ),
    inference(subsumption_resolution,[],[f5387,f114])).

fof(f114,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl3_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f5387,plain,
    ( v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_281 ),
    inference(resolution,[],[f5250,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f5250,plain,
    ( r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),u1_pre_topc(sK0))
    | ~ spl3_281 ),
    inference(avatar_component_clause,[],[f5248])).

fof(f5248,plain,
    ( spl3_281
  <=> r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_281])])).

fof(f6033,plain,
    ( ~ v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0)
    | ~ spl3_3
    | spl3_12
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_57
    | spl3_61
    | ~ spl3_313 ),
    inference(forward_demodulation,[],[f6032,f5884])).

fof(f5884,plain,
    ( sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))
    | ~ spl3_28
    | ~ spl3_313 ),
    inference(superposition,[],[f5882,f473])).

fof(f473,plain,
    ( ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),X0)
    | ~ spl3_28 ),
    inference(unit_resulting_resolution,[],[f471,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f471,plain,
    ( m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f469])).

fof(f469,plain,
    ( spl3_28
  <=> m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f5882,plain,
    ( sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))
    | ~ spl3_313 ),
    inference(avatar_component_clause,[],[f5880])).

fof(f5880,plain,
    ( spl3_313
  <=> sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_313])])).

fof(f6032,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)
    | ~ spl3_3
    | spl3_12
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_57
    | spl3_61 ),
    inference(subsumption_resolution,[],[f6031,f454])).

fof(f454,plain,
    ( v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f452])).

fof(f452,plain,
    ( spl3_27
  <=> v1_funct_1(k6_partfun1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f6031,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ spl3_3
    | spl3_12
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_26
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_57
    | spl3_61 ),
    inference(subsumption_resolution,[],[f6030,f219])).

fof(f219,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl3_12
  <=> v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f6030,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_26
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_57
    | spl3_61 ),
    inference(subsumption_resolution,[],[f6029,f471])).

fof(f6029,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_26
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_57
    | spl3_61 ),
    inference(subsumption_resolution,[],[f6017,f440])).

fof(f440,plain,
    ( v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl3_26
  <=> v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f6017,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_57
    | spl3_61 ),
    inference(superposition,[],[f4912,f473])).

fof(f4912,plain,
    ( ! [X1] :
        ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0)
        | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_57
    | spl3_61 ),
    inference(subsumption_resolution,[],[f4895,f865])).

fof(f865,plain,
    ( k1_xboole_0 != k2_struct_0(sK0)
    | spl3_61 ),
    inference(avatar_component_clause,[],[f864])).

fof(f864,plain,
    ( spl3_61
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f4895,plain,
    ( ! [X1] :
        ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0)
        | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | k1_xboole_0 = k2_struct_0(sK0)
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_57 ),
    inference(forward_demodulation,[],[f4894,f384])).

fof(f384,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f382])).

fof(f382,plain,
    ( spl3_22
  <=> u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f4894,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | k1_xboole_0 = k2_struct_0(sK0)
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1)
        | ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_57 ),
    inference(forward_demodulation,[],[f4893,f384])).

fof(f4893,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | k1_xboole_0 = k2_struct_0(sK0)
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
        | ~ v1_funct_1(X1)
        | ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_57 ),
    inference(forward_demodulation,[],[f4892,f384])).

fof(f4892,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k2_struct_0(sK0)
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | ~ v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
        | ~ v1_funct_1(X1)
        | ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_57 ),
    inference(forward_demodulation,[],[f2070,f841])).

fof(f841,plain,
    ( k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f839])).

fof(f839,plain,
    ( spl3_57
  <=> k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f2070,plain,
    ( ! [X1] :
        ( v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | ~ v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
        | ~ v1_funct_1(X1)
        | ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_30 ),
    inference(resolution,[],[f555,f283])).

fof(f283,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl3_16
  <=> l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f555,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v5_pre_topc(X1,sK0,X0)
        | k2_struct_0(X0) = k1_xboole_0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1,sK2(sK0,X0,X1)),sK0) )
    | ~ spl3_3
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f548,f114])).

fof(f548,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1,sK2(sK0,X0,X1)),sK0)
        | v5_pre_topc(X1,sK0,X0)
        | k2_struct_0(X0) = k1_xboole_0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_30 ),
    inference(superposition,[],[f73,f519])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
      | v5_pre_topc(X2,X0,X1)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
                    & v3_pre_topc(sK2(X0,X1,X2),X1)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
        & v3_pre_topc(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v3_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
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
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
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
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

fof(f5883,plain,
    ( spl3_313
    | ~ spl3_85 ),
    inference(avatar_split_clause,[],[f5001,f1315,f5880])).

fof(f5001,plain,
    ( sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))
    | ~ spl3_85 ),
    inference(unit_resulting_resolution,[],[f1317,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f5251,plain,
    ( spl3_281
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_25
    | ~ spl3_80
    | ~ spl3_85 ),
    inference(avatar_split_clause,[],[f5014,f1315,f1176,f427,f281,f124,f117,f112,f107,f102,f5248])).

fof(f102,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f107,plain,
    ( spl3_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f117,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f124,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f427,plain,
    ( spl3_25
  <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f1176,plain,
    ( spl3_80
  <=> v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).

fof(f5014,plain,
    ( r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),u1_pre_topc(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_25
    | ~ spl3_80
    | ~ spl3_85 ),
    inference(forward_demodulation,[],[f4997,f429])).

fof(f429,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f427])).

fof(f4997,plain,
    ( r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k5_tmap_1(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_80
    | ~ spl3_85 ),
    inference(unit_resulting_resolution,[],[f1178,f1317,f335])).

fof(f335,plain,
    ( ! [X7] :
        ( r2_hidden(X7,k5_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X7,k6_tmap_1(sK0,sK1)) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f334,f209])).

fof(f209,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f104,f109,f114,f119,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f119,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f109,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f104,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f334,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X7,k6_tmap_1(sK0,sK1))
        | r2_hidden(X7,u1_pre_topc(k6_tmap_1(sK0,sK1))) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f325,f204])).

fof(f204,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f202,f153])).

fof(f153,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f126,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f126,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f202,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f104,f109,f114,f119,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f325,plain,
    ( ! [X7] :
        ( ~ v3_pre_topc(X7,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | r2_hidden(X7,u1_pre_topc(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_16 ),
    inference(resolution,[],[f283,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1178,plain,
    ( v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))
    | ~ spl3_80 ),
    inference(avatar_component_clause,[],[f1176])).

fof(f4913,plain,
    ( ~ spl3_12
    | spl3_8
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f3015,f377,f143,f217])).

fof(f143,plain,
    ( spl3_8
  <=> v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f377,plain,
    ( spl3_21
  <=> k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f3015,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | spl3_8
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f144,f379])).

fof(f379,plain,
    ( k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f377])).

fof(f144,plain,
    ( ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f4646,plain,
    ( ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_89
    | ~ spl3_91
    | spl3_216
    | ~ spl3_243
    | ~ spl3_268 ),
    inference(avatar_contradiction_clause,[],[f4645])).

fof(f4645,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_89
    | ~ spl3_91
    | spl3_216
    | ~ spl3_243
    | ~ spl3_268 ),
    inference(subsumption_resolution,[],[f4644,f1112])).

fof(f1112,plain,
    ( v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl3_75 ),
    inference(avatar_component_clause,[],[f1110])).

fof(f1110,plain,
    ( spl3_75
  <=> v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f4644,plain,
    ( ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_89
    | ~ spl3_91
    | spl3_216
    | ~ spl3_243
    | ~ spl3_268 ),
    inference(subsumption_resolution,[],[f4643,f3474])).

fof(f3474,plain,
    ( ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0)
    | spl3_216 ),
    inference(avatar_component_clause,[],[f3473])).

fof(f3473,plain,
    ( spl3_216
  <=> v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_216])])).

fof(f4643,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_243
    | ~ spl3_268 ),
    inference(subsumption_resolution,[],[f4642,f1595])).

fof(f1595,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_91 ),
    inference(avatar_component_clause,[],[f1593])).

fof(f1593,plain,
    ( spl3_91
  <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).

fof(f4642,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_89
    | ~ spl3_243
    | ~ spl3_268 ),
    inference(subsumption_resolution,[],[f4641,f1553])).

fof(f1553,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl3_89 ),
    inference(avatar_component_clause,[],[f1551])).

fof(f1551,plain,
    ( spl3_89
  <=> v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).

fof(f4641,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_243
    | ~ spl3_268 ),
    inference(subsumption_resolution,[],[f4640,f3964])).

fof(f3964,plain,
    ( v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),sK0)
    | ~ spl3_243 ),
    inference(avatar_component_clause,[],[f3962])).

fof(f3962,plain,
    ( spl3_243
  <=> v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_243])])).

fof(f4640,plain,
    ( ~ v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),sK0)
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_268 ),
    inference(superposition,[],[f1988,f4636])).

fof(f4636,plain,
    ( sK2(sK0,sK0,k6_partfun1(k1_xboole_0)) = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0)))
    | ~ spl3_268 ),
    inference(avatar_component_clause,[],[f4634])).

fof(f4634,plain,
    ( spl3_268
  <=> sK2(sK0,sK0,k6_partfun1(k1_xboole_0)) = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_268])])).

fof(f1988,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK2(sK0,sK0,X0)),sK0)
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1987,f866])).

fof(f866,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f864])).

fof(f1987,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_xboole_0,k2_struct_0(sK0))
        | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK2(sK0,sK0,X0)),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1986,f519])).

fof(f1986,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK2(sK0,sK0,X0)),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1985,f866])).

fof(f1985,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X0,sK2(sK0,sK0,X0)),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1984,f519])).

fof(f1984,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),X0,sK2(sK0,sK0,X0)),sK0)
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1983,f866])).

fof(f1983,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
        | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),X0,sK2(sK0,sK0,X0)),sK0)
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1979,f519])).

fof(f1979,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0))))
        | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),X0,sK2(sK0,sK0,X0)),sK0)
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(resolution,[],[f1459,f114])).

fof(f1459,plain,
    ( ! [X24,X25] :
        ( ~ l1_pre_topc(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X24))))
        | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0)
        | v5_pre_topc(X25,sK0,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,k1_xboole_0,u1_struct_0(X24)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1458,f866])).

fof(f1458,plain,
    ( ! [X24,X25] :
        ( ~ v1_funct_2(X25,k2_struct_0(sK0),u1_struct_0(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X24))))
        | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0)
        | v5_pre_topc(X25,sK0,X24)
        | ~ v1_funct_1(X25)
        | ~ l1_pre_topc(X24) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1457,f519])).

fof(f1457,plain,
    ( ! [X24,X25] :
        ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X24))))
        | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0)
        | v5_pre_topc(X25,sK0,X24)
        | ~ v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24))
        | ~ v1_funct_1(X25)
        | ~ l1_pre_topc(X24) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1456,f866])).

fof(f1456,plain,
    ( ! [X24,X25] :
        ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X24))))
        | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0)
        | v5_pre_topc(X25,sK0,X24)
        | ~ v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24))
        | ~ v1_funct_1(X25)
        | ~ l1_pre_topc(X24) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1455,f519])).

fof(f1455,plain,
    ( ! [X24,X25] :
        ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0)
        | v5_pre_topc(X25,sK0,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X24))))
        | ~ v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24))
        | ~ v1_funct_1(X25)
        | ~ l1_pre_topc(X24) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1454,f866])).

fof(f1454,plain,
    ( ! [X24,X25] :
        ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0)
        | v5_pre_topc(X25,sK0,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X24))))
        | ~ v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24))
        | ~ v1_funct_1(X25)
        | ~ l1_pre_topc(X24) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1453,f519])).

fof(f1453,plain,
    ( ! [X24,X25] :
        ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0)
        | v5_pre_topc(X25,sK0,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X24))))
        | ~ v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24))
        | ~ v1_funct_1(X25)
        | ~ l1_pre_topc(X24) )
    | ~ spl3_3
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f1444,f114])).

fof(f1444,plain,
    ( ! [X24,X25] :
        ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0)
        | v5_pre_topc(X25,sK0,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X24))))
        | ~ v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24))
        | ~ v1_funct_1(X25)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_61 ),
    inference(trivial_inequality_removal,[],[f1439])).

fof(f1439,plain,
    ( ! [X24,X25] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0)
        | v5_pre_topc(X25,sK0,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X24))))
        | ~ v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24))
        | ~ v1_funct_1(X25)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_61 ),
    inference(superposition,[],[f74,f866])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) != k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f4637,plain,
    ( spl3_268
    | ~ spl3_217 ),
    inference(avatar_split_clause,[],[f3977,f3477,f4634])).

fof(f3477,plain,
    ( spl3_217
  <=> m1_subset_1(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_217])])).

fof(f3977,plain,
    ( sK2(sK0,sK0,k6_partfun1(k1_xboole_0)) = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0)))
    | ~ spl3_217 ),
    inference(unit_resulting_resolution,[],[f3479,f86])).

fof(f3479,plain,
    ( m1_subset_1(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_217 ),
    inference(avatar_component_clause,[],[f3477])).

fof(f3965,plain,
    ( spl3_243
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_89
    | ~ spl3_91
    | spl3_216 ),
    inference(avatar_split_clause,[],[f3959,f3473,f1593,f1551,f1110,f864,f517,f112,f3962])).

fof(f3959,plain,
    ( v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),sK0)
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_89
    | ~ spl3_91
    | spl3_216 ),
    inference(unit_resulting_resolution,[],[f1112,f1553,f1595,f3474,f1911])).

fof(f1911,plain,
    ( ! [X0] :
        ( v3_pre_topc(sK2(sK0,sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1910,f866])).

fof(f1910,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_xboole_0,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v3_pre_topc(sK2(sK0,sK0,X0),sK0)
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1909,f519])).

fof(f1909,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v3_pre_topc(sK2(sK0,sK0,X0),sK0)
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1908,f866])).

fof(f1908,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
        | v3_pre_topc(sK2(sK0,sK0,X0),sK0)
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1904,f519])).

fof(f1904,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0))))
        | v3_pre_topc(sK2(sK0,sK0,X0),sK0)
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(resolution,[],[f1469,f114])).

fof(f1469,plain,
    ( ! [X28,X29] :
        ( ~ l1_pre_topc(X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X28))))
        | v3_pre_topc(sK2(sK0,X28,X29),X28)
        | v5_pre_topc(X29,sK0,X28)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,k1_xboole_0,u1_struct_0(X28)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1468,f866])).

fof(f1468,plain,
    ( ! [X28,X29] :
        ( ~ v1_funct_2(X29,k2_struct_0(sK0),u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X28))))
        | v3_pre_topc(sK2(sK0,X28,X29),X28)
        | v5_pre_topc(X29,sK0,X28)
        | ~ v1_funct_1(X29)
        | ~ l1_pre_topc(X28) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1467,f519])).

fof(f1467,plain,
    ( ! [X28,X29] :
        ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X28))))
        | v3_pre_topc(sK2(sK0,X28,X29),X28)
        | v5_pre_topc(X29,sK0,X28)
        | ~ v1_funct_2(X29,u1_struct_0(sK0),u1_struct_0(X28))
        | ~ v1_funct_1(X29)
        | ~ l1_pre_topc(X28) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1466,f866])).

fof(f1466,plain,
    ( ! [X28,X29] :
        ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X28))))
        | v3_pre_topc(sK2(sK0,X28,X29),X28)
        | v5_pre_topc(X29,sK0,X28)
        | ~ v1_funct_2(X29,u1_struct_0(sK0),u1_struct_0(X28))
        | ~ v1_funct_1(X29)
        | ~ l1_pre_topc(X28) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1465,f519])).

fof(f1465,plain,
    ( ! [X28,X29] :
        ( v3_pre_topc(sK2(sK0,X28,X29),X28)
        | v5_pre_topc(X29,sK0,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X28))))
        | ~ v1_funct_2(X29,u1_struct_0(sK0),u1_struct_0(X28))
        | ~ v1_funct_1(X29)
        | ~ l1_pre_topc(X28) )
    | ~ spl3_3
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f1442,f114])).

fof(f1442,plain,
    ( ! [X28,X29] :
        ( v3_pre_topc(sK2(sK0,X28,X29),X28)
        | v5_pre_topc(X29,sK0,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X28))))
        | ~ v1_funct_2(X29,u1_struct_0(sK0),u1_struct_0(X28))
        | ~ v1_funct_1(X29)
        | ~ l1_pre_topc(X28)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_61 ),
    inference(trivial_inequality_removal,[],[f1441])).

fof(f1441,plain,
    ( ! [X28,X29] :
        ( k1_xboole_0 != k1_xboole_0
        | v3_pre_topc(sK2(sK0,X28,X29),X28)
        | v5_pre_topc(X29,sK0,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X28))))
        | ~ v1_funct_2(X29,u1_struct_0(sK0),u1_struct_0(X28))
        | ~ v1_funct_1(X29)
        | ~ l1_pre_topc(X28)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_61 ),
    inference(superposition,[],[f72,f866])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) != k1_xboole_0
      | v3_pre_topc(sK2(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3951,plain,
    ( ~ spl3_3
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_89
    | ~ spl3_91
    | spl3_135
    | ~ spl3_157
    | ~ spl3_216
    | ~ spl3_241 ),
    inference(avatar_contradiction_clause,[],[f3950])).

fof(f3950,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_89
    | ~ spl3_91
    | spl3_135
    | ~ spl3_157
    | ~ spl3_216
    | ~ spl3_241 ),
    inference(subsumption_resolution,[],[f3949,f3875])).

fof(f3875,plain,
    ( v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0)
    | ~ spl3_241 ),
    inference(avatar_component_clause,[],[f3873])).

fof(f3873,plain,
    ( spl3_241
  <=> v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_241])])).

fof(f3949,plain,
    ( ~ v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0)
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_89
    | ~ spl3_91
    | spl3_135
    | ~ spl3_157
    | ~ spl3_216 ),
    inference(subsumption_resolution,[],[f3941,f2497])).

fof(f2497,plain,
    ( m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_157 ),
    inference(avatar_component_clause,[],[f2495])).

fof(f2495,plain,
    ( spl3_157
  <=> m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_157])])).

fof(f3941,plain,
    ( ~ m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0)
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_89
    | ~ spl3_91
    | spl3_135
    | ~ spl3_216 ),
    inference(resolution,[],[f3495,f2307])).

fof(f2307,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)
    | spl3_135 ),
    inference(avatar_component_clause,[],[f2305])).

fof(f2305,plain,
    ( spl3_135
  <=> v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_135])])).

fof(f3495,plain,
    ( ! [X1] :
        ( v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | ~ v3_pre_topc(X1,sK0) )
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_89
    | ~ spl3_91
    | ~ spl3_216 ),
    inference(subsumption_resolution,[],[f3494,f1553])).

fof(f3494,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,sK0) )
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_91
    | ~ spl3_216 ),
    inference(forward_demodulation,[],[f3493,f866])).

fof(f3493,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,sK0) )
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_91
    | ~ spl3_216 ),
    inference(forward_demodulation,[],[f3492,f519])).

fof(f3492,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_91
    | ~ spl3_216 ),
    inference(forward_demodulation,[],[f3491,f866])).

fof(f3491,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_91
    | ~ spl3_216 ),
    inference(forward_demodulation,[],[f3490,f519])).

fof(f3490,plain,
    ( ! [X1] :
        ( v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_91
    | ~ spl3_216 ),
    inference(forward_demodulation,[],[f3489,f1418])).

fof(f1418,plain,
    ( ! [X16] : k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X16) = k10_relat_1(k6_partfun1(k1_xboole_0),X16)
    | ~ spl3_28
    | ~ spl3_61 ),
    inference(superposition,[],[f473,f866])).

fof(f3489,plain,
    ( ! [X1] :
        ( v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_91
    | ~ spl3_216 ),
    inference(forward_demodulation,[],[f3488,f866])).

fof(f3488,plain,
    ( ! [X1] :
        ( v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_91
    | ~ spl3_216 ),
    inference(forward_demodulation,[],[f3487,f519])).

fof(f3487,plain,
    ( ! [X1] :
        ( v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_91
    | ~ spl3_216 ),
    inference(subsumption_resolution,[],[f3486,f1595])).

fof(f3486,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_216 ),
    inference(forward_demodulation,[],[f3485,f866])).

fof(f3485,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_216 ),
    inference(forward_demodulation,[],[f3484,f519])).

fof(f3484,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0))))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_216 ),
    inference(subsumption_resolution,[],[f3483,f114])).

fof(f3483,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0))))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_216 ),
    inference(subsumption_resolution,[],[f3482,f1112])).

fof(f3482,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0))))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0))
        | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_216 ),
    inference(resolution,[],[f3475,f1452])).

fof(f1452,plain,
    ( ! [X23,X21,X22] :
        ( ~ v5_pre_topc(X23,sK0,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X22))))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0)
        | ~ v3_pre_topc(X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v1_funct_2(X23,k1_xboole_0,u1_struct_0(X22))
        | ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1451,f866])).

fof(f1451,plain,
    ( ! [X23,X21,X22] :
        ( ~ v1_funct_2(X23,k2_struct_0(sK0),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X22))))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0)
        | ~ v3_pre_topc(X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v5_pre_topc(X23,sK0,X22)
        | ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1450,f519])).

fof(f1450,plain,
    ( ! [X23,X21,X22] :
        ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X22))))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0)
        | ~ v3_pre_topc(X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v5_pre_topc(X23,sK0,X22)
        | ~ v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22))
        | ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1449,f866])).

fof(f1449,plain,
    ( ! [X23,X21,X22] :
        ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X22))))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0)
        | ~ v3_pre_topc(X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v5_pre_topc(X23,sK0,X22)
        | ~ v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22))
        | ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1448,f519])).

fof(f1448,plain,
    ( ! [X23,X21,X22] :
        ( v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0)
        | ~ v3_pre_topc(X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v5_pre_topc(X23,sK0,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22))))
        | ~ v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22))
        | ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1447,f866])).

fof(f1447,plain,
    ( ! [X23,X21,X22] :
        ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X22),X23,X21),sK0)
        | ~ v3_pre_topc(X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v5_pre_topc(X23,sK0,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22))))
        | ~ v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22))
        | ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1446,f519])).

fof(f1446,plain,
    ( ! [X23,X21,X22] :
        ( ~ v3_pre_topc(X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v5_pre_topc(X23,sK0,X22)
        | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X21),sK0)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22))))
        | ~ v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22))
        | ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22) )
    | ~ spl3_3
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f1445,f114])).

fof(f1445,plain,
    ( ! [X23,X21,X22] :
        ( ~ v3_pre_topc(X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v5_pre_topc(X23,sK0,X22)
        | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X21),sK0)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22))))
        | ~ v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22))
        | ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_61 ),
    inference(trivial_inequality_removal,[],[f1438])).

fof(f1438,plain,
    ( ! [X23,X21,X22] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ v3_pre_topc(X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v5_pre_topc(X23,sK0,X22)
        | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X21),sK0)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22))))
        | ~ v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22))
        | ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_61 ),
    inference(superposition,[],[f68,f866])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( k2_struct_0(X0) != k1_xboole_0
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3475,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0)
    | ~ spl3_216 ),
    inference(avatar_component_clause,[],[f3473])).

fof(f3876,plain,
    ( spl3_241
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_157
    | ~ spl3_237 ),
    inference(avatar_split_clause,[],[f3856,f3706,f2495,f864,f517,f112,f3873])).

fof(f3706,plain,
    ( spl3_237
  <=> r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_237])])).

fof(f3856,plain,
    ( v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0)
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_157
    | ~ spl3_237 ),
    inference(subsumption_resolution,[],[f3855,f2497])).

fof(f3855,plain,
    ( ~ m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0)
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_237 ),
    inference(forward_demodulation,[],[f3854,f866])).

fof(f3854,plain,
    ( ~ m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0)
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_237 ),
    inference(forward_demodulation,[],[f3853,f519])).

fof(f3853,plain,
    ( v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0)
    | ~ m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_237 ),
    inference(subsumption_resolution,[],[f3846,f114])).

fof(f3846,plain,
    ( v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0)
    | ~ m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_237 ),
    inference(resolution,[],[f3708,f76])).

fof(f3708,plain,
    ( r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),u1_pre_topc(sK0))
    | ~ spl3_237 ),
    inference(avatar_component_clause,[],[f3706])).

fof(f3709,plain,
    ( spl3_237
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_25
    | ~ spl3_61
    | ~ spl3_133
    | ~ spl3_157 ),
    inference(avatar_split_clause,[],[f3434,f2495,f2275,f864,f427,f281,f124,f117,f112,f107,f102,f3706])).

fof(f2275,plain,
    ( spl3_133
  <=> v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_133])])).

fof(f3434,plain,
    ( r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),u1_pre_topc(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_25
    | ~ spl3_61
    | ~ spl3_133
    | ~ spl3_157 ),
    inference(unit_resulting_resolution,[],[f2277,f2497,f3050])).

fof(f3050,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | r2_hidden(X2,u1_pre_topc(sK0))
        | ~ v3_pre_topc(X2,k6_tmap_1(sK0,sK1)) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_25
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f3047,f866])).

fof(f3047,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X2,u1_pre_topc(sK0))
        | ~ v3_pre_topc(X2,k6_tmap_1(sK0,sK1)) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_25 ),
    inference(superposition,[],[f335,f429])).

fof(f2277,plain,
    ( v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1))
    | ~ spl3_133 ),
    inference(avatar_component_clause,[],[f2275])).

fof(f3480,plain,
    ( spl3_216
    | spl3_217
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_89
    | ~ spl3_91 ),
    inference(avatar_split_clause,[],[f2383,f1593,f1551,f1110,f864,f517,f112,f3477,f3473])).

fof(f2383,plain,
    ( m1_subset_1(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0)
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_89
    | ~ spl3_91 ),
    inference(subsumption_resolution,[],[f2382,f1112])).

fof(f2382,plain,
    ( m1_subset_1(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_89
    | ~ spl3_91 ),
    inference(subsumption_resolution,[],[f2381,f1595])).

fof(f2381,plain,
    ( m1_subset_1(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_89 ),
    inference(resolution,[],[f1950,f1553])).

fof(f1950,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | m1_subset_1(sK2(sK0,sK0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1949,f866])).

fof(f1949,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_xboole_0,k2_struct_0(sK0))
        | m1_subset_1(sK2(sK0,sK0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1948,f519])).

fof(f1948,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2(sK0,sK0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1947,f866])).

fof(f1947,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2(sK0,sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1946,f519])).

fof(f1946,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | m1_subset_1(sK2(sK0,sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1945,f866])).

fof(f1945,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
        | m1_subset_1(sK2(sK0,sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1941,f519])).

fof(f1941,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0))))
        | m1_subset_1(sK2(sK0,sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(resolution,[],[f1464,f114])).

fof(f1464,plain,
    ( ! [X26,X27] :
        ( ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X26))))
        | m1_subset_1(sK2(sK0,X26,X27),k1_zfmisc_1(u1_struct_0(X26)))
        | v5_pre_topc(X27,sK0,X26)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,k1_xboole_0,u1_struct_0(X26)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1463,f866])).

fof(f1463,plain,
    ( ! [X26,X27] :
        ( ~ v1_funct_2(X27,k2_struct_0(sK0),u1_struct_0(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X26))))
        | m1_subset_1(sK2(sK0,X26,X27),k1_zfmisc_1(u1_struct_0(X26)))
        | v5_pre_topc(X27,sK0,X26)
        | ~ v1_funct_1(X27)
        | ~ l1_pre_topc(X26) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1462,f519])).

fof(f1462,plain,
    ( ! [X26,X27] :
        ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X26))))
        | m1_subset_1(sK2(sK0,X26,X27),k1_zfmisc_1(u1_struct_0(X26)))
        | v5_pre_topc(X27,sK0,X26)
        | ~ v1_funct_2(X27,u1_struct_0(sK0),u1_struct_0(X26))
        | ~ v1_funct_1(X27)
        | ~ l1_pre_topc(X26) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1461,f866])).

fof(f1461,plain,
    ( ! [X26,X27] :
        ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X26))))
        | m1_subset_1(sK2(sK0,X26,X27),k1_zfmisc_1(u1_struct_0(X26)))
        | v5_pre_topc(X27,sK0,X26)
        | ~ v1_funct_2(X27,u1_struct_0(sK0),u1_struct_0(X26))
        | ~ v1_funct_1(X27)
        | ~ l1_pre_topc(X26) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1460,f519])).

fof(f1460,plain,
    ( ! [X26,X27] :
        ( m1_subset_1(sK2(sK0,X26,X27),k1_zfmisc_1(u1_struct_0(X26)))
        | v5_pre_topc(X27,sK0,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X26))))
        | ~ v1_funct_2(X27,u1_struct_0(sK0),u1_struct_0(X26))
        | ~ v1_funct_1(X27)
        | ~ l1_pre_topc(X26) )
    | ~ spl3_3
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f1443,f114])).

fof(f1443,plain,
    ( ! [X26,X27] :
        ( m1_subset_1(sK2(sK0,X26,X27),k1_zfmisc_1(u1_struct_0(X26)))
        | v5_pre_topc(X27,sK0,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X26))))
        | ~ v1_funct_2(X27,u1_struct_0(sK0),u1_struct_0(X26))
        | ~ v1_funct_1(X27)
        | ~ l1_pre_topc(X26)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_61 ),
    inference(trivial_inequality_removal,[],[f1440])).

fof(f1440,plain,
    ( ! [X26,X27] :
        ( k1_xboole_0 != k1_xboole_0
        | m1_subset_1(sK2(sK0,X26,X27),k1_zfmisc_1(u1_struct_0(X26)))
        | v5_pre_topc(X27,sK0,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X26))))
        | ~ v1_funct_2(X27,u1_struct_0(sK0),u1_struct_0(X26))
        | ~ v1_funct_1(X27)
        | ~ l1_pre_topc(X26)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_61 ),
    inference(superposition,[],[f70,f866])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) != k1_xboole_0
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3471,plain,
    ( ~ spl3_135
    | ~ spl3_3
    | spl3_8
    | ~ spl3_16
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_89
    | ~ spl3_91 ),
    inference(avatar_split_clause,[],[f3021,f1593,f1551,f1110,f864,f517,f469,f382,f377,f281,f143,f112,f2305])).

fof(f3021,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)
    | ~ spl3_3
    | spl3_8
    | ~ spl3_16
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_89
    | ~ spl3_91 ),
    inference(subsumption_resolution,[],[f3004,f3016])).

fof(f3016,plain,
    ( ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | spl3_8
    | ~ spl3_21
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f3015,f866])).

fof(f3004,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_89
    | ~ spl3_91 ),
    inference(subsumption_resolution,[],[f3003,f1112])).

fof(f3003,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_89
    | ~ spl3_91 ),
    inference(subsumption_resolution,[],[f3002,f1595])).

fof(f3002,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_89 ),
    inference(subsumption_resolution,[],[f2434,f1553])).

fof(f2434,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(superposition,[],[f1994,f1418])).

fof(f1994,plain,
    ( ! [X1] :
        ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0)
        | ~ v1_funct_2(X1,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1993,f866])).

fof(f1993,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,k1_xboole_0,k2_struct_0(sK0))
        | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1992,f384])).

fof(f1992,plain,
    ( ! [X1] :
        ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1991,f866])).

fof(f1991,plain,
    ( ! [X1] :
        ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1990,f384])).

fof(f1990,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0)
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1989,f866])).

fof(f1989,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
        | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0)
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1980,f384])).

fof(f1980,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0)
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(resolution,[],[f1459,f283])).

fof(f3027,plain,
    ( ~ spl3_86
    | spl3_8
    | ~ spl3_21
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f3016,f864,f377,f143,f1380])).

fof(f1380,plain,
    ( spl3_86
  <=> v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).

fof(f3018,plain,
    ( ~ spl3_3
    | spl3_8
    | ~ spl3_16
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_89
    | ~ spl3_91
    | spl3_133 ),
    inference(avatar_contradiction_clause,[],[f3017])).

fof(f3017,plain,
    ( $false
    | ~ spl3_3
    | spl3_8
    | ~ spl3_16
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_89
    | ~ spl3_91
    | spl3_133 ),
    inference(subsumption_resolution,[],[f3016,f3007])).

fof(f3007,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_89
    | ~ spl3_91
    | spl3_133 ),
    inference(subsumption_resolution,[],[f3006,f1112])).

fof(f3006,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_89
    | ~ spl3_91
    | spl3_133 ),
    inference(subsumption_resolution,[],[f3005,f1553])).

fof(f3005,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_91
    | spl3_133 ),
    inference(subsumption_resolution,[],[f2967,f1595])).

fof(f2967,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61
    | spl3_133 ),
    inference(resolution,[],[f2276,f1915])).

fof(f1915,plain,
    ( ! [X1] :
        ( v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_2(X1,k1_xboole_0,k1_xboole_0)
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1914,f866])).

fof(f1914,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,k1_xboole_0,k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1))
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1913,f384])).

fof(f1913,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1))
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1912,f866])).

fof(f1912,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
        | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1))
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1905,f384])).

fof(f1905,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1))
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(resolution,[],[f1469,f283])).

fof(f2276,plain,
    ( ~ v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1))
    | spl3_133 ),
    inference(avatar_component_clause,[],[f2275])).

fof(f2993,plain,
    ( k7_tmap_1(sK0,sK1) != k6_partfun1(k2_struct_0(sK0))
    | k1_xboole_0 != k2_struct_0(sK0)
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2992,plain,
    ( k1_xboole_0 != k2_struct_0(sK0)
    | sK1 != k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1)
    | sK1 = k10_relat_1(k6_partfun1(k1_xboole_0),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2990,plain,
    ( ~ spl3_3
    | spl3_6
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_35
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_78
    | ~ spl3_81
    | ~ spl3_86
    | ~ spl3_89
    | ~ spl3_91 ),
    inference(avatar_contradiction_clause,[],[f2989])).

fof(f2989,plain,
    ( $false
    | ~ spl3_3
    | spl3_6
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_35
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_78
    | ~ spl3_81
    | ~ spl3_86
    | ~ spl3_89
    | ~ spl3_91 ),
    inference(subsumption_resolution,[],[f2988,f545])).

fof(f545,plain,
    ( v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f543])).

fof(f543,plain,
    ( spl3_35
  <=> v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f2988,plain,
    ( ~ v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))
    | ~ spl3_3
    | spl3_6
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_78
    | ~ spl3_81
    | ~ spl3_86
    | ~ spl3_89
    | ~ spl3_91 ),
    inference(subsumption_resolution,[],[f2987,f1166])).

fof(f1166,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_78 ),
    inference(avatar_component_clause,[],[f1164])).

fof(f1164,plain,
    ( spl3_78
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f2987,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))
    | ~ spl3_3
    | spl3_6
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_81
    | ~ spl3_86
    | ~ spl3_89
    | ~ spl3_91 ),
    inference(subsumption_resolution,[],[f2981,f130])).

fof(f130,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl3_6
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f2981,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_81
    | ~ spl3_86
    | ~ spl3_89
    | ~ spl3_91 ),
    inference(superposition,[],[f2732,f1186])).

fof(f1186,plain,
    ( sK1 = k10_relat_1(k6_partfun1(k1_xboole_0),sK1)
    | ~ spl3_81 ),
    inference(avatar_component_clause,[],[f1184])).

fof(f1184,plain,
    ( spl3_81
  <=> sK1 = k10_relat_1(k6_partfun1(k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).

fof(f2732,plain,
    ( ! [X1] :
        ( v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_86
    | ~ spl3_89
    | ~ spl3_91 ),
    inference(subsumption_resolution,[],[f2731,f1553])).

fof(f2731,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_86
    | ~ spl3_91 ),
    inference(forward_demodulation,[],[f2730,f866])).

fof(f2730,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_86
    | ~ spl3_91 ),
    inference(forward_demodulation,[],[f2729,f384])).

fof(f2729,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_86
    | ~ spl3_91 ),
    inference(forward_demodulation,[],[f2728,f866])).

fof(f2728,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_86
    | ~ spl3_91 ),
    inference(forward_demodulation,[],[f2727,f384])).

fof(f2727,plain,
    ( ! [X1] :
        ( v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_86
    | ~ spl3_91 ),
    inference(forward_demodulation,[],[f2726,f1418])).

fof(f2726,plain,
    ( ! [X1] :
        ( v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_86
    | ~ spl3_91 ),
    inference(forward_demodulation,[],[f2725,f866])).

fof(f2725,plain,
    ( ! [X1] :
        ( v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_86
    | ~ spl3_91 ),
    inference(forward_demodulation,[],[f2724,f384])).

fof(f2724,plain,
    ( ! [X1] :
        ( v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_86
    | ~ spl3_91 ),
    inference(subsumption_resolution,[],[f2723,f1595])).

fof(f2723,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_86 ),
    inference(forward_demodulation,[],[f2722,f866])).

fof(f2722,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_86 ),
    inference(forward_demodulation,[],[f2721,f384])).

fof(f2721,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_86 ),
    inference(subsumption_resolution,[],[f2720,f283])).

fof(f2720,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
        | ~ l1_pre_topc(k6_tmap_1(sK0,sK1)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | ~ spl3_86 ),
    inference(subsumption_resolution,[],[f2719,f1112])).

fof(f2719,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
        | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
        | ~ l1_pre_topc(k6_tmap_1(sK0,sK1)) )
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_86 ),
    inference(resolution,[],[f1381,f1452])).

fof(f1381,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl3_86 ),
    inference(avatar_component_clause,[],[f1380])).

fof(f2498,plain,
    ( spl3_157
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | spl3_86
    | ~ spl3_89
    | ~ spl3_91 ),
    inference(avatar_split_clause,[],[f2417,f1593,f1551,f1380,f1110,f864,f517,f382,f281,f112,f2495])).

fof(f2417,plain,
    ( m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61
    | ~ spl3_75
    | spl3_86
    | ~ spl3_89
    | ~ spl3_91 ),
    inference(unit_resulting_resolution,[],[f1112,f1553,f1382,f1595,f1956])).

fof(f1956,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,k1_xboole_0,k1_xboole_0)
        | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1955,f866])).

fof(f1955,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,k1_xboole_0,k2_struct_0(sK0))
        | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1954,f384])).

fof(f1954,plain,
    ( ! [X1] :
        ( m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1953,f866])).

fof(f1953,plain,
    ( ! [X1] :
        ( m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1952,f384])).

fof(f1952,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1951,f866])).

fof(f1951,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
        | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f1942,f384])).

fof(f1942,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) )
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_61 ),
    inference(resolution,[],[f1464,f283])).

fof(f1382,plain,
    ( ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | spl3_86 ),
    inference(avatar_component_clause,[],[f1380])).

fof(f1596,plain,
    ( spl3_91
    | ~ spl3_28
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f1417,f864,f469,f1593])).

fof(f1417,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_28
    | ~ spl3_61 ),
    inference(superposition,[],[f471,f866])).

fof(f1554,plain,
    ( spl3_89
    | ~ spl3_26
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f1413,f864,f438,f1551])).

fof(f1413,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl3_26
    | ~ spl3_61 ),
    inference(superposition,[],[f440,f866])).

fof(f1362,plain,
    ( spl3_6
    | ~ spl3_12
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_31
    | ~ spl3_35
    | ~ spl3_74
    | ~ spl3_77 ),
    inference(avatar_contradiction_clause,[],[f1361])).

fof(f1361,plain,
    ( $false
    | spl3_6
    | ~ spl3_12
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_31
    | ~ spl3_35
    | ~ spl3_74
    | ~ spl3_77 ),
    inference(subsumption_resolution,[],[f1360,f130])).

fof(f1360,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_12
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_31
    | ~ spl3_35
    | ~ spl3_74
    | ~ spl3_77 ),
    inference(forward_demodulation,[],[f1359,f1157])).

fof(f1157,plain,
    ( sK1 = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1)
    | ~ spl3_77 ),
    inference(avatar_component_clause,[],[f1155])).

fof(f1155,plain,
    ( spl3_77
  <=> sK1 = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f1359,plain,
    ( v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1),sK0)
    | ~ spl3_12
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_31
    | ~ spl3_35
    | ~ spl3_74 ),
    inference(forward_demodulation,[],[f1357,f473])).

fof(f1357,plain,
    ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1),sK0)
    | ~ spl3_12
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_31
    | ~ spl3_35
    | ~ spl3_74 ),
    inference(unit_resulting_resolution,[],[f454,f524,f545,f440,f471,f218,f1101])).

fof(f1101,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0,X1),sK0) )
    | ~ spl3_74 ),
    inference(avatar_component_clause,[],[f1100])).

fof(f1100,plain,
    ( spl3_74
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0,X1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f218,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f217])).

fof(f524,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f522])).

fof(f522,plain,
    ( spl3_31
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f1356,plain,
    ( spl3_12
    | ~ spl3_8
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f1338,f377,f143,f217])).

fof(f1338,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl3_8
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f145,f379])).

fof(f145,plain,
    ( v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f1318,plain,
    ( spl3_85
    | spl3_12
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f1017,f871,f469,f452,f438,f217,f1315])).

fof(f871,plain,
    ( spl3_62
  <=> ! [X0] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0)
        | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f1017,plain,
    ( m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_12
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_62 ),
    inference(unit_resulting_resolution,[],[f454,f219,f440,f471,f872])).

fof(f872,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0)
        | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) )
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f871])).

fof(f1181,plain,
    ( k7_tmap_1(sK0,sK1) != k6_partfun1(k2_struct_0(sK0))
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(k6_tmap_1(sK0,sK1)) != k2_struct_0(sK0)
    | m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1180,plain,
    ( k7_tmap_1(sK0,sK1) != k6_partfun1(k2_struct_0(sK0))
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(k6_tmap_1(sK0,sK1)) != k2_struct_0(sK0)
    | v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1179,plain,
    ( spl3_80
    | spl3_12
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f868,f861,f469,f452,f438,f217,f1176])).

fof(f861,plain,
    ( spl3_60
  <=> ! [X0] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0)
        | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f868,plain,
    ( v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))
    | spl3_12
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_60 ),
    inference(unit_resulting_resolution,[],[f454,f219,f440,f471,f862])).

fof(f862,plain,
    ( ! [X0] :
        ( v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k6_tmap_1(sK0,sK1))
        | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) )
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f861])).

fof(f1167,plain,
    ( spl3_78
    | ~ spl3_72 ),
    inference(avatar_split_clause,[],[f1106,f991,f1164])).

fof(f991,plain,
    ( spl3_72
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f1106,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_72 ),
    inference(unit_resulting_resolution,[],[f993,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f993,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f991])).

fof(f1158,plain,
    ( spl3_77
    | ~ spl3_28
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f791,f480,f469,f1155])).

fof(f480,plain,
    ( spl3_29
  <=> sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f791,plain,
    ( sK1 = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1)
    | ~ spl3_28
    | ~ spl3_29 ),
    inference(superposition,[],[f473,f482])).

fof(f482,plain,
    ( sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f480])).

fof(f1113,plain,
    ( spl3_75
    | ~ spl3_27
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f1042,f864,f452,f1110])).

fof(f1042,plain,
    ( v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl3_27
    | ~ spl3_61 ),
    inference(superposition,[],[f454,f866])).

fof(f1102,plain,
    ( spl3_74
    | spl3_61
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f515,f382,f345,f281,f124,f112,f864,f1100])).

fof(f345,plain,
    ( spl3_19
  <=> l1_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f515,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k2_struct_0(sK0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0,X1),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f514,f413])).

fof(f413,plain,
    ( k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl3_19
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f411,f384])).

fof(f411,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f347,f65])).

fof(f347,plain,
    ( l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f345])).

fof(f514,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0,X1),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))
        | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f513,f283])).

fof(f513,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0,X1),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))
        | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(k6_tmap_1(sK0,sK1)) )
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_22 ),
    inference(superposition,[],[f253,f384])).

fof(f253,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,k2_struct_0(sK0),u1_struct_0(X1))
        | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X1),X2,X0),sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
        | ~ v3_pre_topc(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v5_pre_topc(X2,sK0,X1)
        | k2_struct_0(X1) = k1_xboole_0
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1) )
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f252,f153])).

fof(f252,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,k2_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
        | ~ v3_pre_topc(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v5_pre_topc(X2,sK0,X1)
        | k2_struct_0(X1) = k1_xboole_0
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X0),sK0) )
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f251,f153])).

fof(f251,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
        | ~ v3_pre_topc(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v5_pre_topc(X2,sK0,X1)
        | k2_struct_0(X1) = k1_xboole_0
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X0),sK0) )
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f250,f153])).

fof(f250,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_pre_topc(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v5_pre_topc(X2,sK0,X1)
        | k2_struct_0(X1) = k1_xboole_0
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X0),sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f67,f114])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f994,plain,
    ( spl3_72
    | ~ spl3_17
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f921,f864,f286,f991])).

fof(f286,plain,
    ( spl3_17
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f921,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_17
    | ~ spl3_61 ),
    inference(superposition,[],[f288,f866])).

fof(f288,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f286])).

fof(f873,plain,
    ( spl3_62
    | spl3_61
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f512,f382,f345,f281,f124,f112,f864,f871])).

fof(f512,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_struct_0(sK0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v1_funct_1(X0)
        | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f511,f413])).

fof(f511,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0)
        | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f510,f283])).

fof(f510,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
        | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_22 ),
    inference(superposition,[],[f249,f384])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | m1_subset_1(sK2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | k2_struct_0(X0) = k1_xboole_0
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f248,f153])).

fof(f248,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | m1_subset_1(sK2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | k2_struct_0(X0) = k1_xboole_0
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f247,f153])).

fof(f247,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | k2_struct_0(X0) = k1_xboole_0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f69,f114])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f867,plain,
    ( spl3_60
    | spl3_61
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f509,f382,f345,f281,f124,f112,f864,f861])).

fof(f509,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_struct_0(sK0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0)
        | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f508,f413])).

fof(f508,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k6_tmap_1(sK0,sK1))
        | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0)
        | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f507,f283])).

fof(f507,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k6_tmap_1(sK0,sK1))
        | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
        | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_22 ),
    inference(superposition,[],[f240,f384])).

fof(f240,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | v3_pre_topc(sK2(sK0,X0,X1),X0)
        | k2_struct_0(X0) = k1_xboole_0
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f239,f153])).

fof(f239,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | v3_pre_topc(sK2(sK0,X0,X1),X0)
        | k2_struct_0(X0) = k1_xboole_0
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f238,f153])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(sK2(sK0,X0,X1),X0)
        | k2_struct_0(X0) = k1_xboole_0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f71,f114])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v3_pre_topc(sK2(X0,X1,X2),X1)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f842,plain,
    ( spl3_57
    | ~ spl3_19
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f413,f382,f345,f839])).

fof(f632,plain,
    ( spl3_25
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f290,f255,f117,f112,f107,f102,f427])).

fof(f255,plain,
    ( spl3_14
  <=> r2_hidden(sK1,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f290,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f104,f109,f114,f119,f257,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f257,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f255])).

fof(f546,plain,
    ( spl3_35
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f504,f382,f286,f124,f112,f107,f102,f543])).

fof(f504,plain,
    ( v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f503,f337])).

fof(f337,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f288,f96])).

fof(f503,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_22 ),
    inference(duplicate_literal_removal,[],[f502])).

fof(f502,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_22 ),
    inference(superposition,[],[f237,f384])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v3_pre_topc(X0,k6_tmap_1(sK0,X0)) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f236,f153])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,k6_tmap_1(sK0,X0)) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f235,f104])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,k6_tmap_1(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f234,f114])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v3_pre_topc(X0,k6_tmap_1(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f98,f109])).

fof(f98,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X2,k6_tmap_1(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
      | X1 != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).

fof(f525,plain,
    ( spl3_31
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f337,f286,f522])).

fof(f520,plain,
    ( spl3_30
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f153,f124,f517])).

fof(f483,plain,
    ( spl3_29
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f167,f124,f117,f480])).

fof(f167,plain,
    ( sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f164,f153])).

fof(f164,plain,
    ( sK1 = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),sK1)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f119,f86])).

fof(f472,plain,
    ( spl3_28
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f229,f124,f117,f112,f107,f102,f469])).

fof(f229,plain,
    ( m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f228,f197])).

fof(f197,plain,
    ( k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f195,f153])).

fof(f195,plain,
    ( k7_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f104,f109,f114,f119,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

fof(f228,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f227,f153])).

fof(f227,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0))))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f225,f204])).

fof(f225,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f104,f109,f114,f119,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f467,plain,
    ( spl3_27
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f456,f377,f117,f112,f107,f102,f452])).

fof(f456,plain,
    ( v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f189,f379])).

fof(f189,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f104,f109,f114,f119,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_funct_1(k7_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f465,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_7
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f464])).

fof(f464,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_7
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f463,f456])).

fof(f463,plain,
    ( ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | spl3_7
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f134,f379])).

fof(f134,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl3_7
  <=> v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f441,plain,
    ( spl3_26
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f224,f124,f117,f112,f107,f102,f438])).

fof(f224,plain,
    ( v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f223,f197])).

fof(f223,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f222,f153])).

fof(f222,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),k2_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f221,f204])).

fof(f221,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f104,f109,f114,f119,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f385,plain,
    ( spl3_22
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f204,f124,f117,f112,f107,f102,f382])).

fof(f380,plain,
    ( spl3_21
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f197,f124,f117,f112,f107,f102,f377])).

fof(f348,plain,
    ( spl3_19
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f321,f281,f345])).

fof(f321,plain,
    ( l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f283,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f289,plain,
    ( spl3_17
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f246,f242,f124,f286])).

fof(f242,plain,
    ( spl3_13
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f246,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f244,f153])).

fof(f244,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f242])).

fof(f284,plain,
    ( spl3_16
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f184,f117,f112,f107,f102,f281])).

fof(f184,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f104,f109,f114,f119,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f258,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f171,f129,f117,f112,f255])).

fof(f171,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f114,f131,f119,f75])).

fof(f131,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f245,plain,
    ( spl3_13
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f138,f117,f242])).

fof(f138,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f119,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f214,plain,
    ( ~ spl3_9
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f147,f133,f129,f159,f143,f149])).

fof(f149,plain,
    ( spl3_9
  <=> v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f159,plain,
    ( spl3_10
  <=> m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f147,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f137,f131])).

fof(f137,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f64,f135])).

fof(f135,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f133])).

fof(f64,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
      | ~ v3_pre_topc(sK1,sK0) )
    & ( ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
        & v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
        & v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
        & v1_funct_1(k7_tmap_1(sK0,sK1)) )
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              | ~ v1_funct_1(k7_tmap_1(X0,X1))
              | ~ v3_pre_topc(X1,X0) )
            & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) )
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(sK0,X1),sK0,k6_tmap_1(sK0,X1))
            | ~ v1_funct_2(k7_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1)))
            | ~ v1_funct_1(k7_tmap_1(sK0,X1))
            | ~ v3_pre_topc(X1,sK0) )
          & ( ( m1_subset_1(k7_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1)))))
              & v5_pre_topc(k7_tmap_1(sK0,X1),sK0,k6_tmap_1(sK0,X1))
              & v1_funct_2(k7_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1)))
              & v1_funct_1(k7_tmap_1(sK0,X1)) )
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(k7_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1)))))
          | ~ v5_pre_topc(k7_tmap_1(sK0,X1),sK0,k6_tmap_1(sK0,X1))
          | ~ v1_funct_2(k7_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1)))
          | ~ v1_funct_1(k7_tmap_1(sK0,X1))
          | ~ v3_pre_topc(X1,sK0) )
        & ( ( m1_subset_1(k7_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1)))))
            & v5_pre_topc(k7_tmap_1(sK0,X1),sK0,k6_tmap_1(sK0,X1))
            & v1_funct_2(k7_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1)))
            & v1_funct_1(k7_tmap_1(sK0,X1)) )
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
        | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
        | ~ v3_pre_topc(sK1,sK0) )
      & ( ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
          & v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
          & v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
          & v1_funct_1(k7_tmap_1(sK0,sK1)) )
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k7_tmap_1(X0,X1))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k7_tmap_1(X0,X1))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_tmap_1)).

fof(f146,plain,
    ( spl3_6
    | spl3_8 ),
    inference(avatar_split_clause,[],[f62,f143,f129])).

fof(f62,plain,
    ( v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f127,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f121,f112,f124])).

fof(f121,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f114,f66])).

fof(f120,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f59,f117])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f115,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f58,f112])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f110,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f57,f107])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f105,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f56,f102])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:20:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (28973)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (28978)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (28990)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (28968)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (28968)Refutation not found, incomplete strategy% (28968)------------------------------
% 0.22/0.51  % (28968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28968)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28968)Memory used [KB]: 10618
% 0.22/0.51  % (28968)Time elapsed: 0.095 s
% 0.22/0.51  % (28968)------------------------------
% 0.22/0.51  % (28968)------------------------------
% 0.22/0.51  % (28969)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (28971)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.27/0.52  % (28984)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.27/0.52  % (28974)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.27/0.52  % (28973)Refutation not found, incomplete strategy% (28973)------------------------------
% 1.27/0.52  % (28973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (28973)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (28973)Memory used [KB]: 6140
% 1.27/0.52  % (28973)Time elapsed: 0.088 s
% 1.27/0.52  % (28973)------------------------------
% 1.27/0.52  % (28973)------------------------------
% 1.27/0.52  % (28983)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.27/0.52  % (28981)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.27/0.52  % (28974)Refutation not found, incomplete strategy% (28974)------------------------------
% 1.27/0.52  % (28974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (28974)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (28974)Memory used [KB]: 10618
% 1.27/0.52  % (28974)Time elapsed: 0.064 s
% 1.27/0.52  % (28974)------------------------------
% 1.27/0.52  % (28974)------------------------------
% 1.27/0.52  % (28976)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.27/0.52  % (28981)Refutation not found, incomplete strategy% (28981)------------------------------
% 1.27/0.52  % (28981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (28981)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (28981)Memory used [KB]: 6140
% 1.27/0.52  % (28981)Time elapsed: 0.107 s
% 1.27/0.52  % (28981)------------------------------
% 1.27/0.52  % (28981)------------------------------
% 1.27/0.52  % (28972)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.27/0.52  % (28982)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.27/0.52  % (28989)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.27/0.53  % (28991)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.27/0.53  % (28980)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.27/0.53  % (28992)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.27/0.53  % (28979)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.27/0.53  % (28979)Refutation not found, incomplete strategy% (28979)------------------------------
% 1.27/0.53  % (28979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (28979)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (28979)Memory used [KB]: 10618
% 1.27/0.53  % (28979)Time elapsed: 0.110 s
% 1.27/0.53  % (28979)------------------------------
% 1.27/0.53  % (28979)------------------------------
% 1.27/0.53  % (28993)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.27/0.53  % (28975)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.27/0.53  % (28970)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.42/0.54  % (28988)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.42/0.54  % (28986)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.42/0.54  % (28985)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.42/0.54  % (28977)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.42/0.54  % (28987)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.42/0.54  % (28975)Refutation not found, incomplete strategy% (28975)------------------------------
% 1.42/0.54  % (28975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (28975)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (28975)Memory used [KB]: 1791
% 1.42/0.54  % (28975)Time elapsed: 0.121 s
% 1.42/0.54  % (28975)------------------------------
% 1.42/0.54  % (28975)------------------------------
% 2.15/0.65  % (28977)Refutation not found, incomplete strategy% (28977)------------------------------
% 2.15/0.65  % (28977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.65  % (28977)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.65  
% 2.15/0.65  % (28977)Memory used [KB]: 6140
% 2.15/0.65  % (28977)Time elapsed: 0.240 s
% 2.15/0.65  % (28977)------------------------------
% 2.15/0.65  % (28977)------------------------------
% 2.64/0.69  % (28991)Refutation found. Thanks to Tanya!
% 2.64/0.69  % SZS status Theorem for theBenchmark
% 2.64/0.69  % SZS output start Proof for theBenchmark
% 2.64/0.69  fof(f6047,plain,(
% 2.64/0.69    $false),
% 2.64/0.69    inference(avatar_sat_refutation,[],[f105,f110,f115,f120,f127,f146,f214,f245,f258,f284,f289,f348,f380,f385,f441,f465,f467,f472,f483,f520,f525,f546,f632,f842,f867,f873,f994,f1102,f1113,f1158,f1167,f1179,f1180,f1181,f1318,f1356,f1362,f1554,f1596,f2498,f2990,f2992,f2993,f3018,f3027,f3471,f3480,f3709,f3876,f3951,f3965,f4637,f4646,f4913,f5251,f5883,f6035])).
% 2.64/0.69  fof(f6035,plain,(
% 2.64/0.69    ~spl3_3 | spl3_12 | ~spl3_16 | ~spl3_22 | ~spl3_26 | ~spl3_27 | ~spl3_28 | ~spl3_30 | ~spl3_57 | spl3_61 | ~spl3_85 | ~spl3_281 | ~spl3_313),
% 2.64/0.69    inference(avatar_contradiction_clause,[],[f6034])).
% 2.64/0.69  fof(f6034,plain,(
% 2.64/0.69    $false | (~spl3_3 | spl3_12 | ~spl3_16 | ~spl3_22 | ~spl3_26 | ~spl3_27 | ~spl3_28 | ~spl3_30 | ~spl3_57 | spl3_61 | ~spl3_85 | ~spl3_281 | ~spl3_313)),
% 2.64/0.69    inference(subsumption_resolution,[],[f6033,f5395])).
% 2.64/0.69  fof(f5395,plain,(
% 2.64/0.69    v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0) | (~spl3_3 | ~spl3_30 | ~spl3_85 | ~spl3_281)),
% 2.64/0.69    inference(subsumption_resolution,[],[f5394,f1317])).
% 2.64/0.69  fof(f1317,plain,(
% 2.64/0.69    m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_85),
% 2.64/0.69    inference(avatar_component_clause,[],[f1315])).
% 2.64/0.69  fof(f1315,plain,(
% 2.64/0.69    spl3_85 <=> m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).
% 2.64/0.69  fof(f5394,plain,(
% 2.64/0.69    ~m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0) | (~spl3_3 | ~spl3_30 | ~spl3_281)),
% 2.64/0.69    inference(forward_demodulation,[],[f5393,f519])).
% 2.64/0.69  fof(f519,plain,(
% 2.64/0.69    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_30),
% 2.64/0.69    inference(avatar_component_clause,[],[f517])).
% 2.64/0.69  fof(f517,plain,(
% 2.64/0.69    spl3_30 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 2.64/0.69  fof(f5393,plain,(
% 2.64/0.69    v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0) | ~m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_3 | ~spl3_281)),
% 2.64/0.69    inference(subsumption_resolution,[],[f5387,f114])).
% 2.64/0.69  fof(f114,plain,(
% 2.64/0.69    l1_pre_topc(sK0) | ~spl3_3),
% 2.64/0.69    inference(avatar_component_clause,[],[f112])).
% 2.64/0.69  fof(f112,plain,(
% 2.64/0.69    spl3_3 <=> l1_pre_topc(sK0)),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.64/0.69  fof(f5387,plain,(
% 2.64/0.69    v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0) | ~m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_281),
% 2.64/0.69    inference(resolution,[],[f5250,f76])).
% 2.64/0.69  fof(f76,plain,(
% 2.64/0.69    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.64/0.69    inference(cnf_transformation,[],[f51])).
% 2.64/0.69  fof(f51,plain,(
% 2.64/0.69    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.64/0.69    inference(nnf_transformation,[],[f25])).
% 2.64/0.69  fof(f25,plain,(
% 2.64/0.69    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.64/0.69    inference(ennf_transformation,[],[f6])).
% 2.64/0.69  fof(f6,axiom,(
% 2.64/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 2.64/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 2.64/0.69  fof(f5250,plain,(
% 2.64/0.69    r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),u1_pre_topc(sK0)) | ~spl3_281),
% 2.64/0.69    inference(avatar_component_clause,[],[f5248])).
% 2.64/0.69  fof(f5248,plain,(
% 2.64/0.69    spl3_281 <=> r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),u1_pre_topc(sK0))),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_281])])).
% 2.64/0.69  fof(f6033,plain,(
% 2.64/0.69    ~v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0) | (~spl3_3 | spl3_12 | ~spl3_16 | ~spl3_22 | ~spl3_26 | ~spl3_27 | ~spl3_28 | ~spl3_30 | ~spl3_57 | spl3_61 | ~spl3_313)),
% 2.64/0.69    inference(forward_demodulation,[],[f6032,f5884])).
% 2.64/0.69  fof(f5884,plain,(
% 2.64/0.69    sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) | (~spl3_28 | ~spl3_313)),
% 2.64/0.69    inference(superposition,[],[f5882,f473])).
% 2.64/0.69  fof(f473,plain,(
% 2.64/0.69    ( ! [X0] : (k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),X0)) ) | ~spl3_28),
% 2.64/0.69    inference(unit_resulting_resolution,[],[f471,f97])).
% 2.64/0.69  fof(f97,plain,(
% 2.64/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 2.64/0.69    inference(cnf_transformation,[],[f41])).
% 2.64/0.69  fof(f41,plain,(
% 2.64/0.69    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.64/0.69    inference(ennf_transformation,[],[f3])).
% 2.64/0.69  fof(f3,axiom,(
% 2.64/0.69    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 2.64/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 2.64/0.69  fof(f471,plain,(
% 2.64/0.69    m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~spl3_28),
% 2.64/0.69    inference(avatar_component_clause,[],[f469])).
% 2.64/0.69  fof(f469,plain,(
% 2.64/0.69    spl3_28 <=> m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 2.64/0.69  fof(f5882,plain,(
% 2.64/0.69    sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) | ~spl3_313),
% 2.64/0.69    inference(avatar_component_clause,[],[f5880])).
% 2.64/0.69  fof(f5880,plain,(
% 2.64/0.69    spl3_313 <=> sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_313])])).
% 2.64/0.69  fof(f6032,plain,(
% 2.64/0.69    ~v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) | (~spl3_3 | spl3_12 | ~spl3_16 | ~spl3_22 | ~spl3_26 | ~spl3_27 | ~spl3_28 | ~spl3_30 | ~spl3_57 | spl3_61)),
% 2.64/0.69    inference(subsumption_resolution,[],[f6031,f454])).
% 2.64/0.69  fof(f454,plain,(
% 2.64/0.69    v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~spl3_27),
% 2.64/0.69    inference(avatar_component_clause,[],[f452])).
% 2.64/0.69  fof(f452,plain,(
% 2.64/0.69    spl3_27 <=> v1_funct_1(k6_partfun1(k2_struct_0(sK0)))),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 2.64/0.69  fof(f6031,plain,(
% 2.64/0.69    ~v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | (~spl3_3 | spl3_12 | ~spl3_16 | ~spl3_22 | ~spl3_26 | ~spl3_28 | ~spl3_30 | ~spl3_57 | spl3_61)),
% 2.64/0.69    inference(subsumption_resolution,[],[f6030,f219])).
% 2.64/0.69  fof(f219,plain,(
% 2.64/0.69    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | spl3_12),
% 2.64/0.69    inference(avatar_component_clause,[],[f217])).
% 2.64/0.69  fof(f217,plain,(
% 2.64/0.69    spl3_12 <=> v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.64/0.69  fof(f6030,plain,(
% 2.64/0.69    ~v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_26 | ~spl3_28 | ~spl3_30 | ~spl3_57 | spl3_61)),
% 2.64/0.69    inference(subsumption_resolution,[],[f6029,f471])).
% 2.64/0.69  fof(f6029,plain,(
% 2.64/0.69    ~v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_26 | ~spl3_28 | ~spl3_30 | ~spl3_57 | spl3_61)),
% 2.64/0.69    inference(subsumption_resolution,[],[f6017,f440])).
% 2.64/0.69  fof(f440,plain,(
% 2.64/0.69    v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl3_26),
% 2.64/0.69    inference(avatar_component_clause,[],[f438])).
% 2.64/0.69  fof(f438,plain,(
% 2.64/0.69    spl3_26 <=> v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 2.64/0.69  fof(f6017,plain,(
% 2.64/0.69    ~v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_57 | spl3_61)),
% 2.64/0.69    inference(superposition,[],[f4912,f473])).
% 2.64/0.69  fof(f4912,plain,(
% 2.64/0.69    ( ! [X1] : (~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1)) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_57 | spl3_61)),
% 2.64/0.69    inference(subsumption_resolution,[],[f4895,f865])).
% 2.64/0.69  fof(f865,plain,(
% 2.64/0.69    k1_xboole_0 != k2_struct_0(sK0) | spl3_61),
% 2.64/0.69    inference(avatar_component_clause,[],[f864])).
% 2.64/0.69  fof(f864,plain,(
% 2.64/0.69    spl3_61 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 2.64/0.69  fof(f4895,plain,(
% 2.64/0.69    ( ! [X1] : (~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | k1_xboole_0 = k2_struct_0(sK0) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1)) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_57)),
% 2.64/0.69    inference(forward_demodulation,[],[f4894,f384])).
% 2.64/0.69  fof(f384,plain,(
% 2.64/0.69    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0) | ~spl3_22),
% 2.64/0.69    inference(avatar_component_clause,[],[f382])).
% 2.64/0.69  fof(f382,plain,(
% 2.64/0.69    spl3_22 <=> u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0)),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 2.64/0.69  fof(f4894,plain,(
% 2.64/0.69    ( ! [X1] : (~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | k1_xboole_0 = k2_struct_0(sK0) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0)) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_57)),
% 2.64/0.69    inference(forward_demodulation,[],[f4893,f384])).
% 2.64/0.69  fof(f4893,plain,(
% 2.64/0.69    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | k1_xboole_0 = k2_struct_0(sK0) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(X1) | ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0)) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_57)),
% 2.64/0.69    inference(forward_demodulation,[],[f4892,f384])).
% 2.64/0.69  fof(f4892,plain,(
% 2.64/0.69    ( ! [X1] : (k1_xboole_0 = k2_struct_0(sK0) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(X1) | ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0)) ) | (~spl3_3 | ~spl3_16 | ~spl3_30 | ~spl3_57)),
% 2.64/0.69    inference(forward_demodulation,[],[f2070,f841])).
% 2.64/0.69  fof(f841,plain,(
% 2.64/0.69    k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~spl3_57),
% 2.64/0.69    inference(avatar_component_clause,[],[f839])).
% 2.64/0.69  fof(f839,plain,(
% 2.64/0.69    spl3_57 <=> k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 2.64/0.69  fof(f2070,plain,(
% 2.64/0.69    ( ! [X1] : (v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(X1) | ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0)) ) | (~spl3_3 | ~spl3_16 | ~spl3_30)),
% 2.64/0.69    inference(resolution,[],[f555,f283])).
% 2.64/0.69  fof(f283,plain,(
% 2.64/0.69    l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~spl3_16),
% 2.64/0.69    inference(avatar_component_clause,[],[f281])).
% 2.64/0.69  fof(f281,plain,(
% 2.64/0.69    spl3_16 <=> l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 2.64/0.69  fof(f555,plain,(
% 2.64/0.69    ( ! [X0,X1] : (~l1_pre_topc(X0) | v5_pre_topc(X1,sK0,X0) | k2_struct_0(X0) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1,sK2(sK0,X0,X1)),sK0)) ) | (~spl3_3 | ~spl3_30)),
% 2.64/0.69    inference(subsumption_resolution,[],[f548,f114])).
% 2.64/0.69  fof(f548,plain,(
% 2.64/0.69    ( ! [X0,X1] : (~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1,sK2(sK0,X0,X1)),sK0) | v5_pre_topc(X1,sK0,X0) | k2_struct_0(X0) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK0)) ) | ~spl3_30),
% 2.64/0.69    inference(superposition,[],[f73,f519])).
% 2.64/0.69  fof(f73,plain,(
% 2.64/0.69    ( ! [X2,X0,X1] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) | v5_pre_topc(X2,X0,X1) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.64/0.69    inference(cnf_transformation,[],[f50])).
% 2.64/0.69  fof(f50,plain,(
% 2.64/0.69    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) & v3_pre_topc(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.64/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).
% 2.64/0.69  fof(f49,plain,(
% 2.64/0.69    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) & v3_pre_topc(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.64/0.69    introduced(choice_axiom,[])).
% 2.64/0.69  fof(f48,plain,(
% 2.64/0.69    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.64/0.69    inference(rectify,[],[f47])).
% 2.64/0.69  fof(f47,plain,(
% 2.64/0.69    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.64/0.69    inference(nnf_transformation,[],[f24])).
% 2.64/0.69  fof(f24,plain,(
% 2.64/0.69    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.64/0.69    inference(flattening,[],[f23])).
% 2.64/0.69  fof(f23,plain,(
% 2.64/0.69    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.64/0.69    inference(ennf_transformation,[],[f8])).
% 2.64/0.69  fof(f8,axiom,(
% 2.64/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_struct_0(X1) = k1_xboole_0 => k2_struct_0(X0) = k1_xboole_0) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 2.64/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).
% 2.64/0.69  fof(f5883,plain,(
% 2.64/0.69    spl3_313 | ~spl3_85),
% 2.64/0.69    inference(avatar_split_clause,[],[f5001,f1315,f5880])).
% 2.64/0.69  fof(f5001,plain,(
% 2.64/0.69    sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) | ~spl3_85),
% 2.64/0.69    inference(unit_resulting_resolution,[],[f1317,f86])).
% 2.64/0.69  fof(f86,plain,(
% 2.64/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1) )),
% 2.64/0.69    inference(cnf_transformation,[],[f36])).
% 2.64/0.69  fof(f36,plain,(
% 2.64/0.69    ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.64/0.69    inference(ennf_transformation,[],[f4])).
% 2.64/0.69  fof(f4,axiom,(
% 2.64/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 2.64/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 2.64/0.69  fof(f5251,plain,(
% 2.64/0.69    spl3_281 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_16 | ~spl3_25 | ~spl3_80 | ~spl3_85),
% 2.64/0.69    inference(avatar_split_clause,[],[f5014,f1315,f1176,f427,f281,f124,f117,f112,f107,f102,f5248])).
% 2.64/0.69  fof(f102,plain,(
% 2.64/0.69    spl3_1 <=> v2_struct_0(sK0)),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.64/0.69  fof(f107,plain,(
% 2.64/0.69    spl3_2 <=> v2_pre_topc(sK0)),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.64/0.69  fof(f117,plain,(
% 2.64/0.69    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.64/0.69  fof(f124,plain,(
% 2.64/0.69    spl3_5 <=> l1_struct_0(sK0)),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.64/0.69  fof(f427,plain,(
% 2.64/0.69    spl3_25 <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 2.64/0.69  fof(f1176,plain,(
% 2.64/0.69    spl3_80 <=> v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).
% 2.64/0.69  fof(f5014,plain,(
% 2.64/0.69    r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),u1_pre_topc(sK0)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_16 | ~spl3_25 | ~spl3_80 | ~spl3_85)),
% 2.64/0.69    inference(forward_demodulation,[],[f4997,f429])).
% 2.64/0.69  fof(f429,plain,(
% 2.64/0.69    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~spl3_25),
% 2.64/0.69    inference(avatar_component_clause,[],[f427])).
% 2.64/0.69  fof(f4997,plain,(
% 2.64/0.69    r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k5_tmap_1(sK0,sK1)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_16 | ~spl3_80 | ~spl3_85)),
% 2.64/0.69    inference(unit_resulting_resolution,[],[f1178,f1317,f335])).
% 2.64/0.69  fof(f335,plain,(
% 2.64/0.69    ( ! [X7] : (r2_hidden(X7,k5_tmap_1(sK0,sK1)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X7,k6_tmap_1(sK0,sK1))) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_16)),
% 2.64/0.69    inference(forward_demodulation,[],[f334,f209])).
% 2.64/0.69  fof(f209,plain,(
% 2.64/0.69    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 2.64/0.69    inference(unit_resulting_resolution,[],[f104,f109,f114,f119,f82])).
% 2.64/0.69  fof(f82,plain,(
% 2.64/0.69    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 2.64/0.69    inference(cnf_transformation,[],[f31])).
% 2.64/0.69  fof(f31,plain,(
% 2.64/0.69    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.64/0.69    inference(flattening,[],[f30])).
% 2.64/0.69  fof(f30,plain,(
% 2.64/0.69    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.64/0.69    inference(ennf_transformation,[],[f14])).
% 2.64/0.69  fof(f14,axiom,(
% 2.64/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 2.64/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).
% 2.64/0.69  fof(f119,plain,(
% 2.64/0.69    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 2.64/0.69    inference(avatar_component_clause,[],[f117])).
% 2.64/0.69  fof(f109,plain,(
% 2.64/0.69    v2_pre_topc(sK0) | ~spl3_2),
% 2.64/0.69    inference(avatar_component_clause,[],[f107])).
% 2.64/0.69  fof(f104,plain,(
% 2.64/0.69    ~v2_struct_0(sK0) | spl3_1),
% 2.64/0.69    inference(avatar_component_clause,[],[f102])).
% 2.64/0.69  fof(f334,plain,(
% 2.64/0.69    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X7,k6_tmap_1(sK0,sK1)) | r2_hidden(X7,u1_pre_topc(k6_tmap_1(sK0,sK1)))) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_16)),
% 2.64/0.69    inference(forward_demodulation,[],[f325,f204])).
% 2.64/0.69  fof(f204,plain,(
% 2.64/0.69    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5)),
% 2.64/0.69    inference(forward_demodulation,[],[f202,f153])).
% 2.64/0.69  fof(f153,plain,(
% 2.64/0.69    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 2.64/0.69    inference(unit_resulting_resolution,[],[f126,f65])).
% 2.64/0.69  fof(f65,plain,(
% 2.64/0.69    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 2.64/0.69    inference(cnf_transformation,[],[f21])).
% 2.64/0.69  fof(f21,plain,(
% 2.64/0.69    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.64/0.69    inference(ennf_transformation,[],[f5])).
% 2.64/0.69  fof(f5,axiom,(
% 2.64/0.69    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.64/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 2.64/0.69  fof(f126,plain,(
% 2.64/0.69    l1_struct_0(sK0) | ~spl3_5),
% 2.64/0.69    inference(avatar_component_clause,[],[f124])).
% 2.64/0.69  fof(f202,plain,(
% 2.64/0.69    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 2.64/0.69    inference(unit_resulting_resolution,[],[f104,f109,f114,f119,f81])).
% 2.64/0.69  fof(f81,plain,(
% 2.64/0.69    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 2.64/0.69    inference(cnf_transformation,[],[f31])).
% 2.64/0.69  fof(f325,plain,(
% 2.64/0.69    ( ! [X7] : (~v3_pre_topc(X7,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | r2_hidden(X7,u1_pre_topc(k6_tmap_1(sK0,sK1)))) ) | ~spl3_16),
% 2.64/0.69    inference(resolution,[],[f283,f75])).
% 2.64/0.69  fof(f75,plain,(
% 2.64/0.69    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,u1_pre_topc(X0))) )),
% 2.64/0.69    inference(cnf_transformation,[],[f51])).
% 2.64/0.69  fof(f1178,plain,(
% 2.64/0.69    v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) | ~spl3_80),
% 2.64/0.69    inference(avatar_component_clause,[],[f1176])).
% 2.64/0.69  fof(f4913,plain,(
% 2.64/0.69    ~spl3_12 | spl3_8 | ~spl3_21),
% 2.64/0.69    inference(avatar_split_clause,[],[f3015,f377,f143,f217])).
% 2.64/0.69  fof(f143,plain,(
% 2.64/0.69    spl3_8 <=> v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.64/0.69  fof(f377,plain,(
% 2.64/0.69    spl3_21 <=> k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0))),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 2.64/0.69  fof(f3015,plain,(
% 2.64/0.69    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (spl3_8 | ~spl3_21)),
% 2.64/0.69    inference(forward_demodulation,[],[f144,f379])).
% 2.64/0.69  fof(f379,plain,(
% 2.64/0.69    k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0)) | ~spl3_21),
% 2.64/0.69    inference(avatar_component_clause,[],[f377])).
% 2.64/0.69  fof(f144,plain,(
% 2.64/0.69    ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | spl3_8),
% 2.64/0.69    inference(avatar_component_clause,[],[f143])).
% 2.64/0.69  fof(f4646,plain,(
% 2.64/0.69    ~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_89 | ~spl3_91 | spl3_216 | ~spl3_243 | ~spl3_268),
% 2.64/0.69    inference(avatar_contradiction_clause,[],[f4645])).
% 2.64/0.69  fof(f4645,plain,(
% 2.64/0.69    $false | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_89 | ~spl3_91 | spl3_216 | ~spl3_243 | ~spl3_268)),
% 2.64/0.69    inference(subsumption_resolution,[],[f4644,f1112])).
% 2.64/0.69  fof(f1112,plain,(
% 2.64/0.69    v1_funct_1(k6_partfun1(k1_xboole_0)) | ~spl3_75),
% 2.64/0.69    inference(avatar_component_clause,[],[f1110])).
% 2.64/0.69  fof(f1110,plain,(
% 2.64/0.69    spl3_75 <=> v1_funct_1(k6_partfun1(k1_xboole_0))),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 2.64/0.69  fof(f4644,plain,(
% 2.64/0.69    ~v1_funct_1(k6_partfun1(k1_xboole_0)) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_89 | ~spl3_91 | spl3_216 | ~spl3_243 | ~spl3_268)),
% 2.64/0.69    inference(subsumption_resolution,[],[f4643,f3474])).
% 2.64/0.69  fof(f3474,plain,(
% 2.64/0.69    ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0) | spl3_216),
% 2.64/0.69    inference(avatar_component_clause,[],[f3473])).
% 2.64/0.69  fof(f3473,plain,(
% 2.64/0.69    spl3_216 <=> v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0)),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_216])])).
% 2.64/0.69  fof(f4643,plain,(
% 2.64/0.69    v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_89 | ~spl3_91 | ~spl3_243 | ~spl3_268)),
% 2.64/0.69    inference(subsumption_resolution,[],[f4642,f1595])).
% 2.64/0.69  fof(f1595,plain,(
% 2.64/0.69    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_91),
% 2.64/0.69    inference(avatar_component_clause,[],[f1593])).
% 2.64/0.69  fof(f1593,plain,(
% 2.64/0.69    spl3_91 <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).
% 2.64/0.69  fof(f4642,plain,(
% 2.64/0.69    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_89 | ~spl3_243 | ~spl3_268)),
% 2.64/0.69    inference(subsumption_resolution,[],[f4641,f1553])).
% 2.64/0.69  fof(f1553,plain,(
% 2.64/0.69    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~spl3_89),
% 2.64/0.69    inference(avatar_component_clause,[],[f1551])).
% 2.64/0.69  fof(f1551,plain,(
% 2.64/0.69    spl3_89 <=> v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).
% 2.64/0.69  fof(f4641,plain,(
% 2.64/0.69    ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_243 | ~spl3_268)),
% 2.64/0.69    inference(subsumption_resolution,[],[f4640,f3964])).
% 2.64/0.69  fof(f3964,plain,(
% 2.64/0.69    v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),sK0) | ~spl3_243),
% 2.64/0.69    inference(avatar_component_clause,[],[f3962])).
% 2.64/0.69  fof(f3962,plain,(
% 2.64/0.69    spl3_243 <=> v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),sK0)),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_243])])).
% 2.64/0.69  fof(f4640,plain,(
% 2.64/0.69    ~v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),sK0) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_268)),
% 2.64/0.69    inference(superposition,[],[f1988,f4636])).
% 2.64/0.69  fof(f4636,plain,(
% 2.64/0.69    sK2(sK0,sK0,k6_partfun1(k1_xboole_0)) = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))) | ~spl3_268),
% 2.64/0.69    inference(avatar_component_clause,[],[f4634])).
% 2.64/0.69  fof(f4634,plain,(
% 2.64/0.69    spl3_268 <=> sK2(sK0,sK0,k6_partfun1(k1_xboole_0)) = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0)))),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_268])])).
% 2.64/0.69  fof(f1988,plain,(
% 2.64/0.69    ( ! [X0] : (~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK2(sK0,sK0,X0)),sK0) | ~v1_funct_2(X0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.69    inference(forward_demodulation,[],[f1987,f866])).
% 2.64/0.69  fof(f866,plain,(
% 2.64/0.69    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_61),
% 2.64/0.69    inference(avatar_component_clause,[],[f864])).
% 2.64/0.69  fof(f1987,plain,(
% 2.64/0.69    ( ! [X0] : (~v1_funct_2(X0,k1_xboole_0,k2_struct_0(sK0)) | ~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK2(sK0,sK0,X0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.69    inference(forward_demodulation,[],[f1986,f519])).
% 2.64/0.69  fof(f1986,plain,(
% 2.64/0.69    ( ! [X0] : (~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK2(sK0,sK0,X0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.69    inference(forward_demodulation,[],[f1985,f866])).
% 2.64/0.69  fof(f1985,plain,(
% 2.64/0.69    ( ! [X0] : (~v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X0,sK2(sK0,sK0,X0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.69    inference(forward_demodulation,[],[f1984,f519])).
% 2.64/0.69  fof(f1984,plain,(
% 2.64/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),X0,sK2(sK0,sK0,X0)),sK0) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.69    inference(forward_demodulation,[],[f1983,f866])).
% 2.64/0.69  fof(f1983,plain,(
% 2.64/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),X0,sK2(sK0,sK0,X0)),sK0) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.69    inference(forward_demodulation,[],[f1979,f519])).
% 2.64/0.69  fof(f1979,plain,(
% 2.64/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0)))) | ~v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),X0,sK2(sK0,sK0,X0)),sK0) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.69    inference(resolution,[],[f1459,f114])).
% 2.64/0.69  fof(f1459,plain,(
% 2.64/0.69    ( ! [X24,X25] : (~l1_pre_topc(X24) | ~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X24)))) | ~v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0) | v5_pre_topc(X25,sK0,X24) | ~v1_funct_1(X25) | ~v1_funct_2(X25,k1_xboole_0,u1_struct_0(X24))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.69    inference(forward_demodulation,[],[f1458,f866])).
% 2.64/0.69  fof(f1458,plain,(
% 2.64/0.69    ( ! [X24,X25] : (~v1_funct_2(X25,k2_struct_0(sK0),u1_struct_0(X24)) | ~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X24)))) | ~v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0) | v5_pre_topc(X25,sK0,X24) | ~v1_funct_1(X25) | ~l1_pre_topc(X24)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.69    inference(forward_demodulation,[],[f1457,f519])).
% 2.64/0.69  fof(f1457,plain,(
% 2.64/0.69    ( ! [X24,X25] : (~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X24)))) | ~v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0) | v5_pre_topc(X25,sK0,X24) | ~v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24)) | ~v1_funct_1(X25) | ~l1_pre_topc(X24)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.69    inference(forward_demodulation,[],[f1456,f866])).
% 2.64/0.69  fof(f1456,plain,(
% 2.64/0.69    ( ! [X24,X25] : (~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X24)))) | ~v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0) | v5_pre_topc(X25,sK0,X24) | ~v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24)) | ~v1_funct_1(X25) | ~l1_pre_topc(X24)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.69    inference(forward_demodulation,[],[f1455,f519])).
% 2.64/0.69  fof(f1455,plain,(
% 2.64/0.69    ( ! [X24,X25] : (~v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0) | v5_pre_topc(X25,sK0,X24) | ~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X24)))) | ~v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24)) | ~v1_funct_1(X25) | ~l1_pre_topc(X24)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.69    inference(forward_demodulation,[],[f1454,f866])).
% 2.64/0.69  fof(f1454,plain,(
% 2.64/0.69    ( ! [X24,X25] : (~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0) | v5_pre_topc(X25,sK0,X24) | ~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X24)))) | ~v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24)) | ~v1_funct_1(X25) | ~l1_pre_topc(X24)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.69    inference(forward_demodulation,[],[f1453,f519])).
% 2.64/0.69  fof(f1453,plain,(
% 2.64/0.69    ( ! [X24,X25] : (~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0) | v5_pre_topc(X25,sK0,X24) | ~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X24)))) | ~v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24)) | ~v1_funct_1(X25) | ~l1_pre_topc(X24)) ) | (~spl3_3 | ~spl3_61)),
% 2.64/0.69    inference(subsumption_resolution,[],[f1444,f114])).
% 2.64/0.69  fof(f1444,plain,(
% 2.64/0.69    ( ! [X24,X25] : (~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0) | v5_pre_topc(X25,sK0,X24) | ~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X24)))) | ~v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24)) | ~v1_funct_1(X25) | ~l1_pre_topc(X24) | ~l1_pre_topc(sK0)) ) | ~spl3_61),
% 2.64/0.69    inference(trivial_inequality_removal,[],[f1439])).
% 2.64/0.69  fof(f1439,plain,(
% 2.64/0.69    ( ! [X24,X25] : (k1_xboole_0 != k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X24),X25,sK2(sK0,X24,X25)),sK0) | v5_pre_topc(X25,sK0,X24) | ~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X24)))) | ~v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24)) | ~v1_funct_1(X25) | ~l1_pre_topc(X24) | ~l1_pre_topc(sK0)) ) | ~spl3_61),
% 2.64/0.69    inference(superposition,[],[f74,f866])).
% 2.64/0.69  fof(f74,plain,(
% 2.64/0.69    ( ! [X2,X0,X1] : (k2_struct_0(X0) != k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.64/0.69    inference(cnf_transformation,[],[f50])).
% 2.64/0.69  fof(f4637,plain,(
% 2.64/0.69    spl3_268 | ~spl3_217),
% 2.64/0.69    inference(avatar_split_clause,[],[f3977,f3477,f4634])).
% 2.64/0.69  fof(f3477,plain,(
% 2.64/0.69    spl3_217 <=> m1_subset_1(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))),
% 2.64/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_217])])).
% 2.64/0.69  fof(f3977,plain,(
% 2.64/0.69    sK2(sK0,sK0,k6_partfun1(k1_xboole_0)) = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))) | ~spl3_217),
% 2.64/0.69    inference(unit_resulting_resolution,[],[f3479,f86])).
% 2.64/0.69  fof(f3479,plain,(
% 2.64/0.69    m1_subset_1(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | ~spl3_217),
% 2.64/0.69    inference(avatar_component_clause,[],[f3477])).
% 2.64/0.69  fof(f3965,plain,(
% 2.64/0.69    spl3_243 | ~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_89 | ~spl3_91 | spl3_216),
% 2.64/0.69    inference(avatar_split_clause,[],[f3959,f3473,f1593,f1551,f1110,f864,f517,f112,f3962])).
% 2.64/0.69  fof(f3959,plain,(
% 2.64/0.69    v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),sK0) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_89 | ~spl3_91 | spl3_216)),
% 2.64/0.69    inference(unit_resulting_resolution,[],[f1112,f1553,f1595,f3474,f1911])).
% 2.64/0.69  fof(f1911,plain,(
% 2.64/0.69    ( ! [X0] : (v3_pre_topc(sK2(sK0,sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(X0,k1_xboole_0,k1_xboole_0) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.69    inference(forward_demodulation,[],[f1910,f866])).
% 2.64/0.69  fof(f1910,plain,(
% 2.64/0.69    ( ! [X0] : (~v1_funct_2(X0,k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v3_pre_topc(sK2(sK0,sK0,X0),sK0) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.69    inference(forward_demodulation,[],[f1909,f519])).
% 2.64/0.70  fof(f1909,plain,(
% 2.64/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v3_pre_topc(sK2(sK0,sK0,X0),sK0) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1908,f866])).
% 2.64/0.70  fof(f1908,plain,(
% 2.64/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | v3_pre_topc(sK2(sK0,sK0,X0),sK0) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1904,f519])).
% 2.64/0.70  fof(f1904,plain,(
% 2.64/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0)))) | v3_pre_topc(sK2(sK0,sK0,X0),sK0) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(resolution,[],[f1469,f114])).
% 2.64/0.70  fof(f1469,plain,(
% 2.64/0.70    ( ! [X28,X29] : (~l1_pre_topc(X28) | ~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X28)))) | v3_pre_topc(sK2(sK0,X28,X29),X28) | v5_pre_topc(X29,sK0,X28) | ~v1_funct_1(X29) | ~v1_funct_2(X29,k1_xboole_0,u1_struct_0(X28))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1468,f866])).
% 2.64/0.70  fof(f1468,plain,(
% 2.64/0.70    ( ! [X28,X29] : (~v1_funct_2(X29,k2_struct_0(sK0),u1_struct_0(X28)) | ~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X28)))) | v3_pre_topc(sK2(sK0,X28,X29),X28) | v5_pre_topc(X29,sK0,X28) | ~v1_funct_1(X29) | ~l1_pre_topc(X28)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1467,f519])).
% 2.64/0.70  fof(f1467,plain,(
% 2.64/0.70    ( ! [X28,X29] : (~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X28)))) | v3_pre_topc(sK2(sK0,X28,X29),X28) | v5_pre_topc(X29,sK0,X28) | ~v1_funct_2(X29,u1_struct_0(sK0),u1_struct_0(X28)) | ~v1_funct_1(X29) | ~l1_pre_topc(X28)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1466,f866])).
% 2.64/0.70  fof(f1466,plain,(
% 2.64/0.70    ( ! [X28,X29] : (~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X28)))) | v3_pre_topc(sK2(sK0,X28,X29),X28) | v5_pre_topc(X29,sK0,X28) | ~v1_funct_2(X29,u1_struct_0(sK0),u1_struct_0(X28)) | ~v1_funct_1(X29) | ~l1_pre_topc(X28)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1465,f519])).
% 2.64/0.70  fof(f1465,plain,(
% 2.64/0.70    ( ! [X28,X29] : (v3_pre_topc(sK2(sK0,X28,X29),X28) | v5_pre_topc(X29,sK0,X28) | ~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X28)))) | ~v1_funct_2(X29,u1_struct_0(sK0),u1_struct_0(X28)) | ~v1_funct_1(X29) | ~l1_pre_topc(X28)) ) | (~spl3_3 | ~spl3_61)),
% 2.64/0.70    inference(subsumption_resolution,[],[f1442,f114])).
% 2.64/0.70  fof(f1442,plain,(
% 2.64/0.70    ( ! [X28,X29] : (v3_pre_topc(sK2(sK0,X28,X29),X28) | v5_pre_topc(X29,sK0,X28) | ~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X28)))) | ~v1_funct_2(X29,u1_struct_0(sK0),u1_struct_0(X28)) | ~v1_funct_1(X29) | ~l1_pre_topc(X28) | ~l1_pre_topc(sK0)) ) | ~spl3_61),
% 2.64/0.70    inference(trivial_inequality_removal,[],[f1441])).
% 2.64/0.70  fof(f1441,plain,(
% 2.64/0.70    ( ! [X28,X29] : (k1_xboole_0 != k1_xboole_0 | v3_pre_topc(sK2(sK0,X28,X29),X28) | v5_pre_topc(X29,sK0,X28) | ~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X28)))) | ~v1_funct_2(X29,u1_struct_0(sK0),u1_struct_0(X28)) | ~v1_funct_1(X29) | ~l1_pre_topc(X28) | ~l1_pre_topc(sK0)) ) | ~spl3_61),
% 2.64/0.70    inference(superposition,[],[f72,f866])).
% 2.64/0.70  fof(f72,plain,(
% 2.64/0.70    ( ! [X2,X0,X1] : (k2_struct_0(X0) != k1_xboole_0 | v3_pre_topc(sK2(X0,X1,X2),X1) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.64/0.70    inference(cnf_transformation,[],[f50])).
% 2.64/0.70  fof(f3951,plain,(
% 2.64/0.70    ~spl3_3 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_89 | ~spl3_91 | spl3_135 | ~spl3_157 | ~spl3_216 | ~spl3_241),
% 2.64/0.70    inference(avatar_contradiction_clause,[],[f3950])).
% 2.64/0.70  fof(f3950,plain,(
% 2.64/0.70    $false | (~spl3_3 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_89 | ~spl3_91 | spl3_135 | ~spl3_157 | ~spl3_216 | ~spl3_241)),
% 2.64/0.70    inference(subsumption_resolution,[],[f3949,f3875])).
% 2.64/0.70  fof(f3875,plain,(
% 2.64/0.70    v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0) | ~spl3_241),
% 2.64/0.70    inference(avatar_component_clause,[],[f3873])).
% 2.64/0.70  fof(f3873,plain,(
% 2.64/0.70    spl3_241 <=> v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0)),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_241])])).
% 2.64/0.70  fof(f3949,plain,(
% 2.64/0.70    ~v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0) | (~spl3_3 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_89 | ~spl3_91 | spl3_135 | ~spl3_157 | ~spl3_216)),
% 2.64/0.70    inference(subsumption_resolution,[],[f3941,f2497])).
% 2.64/0.70  fof(f2497,plain,(
% 2.64/0.70    m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | ~spl3_157),
% 2.64/0.70    inference(avatar_component_clause,[],[f2495])).
% 2.64/0.70  fof(f2495,plain,(
% 2.64/0.70    spl3_157 <=> m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_157])])).
% 2.64/0.70  fof(f3941,plain,(
% 2.64/0.70    ~m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | ~v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0) | (~spl3_3 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_89 | ~spl3_91 | spl3_135 | ~spl3_216)),
% 2.64/0.70    inference(resolution,[],[f3495,f2307])).
% 2.64/0.70  fof(f2307,plain,(
% 2.64/0.70    ~v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) | spl3_135),
% 2.64/0.70    inference(avatar_component_clause,[],[f2305])).
% 2.64/0.70  fof(f2305,plain,(
% 2.64/0.70    spl3_135 <=> v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_135])])).
% 2.64/0.70  fof(f3495,plain,(
% 2.64/0.70    ( ! [X1] : (v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~v3_pre_topc(X1,sK0)) ) | (~spl3_3 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_89 | ~spl3_91 | ~spl3_216)),
% 2.64/0.70    inference(subsumption_resolution,[],[f3494,f1553])).
% 2.64/0.70  fof(f3494,plain,(
% 2.64/0.70    ( ! [X1] : (~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,sK0)) ) | (~spl3_3 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_91 | ~spl3_216)),
% 2.64/0.70    inference(forward_demodulation,[],[f3493,f866])).
% 2.64/0.70  fof(f3493,plain,(
% 2.64/0.70    ( ! [X1] : (~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,sK0)) ) | (~spl3_3 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_91 | ~spl3_216)),
% 2.64/0.70    inference(forward_demodulation,[],[f3492,f519])).
% 2.64/0.70  fof(f3492,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,sK0) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_91 | ~spl3_216)),
% 2.64/0.70    inference(forward_demodulation,[],[f3491,f866])).
% 2.64/0.70  fof(f3491,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,sK0) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_91 | ~spl3_216)),
% 2.64/0.70    inference(forward_demodulation,[],[f3490,f519])).
% 2.64/0.70  fof(f3490,plain,(
% 2.64/0.70    ( ! [X1] : (v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_91 | ~spl3_216)),
% 2.64/0.70    inference(forward_demodulation,[],[f3489,f1418])).
% 2.64/0.70  fof(f1418,plain,(
% 2.64/0.70    ( ! [X16] : (k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X16) = k10_relat_1(k6_partfun1(k1_xboole_0),X16)) ) | (~spl3_28 | ~spl3_61)),
% 2.64/0.70    inference(superposition,[],[f473,f866])).
% 2.64/0.70  fof(f3489,plain,(
% 2.64/0.70    ( ! [X1] : (v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_91 | ~spl3_216)),
% 2.64/0.70    inference(forward_demodulation,[],[f3488,f866])).
% 2.64/0.70  fof(f3488,plain,(
% 2.64/0.70    ( ! [X1] : (v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_91 | ~spl3_216)),
% 2.64/0.70    inference(forward_demodulation,[],[f3487,f519])).
% 2.64/0.70  fof(f3487,plain,(
% 2.64/0.70    ( ! [X1] : (v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_91 | ~spl3_216)),
% 2.64/0.70    inference(subsumption_resolution,[],[f3486,f1595])).
% 2.64/0.70  fof(f3486,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_216)),
% 2.64/0.70    inference(forward_demodulation,[],[f3485,f866])).
% 2.64/0.70  fof(f3485,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_216)),
% 2.64/0.70    inference(forward_demodulation,[],[f3484,f519])).
% 2.64/0.70  fof(f3484,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_216)),
% 2.64/0.70    inference(subsumption_resolution,[],[f3483,f114])).
% 2.64/0.70  fof(f3483,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_216)),
% 2.64/0.70    inference(subsumption_resolution,[],[f3482,f1112])).
% 2.64/0.70  fof(f3482,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~l1_pre_topc(sK0)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_216)),
% 2.64/0.70    inference(resolution,[],[f3475,f1452])).
% 2.64/0.70  fof(f1452,plain,(
% 2.64/0.70    ( ! [X23,X21,X22] : (~v5_pre_topc(X23,sK0,X22) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X22)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0) | ~v3_pre_topc(X21,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v1_funct_2(X23,k1_xboole_0,u1_struct_0(X22)) | ~v1_funct_1(X23) | ~l1_pre_topc(X22)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1451,f866])).
% 2.64/0.70  fof(f1451,plain,(
% 2.64/0.70    ( ! [X23,X21,X22] : (~v1_funct_2(X23,k2_struct_0(sK0),u1_struct_0(X22)) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X22)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0) | ~v3_pre_topc(X21,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v5_pre_topc(X23,sK0,X22) | ~v1_funct_1(X23) | ~l1_pre_topc(X22)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1450,f519])).
% 2.64/0.70  fof(f1450,plain,(
% 2.64/0.70    ( ! [X23,X21,X22] : (~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X22)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0) | ~v3_pre_topc(X21,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v5_pre_topc(X23,sK0,X22) | ~v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~l1_pre_topc(X22)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1449,f866])).
% 2.64/0.70  fof(f1449,plain,(
% 2.64/0.70    ( ! [X23,X21,X22] : (~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X22)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0) | ~v3_pre_topc(X21,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v5_pre_topc(X23,sK0,X22) | ~v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~l1_pre_topc(X22)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1448,f519])).
% 2.64/0.70  fof(f1448,plain,(
% 2.64/0.70    ( ! [X23,X21,X22] : (v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0) | ~v3_pre_topc(X21,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v5_pre_topc(X23,sK0,X22) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22)))) | ~v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~l1_pre_topc(X22)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1447,f866])).
% 2.64/0.70  fof(f1447,plain,(
% 2.64/0.70    ( ! [X23,X21,X22] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X22),X23,X21),sK0) | ~v3_pre_topc(X21,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v5_pre_topc(X23,sK0,X22) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22)))) | ~v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~l1_pre_topc(X22)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1446,f519])).
% 2.64/0.70  fof(f1446,plain,(
% 2.64/0.70    ( ! [X23,X21,X22] : (~v3_pre_topc(X21,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v5_pre_topc(X23,sK0,X22) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X21),sK0) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22)))) | ~v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~l1_pre_topc(X22)) ) | (~spl3_3 | ~spl3_61)),
% 2.64/0.70    inference(subsumption_resolution,[],[f1445,f114])).
% 2.64/0.70  fof(f1445,plain,(
% 2.64/0.70    ( ! [X23,X21,X22] : (~v3_pre_topc(X21,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v5_pre_topc(X23,sK0,X22) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X21),sK0) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22)))) | ~v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~l1_pre_topc(X22) | ~l1_pre_topc(sK0)) ) | ~spl3_61),
% 2.64/0.70    inference(trivial_inequality_removal,[],[f1438])).
% 2.64/0.70  fof(f1438,plain,(
% 2.64/0.70    ( ! [X23,X21,X22] : (k1_xboole_0 != k1_xboole_0 | ~v3_pre_topc(X21,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v5_pre_topc(X23,sK0,X22) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X21),sK0) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22)))) | ~v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~l1_pre_topc(X22) | ~l1_pre_topc(sK0)) ) | ~spl3_61),
% 2.64/0.70    inference(superposition,[],[f68,f866])).
% 2.64/0.70  fof(f68,plain,(
% 2.64/0.70    ( ! [X4,X2,X0,X1] : (k2_struct_0(X0) != k1_xboole_0 | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.64/0.70    inference(cnf_transformation,[],[f50])).
% 2.64/0.70  fof(f3475,plain,(
% 2.64/0.70    v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0) | ~spl3_216),
% 2.64/0.70    inference(avatar_component_clause,[],[f3473])).
% 2.64/0.70  fof(f3876,plain,(
% 2.64/0.70    spl3_241 | ~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_157 | ~spl3_237),
% 2.64/0.70    inference(avatar_split_clause,[],[f3856,f3706,f2495,f864,f517,f112,f3873])).
% 2.64/0.70  fof(f3706,plain,(
% 2.64/0.70    spl3_237 <=> r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),u1_pre_topc(sK0))),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_237])])).
% 2.64/0.70  fof(f3856,plain,(
% 2.64/0.70    v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_157 | ~spl3_237)),
% 2.64/0.70    inference(subsumption_resolution,[],[f3855,f2497])).
% 2.64/0.70  fof(f3855,plain,(
% 2.64/0.70    ~m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_237)),
% 2.64/0.70    inference(forward_demodulation,[],[f3854,f866])).
% 2.64/0.70  fof(f3854,plain,(
% 2.64/0.70    ~m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0) | (~spl3_3 | ~spl3_30 | ~spl3_237)),
% 2.64/0.70    inference(forward_demodulation,[],[f3853,f519])).
% 2.64/0.70  fof(f3853,plain,(
% 2.64/0.70    v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0) | ~m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_3 | ~spl3_237)),
% 2.64/0.70    inference(subsumption_resolution,[],[f3846,f114])).
% 2.64/0.70  fof(f3846,plain,(
% 2.64/0.70    v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0) | ~m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_237),
% 2.64/0.70    inference(resolution,[],[f3708,f76])).
% 2.64/0.70  fof(f3708,plain,(
% 2.64/0.70    r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),u1_pre_topc(sK0)) | ~spl3_237),
% 2.64/0.70    inference(avatar_component_clause,[],[f3706])).
% 2.64/0.70  fof(f3709,plain,(
% 2.64/0.70    spl3_237 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_16 | ~spl3_25 | ~spl3_61 | ~spl3_133 | ~spl3_157),
% 2.64/0.70    inference(avatar_split_clause,[],[f3434,f2495,f2275,f864,f427,f281,f124,f117,f112,f107,f102,f3706])).
% 2.64/0.70  fof(f2275,plain,(
% 2.64/0.70    spl3_133 <=> v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1))),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_133])])).
% 2.64/0.70  fof(f3434,plain,(
% 2.64/0.70    r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),u1_pre_topc(sK0)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_16 | ~spl3_25 | ~spl3_61 | ~spl3_133 | ~spl3_157)),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f2277,f2497,f3050])).
% 2.64/0.70  fof(f3050,plain,(
% 2.64/0.70    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | r2_hidden(X2,u1_pre_topc(sK0)) | ~v3_pre_topc(X2,k6_tmap_1(sK0,sK1))) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_16 | ~spl3_25 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f3047,f866])).
% 2.64/0.70  fof(f3047,plain,(
% 2.64/0.70    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X2,u1_pre_topc(sK0)) | ~v3_pre_topc(X2,k6_tmap_1(sK0,sK1))) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_16 | ~spl3_25)),
% 2.64/0.70    inference(superposition,[],[f335,f429])).
% 2.64/0.70  fof(f2277,plain,(
% 2.64/0.70    v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1)) | ~spl3_133),
% 2.64/0.70    inference(avatar_component_clause,[],[f2275])).
% 2.64/0.70  fof(f3480,plain,(
% 2.64/0.70    spl3_216 | spl3_217 | ~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_89 | ~spl3_91),
% 2.64/0.70    inference(avatar_split_clause,[],[f2383,f1593,f1551,f1110,f864,f517,f112,f3477,f3473])).
% 2.64/0.70  fof(f2383,plain,(
% 2.64/0.70    m1_subset_1(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_89 | ~spl3_91)),
% 2.64/0.70    inference(subsumption_resolution,[],[f2382,f1112])).
% 2.64/0.70  fof(f2382,plain,(
% 2.64/0.70    m1_subset_1(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_89 | ~spl3_91)),
% 2.64/0.70    inference(subsumption_resolution,[],[f2381,f1595])).
% 2.64/0.70  fof(f2381,plain,(
% 2.64/0.70    m1_subset_1(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_89)),
% 2.64/0.70    inference(resolution,[],[f1950,f1553])).
% 2.64/0.70  fof(f1950,plain,(
% 2.64/0.70    ( ! [X0] : (~v1_funct_2(X0,k1_xboole_0,k1_xboole_0) | m1_subset_1(sK2(sK0,sK0,X0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1949,f866])).
% 2.64/0.70  fof(f1949,plain,(
% 2.64/0.70    ( ! [X0] : (~v1_funct_2(X0,k1_xboole_0,k2_struct_0(sK0)) | m1_subset_1(sK2(sK0,sK0,X0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1948,f519])).
% 2.64/0.70  fof(f1948,plain,(
% 2.64/0.70    ( ! [X0] : (m1_subset_1(sK2(sK0,sK0,X0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1947,f866])).
% 2.64/0.70  fof(f1947,plain,(
% 2.64/0.70    ( ! [X0] : (m1_subset_1(sK2(sK0,sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1946,f519])).
% 2.64/0.70  fof(f1946,plain,(
% 2.64/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | m1_subset_1(sK2(sK0,sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1945,f866])).
% 2.64/0.70  fof(f1945,plain,(
% 2.64/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | m1_subset_1(sK2(sK0,sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1941,f519])).
% 2.64/0.70  fof(f1941,plain,(
% 2.64/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0)))) | m1_subset_1(sK2(sK0,sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(resolution,[],[f1464,f114])).
% 2.64/0.70  fof(f1464,plain,(
% 2.64/0.70    ( ! [X26,X27] : (~l1_pre_topc(X26) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X26)))) | m1_subset_1(sK2(sK0,X26,X27),k1_zfmisc_1(u1_struct_0(X26))) | v5_pre_topc(X27,sK0,X26) | ~v1_funct_1(X27) | ~v1_funct_2(X27,k1_xboole_0,u1_struct_0(X26))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1463,f866])).
% 2.64/0.70  fof(f1463,plain,(
% 2.64/0.70    ( ! [X26,X27] : (~v1_funct_2(X27,k2_struct_0(sK0),u1_struct_0(X26)) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X26)))) | m1_subset_1(sK2(sK0,X26,X27),k1_zfmisc_1(u1_struct_0(X26))) | v5_pre_topc(X27,sK0,X26) | ~v1_funct_1(X27) | ~l1_pre_topc(X26)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1462,f519])).
% 2.64/0.70  fof(f1462,plain,(
% 2.64/0.70    ( ! [X26,X27] : (~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X26)))) | m1_subset_1(sK2(sK0,X26,X27),k1_zfmisc_1(u1_struct_0(X26))) | v5_pre_topc(X27,sK0,X26) | ~v1_funct_2(X27,u1_struct_0(sK0),u1_struct_0(X26)) | ~v1_funct_1(X27) | ~l1_pre_topc(X26)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1461,f866])).
% 2.64/0.70  fof(f1461,plain,(
% 2.64/0.70    ( ! [X26,X27] : (~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X26)))) | m1_subset_1(sK2(sK0,X26,X27),k1_zfmisc_1(u1_struct_0(X26))) | v5_pre_topc(X27,sK0,X26) | ~v1_funct_2(X27,u1_struct_0(sK0),u1_struct_0(X26)) | ~v1_funct_1(X27) | ~l1_pre_topc(X26)) ) | (~spl3_3 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1460,f519])).
% 2.64/0.70  fof(f1460,plain,(
% 2.64/0.70    ( ! [X26,X27] : (m1_subset_1(sK2(sK0,X26,X27),k1_zfmisc_1(u1_struct_0(X26))) | v5_pre_topc(X27,sK0,X26) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X26)))) | ~v1_funct_2(X27,u1_struct_0(sK0),u1_struct_0(X26)) | ~v1_funct_1(X27) | ~l1_pre_topc(X26)) ) | (~spl3_3 | ~spl3_61)),
% 2.64/0.70    inference(subsumption_resolution,[],[f1443,f114])).
% 2.64/0.70  fof(f1443,plain,(
% 2.64/0.70    ( ! [X26,X27] : (m1_subset_1(sK2(sK0,X26,X27),k1_zfmisc_1(u1_struct_0(X26))) | v5_pre_topc(X27,sK0,X26) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X26)))) | ~v1_funct_2(X27,u1_struct_0(sK0),u1_struct_0(X26)) | ~v1_funct_1(X27) | ~l1_pre_topc(X26) | ~l1_pre_topc(sK0)) ) | ~spl3_61),
% 2.64/0.70    inference(trivial_inequality_removal,[],[f1440])).
% 2.64/0.70  fof(f1440,plain,(
% 2.64/0.70    ( ! [X26,X27] : (k1_xboole_0 != k1_xboole_0 | m1_subset_1(sK2(sK0,X26,X27),k1_zfmisc_1(u1_struct_0(X26))) | v5_pre_topc(X27,sK0,X26) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X26)))) | ~v1_funct_2(X27,u1_struct_0(sK0),u1_struct_0(X26)) | ~v1_funct_1(X27) | ~l1_pre_topc(X26) | ~l1_pre_topc(sK0)) ) | ~spl3_61),
% 2.64/0.70    inference(superposition,[],[f70,f866])).
% 2.64/0.70  fof(f70,plain,(
% 2.64/0.70    ( ! [X2,X0,X1] : (k2_struct_0(X0) != k1_xboole_0 | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.64/0.70    inference(cnf_transformation,[],[f50])).
% 2.64/0.70  fof(f3471,plain,(
% 2.64/0.70    ~spl3_135 | ~spl3_3 | spl3_8 | ~spl3_16 | ~spl3_21 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_89 | ~spl3_91),
% 2.64/0.70    inference(avatar_split_clause,[],[f3021,f1593,f1551,f1110,f864,f517,f469,f382,f377,f281,f143,f112,f2305])).
% 2.64/0.70  fof(f3021,plain,(
% 2.64/0.70    ~v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) | (~spl3_3 | spl3_8 | ~spl3_16 | ~spl3_21 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_89 | ~spl3_91)),
% 2.64/0.70    inference(subsumption_resolution,[],[f3004,f3016])).
% 2.64/0.70  fof(f3016,plain,(
% 2.64/0.70    ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | (spl3_8 | ~spl3_21 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f3015,f866])).
% 2.64/0.70  fof(f3004,plain,(
% 2.64/0.70    ~v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_89 | ~spl3_91)),
% 2.64/0.70    inference(subsumption_resolution,[],[f3003,f1112])).
% 2.64/0.70  fof(f3003,plain,(
% 2.64/0.70    ~v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_89 | ~spl3_91)),
% 2.64/0.70    inference(subsumption_resolution,[],[f3002,f1595])).
% 2.64/0.70  fof(f3002,plain,(
% 2.64/0.70    ~v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_89)),
% 2.64/0.70    inference(subsumption_resolution,[],[f2434,f1553])).
% 2.64/0.70  fof(f2434,plain,(
% 2.64/0.70    ~v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(superposition,[],[f1994,f1418])).
% 2.64/0.70  fof(f1994,plain,(
% 2.64/0.70    ( ! [X1] : (~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0) | ~v1_funct_2(X1,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1)) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1993,f866])).
% 2.64/0.70  fof(f1993,plain,(
% 2.64/0.70    ( ! [X1] : (~v1_funct_2(X1,k1_xboole_0,k2_struct_0(sK0)) | ~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1)) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1992,f384])).
% 2.64/0.70  fof(f1992,plain,(
% 2.64/0.70    ( ! [X1] : (~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1991,f866])).
% 2.64/0.70  fof(f1991,plain,(
% 2.64/0.70    ( ! [X1] : (~v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1990,f384])).
% 2.64/0.70  fof(f1990,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1989,f866])).
% 2.64/0.70  fof(f1989,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1980,f384])).
% 2.64/0.70  fof(f1980,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X1,sK2(sK0,k6_tmap_1(sK0,sK1),X1)),sK0) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(resolution,[],[f1459,f283])).
% 2.64/0.70  fof(f3027,plain,(
% 2.64/0.70    ~spl3_86 | spl3_8 | ~spl3_21 | ~spl3_61),
% 2.64/0.70    inference(avatar_split_clause,[],[f3016,f864,f377,f143,f1380])).
% 2.64/0.70  fof(f1380,plain,(
% 2.64/0.70    spl3_86 <=> v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).
% 2.64/0.70  fof(f3018,plain,(
% 2.64/0.70    ~spl3_3 | spl3_8 | ~spl3_16 | ~spl3_21 | ~spl3_22 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_89 | ~spl3_91 | spl3_133),
% 2.64/0.70    inference(avatar_contradiction_clause,[],[f3017])).
% 2.64/0.70  fof(f3017,plain,(
% 2.64/0.70    $false | (~spl3_3 | spl3_8 | ~spl3_16 | ~spl3_21 | ~spl3_22 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_89 | ~spl3_91 | spl3_133)),
% 2.64/0.70    inference(subsumption_resolution,[],[f3016,f3007])).
% 2.64/0.70  fof(f3007,plain,(
% 2.64/0.70    v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_89 | ~spl3_91 | spl3_133)),
% 2.64/0.70    inference(subsumption_resolution,[],[f3006,f1112])).
% 2.64/0.70  fof(f3006,plain,(
% 2.64/0.70    v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61 | ~spl3_89 | ~spl3_91 | spl3_133)),
% 2.64/0.70    inference(subsumption_resolution,[],[f3005,f1553])).
% 2.64/0.70  fof(f3005,plain,(
% 2.64/0.70    ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61 | ~spl3_91 | spl3_133)),
% 2.64/0.70    inference(subsumption_resolution,[],[f2967,f1595])).
% 2.64/0.70  fof(f2967,plain,(
% 2.64/0.70    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61 | spl3_133)),
% 2.64/0.70    inference(resolution,[],[f2276,f1915])).
% 2.64/0.70  fof(f1915,plain,(
% 2.64/0.70    ( ! [X1] : (v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(X1,k1_xboole_0,k1_xboole_0) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1)) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1914,f866])).
% 2.64/0.70  fof(f1914,plain,(
% 2.64/0.70    ( ! [X1] : (~v1_funct_2(X1,k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1)) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1913,f384])).
% 2.64/0.70  fof(f1913,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1912,f866])).
% 2.64/0.70  fof(f1912,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1905,f384])).
% 2.64/0.70  fof(f1905,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(resolution,[],[f1469,f283])).
% 2.64/0.70  fof(f2276,plain,(
% 2.64/0.70    ~v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1)) | spl3_133),
% 2.64/0.70    inference(avatar_component_clause,[],[f2275])).
% 2.64/0.70  fof(f2993,plain,(
% 2.64/0.70    k7_tmap_1(sK0,sK1) != k6_partfun1(k2_struct_0(sK0)) | k1_xboole_0 != k2_struct_0(sK0) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 2.64/0.70    introduced(theory_tautology_sat_conflict,[])).
% 2.64/0.70  fof(f2992,plain,(
% 2.64/0.70    k1_xboole_0 != k2_struct_0(sK0) | sK1 != k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1) | sK1 = k10_relat_1(k6_partfun1(k1_xboole_0),sK1)),
% 2.64/0.70    introduced(theory_tautology_sat_conflict,[])).
% 2.64/0.70  fof(f2990,plain,(
% 2.64/0.70    ~spl3_3 | spl3_6 | ~spl3_16 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_35 | ~spl3_61 | ~spl3_75 | ~spl3_78 | ~spl3_81 | ~spl3_86 | ~spl3_89 | ~spl3_91),
% 2.64/0.70    inference(avatar_contradiction_clause,[],[f2989])).
% 2.64/0.70  fof(f2989,plain,(
% 2.64/0.70    $false | (~spl3_3 | spl3_6 | ~spl3_16 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_35 | ~spl3_61 | ~spl3_75 | ~spl3_78 | ~spl3_81 | ~spl3_86 | ~spl3_89 | ~spl3_91)),
% 2.64/0.70    inference(subsumption_resolution,[],[f2988,f545])).
% 2.64/0.70  fof(f545,plain,(
% 2.64/0.70    v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) | ~spl3_35),
% 2.64/0.70    inference(avatar_component_clause,[],[f543])).
% 2.64/0.70  fof(f543,plain,(
% 2.64/0.70    spl3_35 <=> v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 2.64/0.70  fof(f2988,plain,(
% 2.64/0.70    ~v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) | (~spl3_3 | spl3_6 | ~spl3_16 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_78 | ~spl3_81 | ~spl3_86 | ~spl3_89 | ~spl3_91)),
% 2.64/0.70    inference(subsumption_resolution,[],[f2987,f1166])).
% 2.64/0.70  fof(f1166,plain,(
% 2.64/0.70    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | ~spl3_78),
% 2.64/0.70    inference(avatar_component_clause,[],[f1164])).
% 2.64/0.70  fof(f1164,plain,(
% 2.64/0.70    spl3_78 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 2.64/0.70  fof(f2987,plain,(
% 2.64/0.70    ~m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | ~v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) | (~spl3_3 | spl3_6 | ~spl3_16 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_81 | ~spl3_86 | ~spl3_89 | ~spl3_91)),
% 2.64/0.70    inference(subsumption_resolution,[],[f2981,f130])).
% 2.64/0.70  fof(f130,plain,(
% 2.64/0.70    ~v3_pre_topc(sK1,sK0) | spl3_6),
% 2.64/0.70    inference(avatar_component_clause,[],[f129])).
% 2.64/0.70  fof(f129,plain,(
% 2.64/0.70    spl3_6 <=> v3_pre_topc(sK1,sK0)),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.64/0.70  fof(f2981,plain,(
% 2.64/0.70    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | ~v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_81 | ~spl3_86 | ~spl3_89 | ~spl3_91)),
% 2.64/0.70    inference(superposition,[],[f2732,f1186])).
% 2.64/0.70  fof(f1186,plain,(
% 2.64/0.70    sK1 = k10_relat_1(k6_partfun1(k1_xboole_0),sK1) | ~spl3_81),
% 2.64/0.70    inference(avatar_component_clause,[],[f1184])).
% 2.64/0.70  fof(f1184,plain,(
% 2.64/0.70    spl3_81 <=> sK1 = k10_relat_1(k6_partfun1(k1_xboole_0),sK1)),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).
% 2.64/0.70  fof(f2732,plain,(
% 2.64/0.70    ( ! [X1] : (v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_86 | ~spl3_89 | ~spl3_91)),
% 2.64/0.70    inference(subsumption_resolution,[],[f2731,f1553])).
% 2.64/0.70  fof(f2731,plain,(
% 2.64/0.70    ( ! [X1] : (~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_86 | ~spl3_91)),
% 2.64/0.70    inference(forward_demodulation,[],[f2730,f866])).
% 2.64/0.70  fof(f2730,plain,(
% 2.64/0.70    ( ! [X1] : (~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_86 | ~spl3_91)),
% 2.64/0.70    inference(forward_demodulation,[],[f2729,f384])).
% 2.64/0.70  fof(f2729,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_86 | ~spl3_91)),
% 2.64/0.70    inference(forward_demodulation,[],[f2728,f866])).
% 2.64/0.70  fof(f2728,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_86 | ~spl3_91)),
% 2.64/0.70    inference(forward_demodulation,[],[f2727,f384])).
% 2.64/0.70  fof(f2727,plain,(
% 2.64/0.70    ( ! [X1] : (v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_28 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_86 | ~spl3_91)),
% 2.64/0.70    inference(forward_demodulation,[],[f2726,f1418])).
% 2.64/0.70  fof(f2726,plain,(
% 2.64/0.70    ( ! [X1] : (v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_86 | ~spl3_91)),
% 2.64/0.70    inference(forward_demodulation,[],[f2725,f866])).
% 2.64/0.70  fof(f2725,plain,(
% 2.64/0.70    ( ! [X1] : (v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_86 | ~spl3_91)),
% 2.64/0.70    inference(forward_demodulation,[],[f2724,f384])).
% 2.64/0.70  fof(f2724,plain,(
% 2.64/0.70    ( ! [X1] : (v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_86 | ~spl3_91)),
% 2.64/0.70    inference(subsumption_resolution,[],[f2723,f1595])).
% 2.64/0.70  fof(f2723,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_86)),
% 2.64/0.70    inference(forward_demodulation,[],[f2722,f866])).
% 2.64/0.70  fof(f2722,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_86)),
% 2.64/0.70    inference(forward_demodulation,[],[f2721,f384])).
% 2.64/0.70  fof(f2721,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_86)),
% 2.64/0.70    inference(subsumption_resolution,[],[f2720,f283])).
% 2.64/0.70  fof(f2720,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_75 | ~spl3_86)),
% 2.64/0.70    inference(subsumption_resolution,[],[f2719,f1112])).
% 2.64/0.70  fof(f2719,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X1),sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1))) ) | (~spl3_3 | ~spl3_30 | ~spl3_61 | ~spl3_86)),
% 2.64/0.70    inference(resolution,[],[f1381,f1452])).
% 2.64/0.70  fof(f1381,plain,(
% 2.64/0.70    v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~spl3_86),
% 2.64/0.70    inference(avatar_component_clause,[],[f1380])).
% 2.64/0.70  fof(f2498,plain,(
% 2.64/0.70    spl3_157 | ~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61 | ~spl3_75 | spl3_86 | ~spl3_89 | ~spl3_91),
% 2.64/0.70    inference(avatar_split_clause,[],[f2417,f1593,f1551,f1380,f1110,f864,f517,f382,f281,f112,f2495])).
% 2.64/0.70  fof(f2417,plain,(
% 2.64/0.70    m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61 | ~spl3_75 | spl3_86 | ~spl3_89 | ~spl3_91)),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f1112,f1553,f1382,f1595,f1956])).
% 2.64/0.70  fof(f1956,plain,(
% 2.64/0.70    ( ! [X1] : (~v1_funct_2(X1,k1_xboole_0,k1_xboole_0) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1)) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1955,f866])).
% 2.64/0.70  fof(f1955,plain,(
% 2.64/0.70    ( ! [X1] : (~v1_funct_2(X1,k1_xboole_0,k2_struct_0(sK0)) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1)) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1954,f384])).
% 2.64/0.70  fof(f1954,plain,(
% 2.64/0.70    ( ! [X1] : (m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1953,f866])).
% 2.64/0.70  fof(f1953,plain,(
% 2.64/0.70    ( ! [X1] : (m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1952,f384])).
% 2.64/0.70  fof(f1952,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1951,f866])).
% 2.64/0.70  fof(f1951,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_22 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(forward_demodulation,[],[f1942,f384])).
% 2.64/0.70  fof(f1942,plain,(
% 2.64/0.70    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | v5_pre_topc(X1,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))) ) | (~spl3_3 | ~spl3_16 | ~spl3_30 | ~spl3_61)),
% 2.64/0.70    inference(resolution,[],[f1464,f283])).
% 2.64/0.70  fof(f1382,plain,(
% 2.64/0.70    ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | spl3_86),
% 2.64/0.70    inference(avatar_component_clause,[],[f1380])).
% 2.64/0.70  fof(f1596,plain,(
% 2.64/0.70    spl3_91 | ~spl3_28 | ~spl3_61),
% 2.64/0.70    inference(avatar_split_clause,[],[f1417,f864,f469,f1593])).
% 2.64/0.70  fof(f1417,plain,(
% 2.64/0.70    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_28 | ~spl3_61)),
% 2.64/0.70    inference(superposition,[],[f471,f866])).
% 2.64/0.70  fof(f1554,plain,(
% 2.64/0.70    spl3_89 | ~spl3_26 | ~spl3_61),
% 2.64/0.70    inference(avatar_split_clause,[],[f1413,f864,f438,f1551])).
% 2.64/0.70  fof(f1413,plain,(
% 2.64/0.70    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | (~spl3_26 | ~spl3_61)),
% 2.64/0.70    inference(superposition,[],[f440,f866])).
% 2.64/0.70  fof(f1362,plain,(
% 2.64/0.70    spl3_6 | ~spl3_12 | ~spl3_26 | ~spl3_27 | ~spl3_28 | ~spl3_31 | ~spl3_35 | ~spl3_74 | ~spl3_77),
% 2.64/0.70    inference(avatar_contradiction_clause,[],[f1361])).
% 2.64/0.70  fof(f1361,plain,(
% 2.64/0.70    $false | (spl3_6 | ~spl3_12 | ~spl3_26 | ~spl3_27 | ~spl3_28 | ~spl3_31 | ~spl3_35 | ~spl3_74 | ~spl3_77)),
% 2.64/0.70    inference(subsumption_resolution,[],[f1360,f130])).
% 2.64/0.70  fof(f1360,plain,(
% 2.64/0.70    v3_pre_topc(sK1,sK0) | (~spl3_12 | ~spl3_26 | ~spl3_27 | ~spl3_28 | ~spl3_31 | ~spl3_35 | ~spl3_74 | ~spl3_77)),
% 2.64/0.70    inference(forward_demodulation,[],[f1359,f1157])).
% 2.64/0.70  fof(f1157,plain,(
% 2.64/0.70    sK1 = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1) | ~spl3_77),
% 2.64/0.70    inference(avatar_component_clause,[],[f1155])).
% 2.64/0.70  fof(f1155,plain,(
% 2.64/0.70    spl3_77 <=> sK1 = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1)),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 2.64/0.70  fof(f1359,plain,(
% 2.64/0.70    v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1),sK0) | (~spl3_12 | ~spl3_26 | ~spl3_27 | ~spl3_28 | ~spl3_31 | ~spl3_35 | ~spl3_74)),
% 2.64/0.70    inference(forward_demodulation,[],[f1357,f473])).
% 2.64/0.70  fof(f1357,plain,(
% 2.64/0.70    v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1),sK0) | (~spl3_12 | ~spl3_26 | ~spl3_27 | ~spl3_28 | ~spl3_31 | ~spl3_35 | ~spl3_74)),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f454,f524,f545,f440,f471,f218,f1101])).
% 2.64/0.70  fof(f1101,plain,(
% 2.64/0.70    ( ! [X0,X1] : (~v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0,X1),sK0)) ) | ~spl3_74),
% 2.64/0.70    inference(avatar_component_clause,[],[f1100])).
% 2.64/0.70  fof(f1100,plain,(
% 2.64/0.70    spl3_74 <=> ! [X1,X0] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | ~v1_funct_1(X0) | ~v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0,X1),sK0))),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 2.64/0.70  fof(f218,plain,(
% 2.64/0.70    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~spl3_12),
% 2.64/0.70    inference(avatar_component_clause,[],[f217])).
% 2.64/0.70  fof(f524,plain,(
% 2.64/0.70    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_31),
% 2.64/0.70    inference(avatar_component_clause,[],[f522])).
% 2.64/0.70  fof(f522,plain,(
% 2.64/0.70    spl3_31 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 2.64/0.70  fof(f1356,plain,(
% 2.64/0.70    spl3_12 | ~spl3_8 | ~spl3_21),
% 2.64/0.70    inference(avatar_split_clause,[],[f1338,f377,f143,f217])).
% 2.64/0.70  fof(f1338,plain,(
% 2.64/0.70    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl3_8 | ~spl3_21)),
% 2.64/0.70    inference(forward_demodulation,[],[f145,f379])).
% 2.64/0.70  fof(f145,plain,(
% 2.64/0.70    v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~spl3_8),
% 2.64/0.70    inference(avatar_component_clause,[],[f143])).
% 2.64/0.70  fof(f1318,plain,(
% 2.64/0.70    spl3_85 | spl3_12 | ~spl3_26 | ~spl3_27 | ~spl3_28 | ~spl3_62),
% 2.64/0.70    inference(avatar_split_clause,[],[f1017,f871,f469,f452,f438,f217,f1315])).
% 2.64/0.70  fof(f871,plain,(
% 2.64/0.70    spl3_62 <=> ! [X0] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))))),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 2.64/0.70  fof(f1017,plain,(
% 2.64/0.70    m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | (spl3_12 | ~spl3_26 | ~spl3_27 | ~spl3_28 | ~spl3_62)),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f454,f219,f440,f471,f872])).
% 2.64/0.70  fof(f872,plain,(
% 2.64/0.70    ( ! [X0] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))) ) | ~spl3_62),
% 2.64/0.70    inference(avatar_component_clause,[],[f871])).
% 2.64/0.70  fof(f1181,plain,(
% 2.64/0.70    k7_tmap_1(sK0,sK1) != k6_partfun1(k2_struct_0(sK0)) | u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(k6_tmap_1(sK0,sK1)) != k2_struct_0(sK0) | m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))),
% 2.64/0.70    introduced(theory_tautology_sat_conflict,[])).
% 2.64/0.70  fof(f1180,plain,(
% 2.64/0.70    k7_tmap_1(sK0,sK1) != k6_partfun1(k2_struct_0(sK0)) | u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(k6_tmap_1(sK0,sK1)) != k2_struct_0(sK0) | v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))),
% 2.64/0.70    introduced(theory_tautology_sat_conflict,[])).
% 2.64/0.70  fof(f1179,plain,(
% 2.64/0.70    spl3_80 | spl3_12 | ~spl3_26 | ~spl3_27 | ~spl3_28 | ~spl3_60),
% 2.64/0.70    inference(avatar_split_clause,[],[f868,f861,f469,f452,f438,f217,f1176])).
% 2.64/0.70  fof(f861,plain,(
% 2.64/0.70    spl3_60 <=> ! [X0] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))))),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 2.64/0.70  fof(f868,plain,(
% 2.64/0.70    v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) | (spl3_12 | ~spl3_26 | ~spl3_27 | ~spl3_28 | ~spl3_60)),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f454,f219,f440,f471,f862])).
% 2.64/0.70  fof(f862,plain,(
% 2.64/0.70    ( ! [X0] : (v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))) ) | ~spl3_60),
% 2.64/0.70    inference(avatar_component_clause,[],[f861])).
% 2.64/0.70  fof(f1167,plain,(
% 2.64/0.70    spl3_78 | ~spl3_72),
% 2.64/0.70    inference(avatar_split_clause,[],[f1106,f991,f1164])).
% 2.64/0.70  fof(f991,plain,(
% 2.64/0.70    spl3_72 <=> r1_tarski(sK1,k1_xboole_0)),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 2.64/0.70  fof(f1106,plain,(
% 2.64/0.70    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | ~spl3_72),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f993,f96])).
% 2.64/0.70  fof(f96,plain,(
% 2.64/0.70    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.64/0.70    inference(cnf_transformation,[],[f55])).
% 2.64/0.70  fof(f55,plain,(
% 2.64/0.70    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.64/0.70    inference(nnf_transformation,[],[f2])).
% 2.64/0.70  fof(f2,axiom,(
% 2.64/0.70    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.64/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.64/0.70  fof(f993,plain,(
% 2.64/0.70    r1_tarski(sK1,k1_xboole_0) | ~spl3_72),
% 2.64/0.70    inference(avatar_component_clause,[],[f991])).
% 2.64/0.70  fof(f1158,plain,(
% 2.64/0.70    spl3_77 | ~spl3_28 | ~spl3_29),
% 2.64/0.70    inference(avatar_split_clause,[],[f791,f480,f469,f1155])).
% 2.64/0.70  fof(f480,plain,(
% 2.64/0.70    spl3_29 <=> sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1)),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 2.64/0.70  fof(f791,plain,(
% 2.64/0.70    sK1 = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1) | (~spl3_28 | ~spl3_29)),
% 2.64/0.70    inference(superposition,[],[f473,f482])).
% 2.64/0.70  fof(f482,plain,(
% 2.64/0.70    sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1) | ~spl3_29),
% 2.64/0.70    inference(avatar_component_clause,[],[f480])).
% 2.64/0.70  fof(f1113,plain,(
% 2.64/0.70    spl3_75 | ~spl3_27 | ~spl3_61),
% 2.64/0.70    inference(avatar_split_clause,[],[f1042,f864,f452,f1110])).
% 2.64/0.70  fof(f1042,plain,(
% 2.64/0.70    v1_funct_1(k6_partfun1(k1_xboole_0)) | (~spl3_27 | ~spl3_61)),
% 2.64/0.70    inference(superposition,[],[f454,f866])).
% 2.64/0.70  fof(f1102,plain,(
% 2.64/0.70    spl3_74 | spl3_61 | ~spl3_3 | ~spl3_5 | ~spl3_16 | ~spl3_19 | ~spl3_22),
% 2.64/0.70    inference(avatar_split_clause,[],[f515,f382,f345,f281,f124,f112,f864,f1100])).
% 2.64/0.70  fof(f345,plain,(
% 2.64/0.70    spl3_19 <=> l1_struct_0(k6_tmap_1(sK0,sK1))),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 2.64/0.70  fof(f515,plain,(
% 2.64/0.70    ( ! [X0,X1] : (k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0,X1),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0)) ) | (~spl3_3 | ~spl3_5 | ~spl3_16 | ~spl3_19 | ~spl3_22)),
% 2.64/0.70    inference(forward_demodulation,[],[f514,f413])).
% 2.64/0.70  fof(f413,plain,(
% 2.64/0.70    k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1)) | (~spl3_19 | ~spl3_22)),
% 2.64/0.70    inference(forward_demodulation,[],[f411,f384])).
% 2.64/0.70  fof(f411,plain,(
% 2.64/0.70    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~spl3_19),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f347,f65])).
% 2.64/0.70  fof(f347,plain,(
% 2.64/0.70    l1_struct_0(k6_tmap_1(sK0,sK1)) | ~spl3_19),
% 2.64/0.70    inference(avatar_component_clause,[],[f345])).
% 2.64/0.70  fof(f514,plain,(
% 2.64/0.70    ( ! [X0,X1] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0,X1),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0)) ) | (~spl3_3 | ~spl3_5 | ~spl3_16 | ~spl3_22)),
% 2.64/0.70    inference(subsumption_resolution,[],[f513,f283])).
% 2.64/0.70  fof(f513,plain,(
% 2.64/0.70    ( ! [X0,X1] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0,X1),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1))) ) | (~spl3_3 | ~spl3_5 | ~spl3_22)),
% 2.64/0.70    inference(superposition,[],[f253,f384])).
% 2.64/0.70  fof(f253,plain,(
% 2.64/0.70    ( ! [X2,X0,X1] : (~v1_funct_2(X2,k2_struct_0(sK0),u1_struct_0(X1)) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X1),X2,X0),sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v3_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,sK0,X1) | k2_struct_0(X1) = k1_xboole_0 | ~v1_funct_1(X2) | ~l1_pre_topc(X1)) ) | (~spl3_3 | ~spl3_5)),
% 2.64/0.70    inference(forward_demodulation,[],[f252,f153])).
% 2.64/0.70  fof(f252,plain,(
% 2.64/0.70    ( ! [X2,X0,X1] : (~v1_funct_2(X2,k2_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v3_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,sK0,X1) | k2_struct_0(X1) = k1_xboole_0 | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X0),sK0)) ) | (~spl3_3 | ~spl3_5)),
% 2.64/0.70    inference(forward_demodulation,[],[f251,f153])).
% 2.64/0.70  fof(f251,plain,(
% 2.64/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v3_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,sK0,X1) | k2_struct_0(X1) = k1_xboole_0 | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X0),sK0)) ) | (~spl3_3 | ~spl3_5)),
% 2.64/0.70    inference(forward_demodulation,[],[f250,f153])).
% 2.64/0.70  fof(f250,plain,(
% 2.64/0.70    ( ! [X2,X0,X1] : (~v3_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,sK0,X1) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X0),sK0)) ) | ~spl3_3),
% 2.64/0.70    inference(resolution,[],[f67,f114])).
% 2.64/0.70  fof(f67,plain,(
% 2.64/0.70    ( ! [X4,X2,X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)) )),
% 2.64/0.70    inference(cnf_transformation,[],[f50])).
% 2.64/0.70  fof(f994,plain,(
% 2.64/0.70    spl3_72 | ~spl3_17 | ~spl3_61),
% 2.64/0.70    inference(avatar_split_clause,[],[f921,f864,f286,f991])).
% 2.64/0.70  fof(f286,plain,(
% 2.64/0.70    spl3_17 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 2.64/0.70  fof(f921,plain,(
% 2.64/0.70    r1_tarski(sK1,k1_xboole_0) | (~spl3_17 | ~spl3_61)),
% 2.64/0.70    inference(superposition,[],[f288,f866])).
% 2.64/0.70  fof(f288,plain,(
% 2.64/0.70    r1_tarski(sK1,k2_struct_0(sK0)) | ~spl3_17),
% 2.64/0.70    inference(avatar_component_clause,[],[f286])).
% 2.64/0.70  fof(f873,plain,(
% 2.64/0.70    spl3_62 | spl3_61 | ~spl3_3 | ~spl3_5 | ~spl3_16 | ~spl3_19 | ~spl3_22),
% 2.64/0.70    inference(avatar_split_clause,[],[f512,f382,f345,f281,f124,f112,f864,f871])).
% 2.64/0.70  fof(f512,plain,(
% 2.64/0.70    ( ! [X0] : (k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))) ) | (~spl3_3 | ~spl3_5 | ~spl3_16 | ~spl3_19 | ~spl3_22)),
% 2.64/0.70    inference(forward_demodulation,[],[f511,f413])).
% 2.64/0.70  fof(f511,plain,(
% 2.64/0.70    ( ! [X0] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))) ) | (~spl3_3 | ~spl3_5 | ~spl3_16 | ~spl3_22)),
% 2.64/0.70    inference(subsumption_resolution,[],[f510,f283])).
% 2.64/0.70  fof(f510,plain,(
% 2.64/0.70    ( ! [X0] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))) ) | (~spl3_3 | ~spl3_5 | ~spl3_22)),
% 2.64/0.70    inference(superposition,[],[f249,f384])).
% 2.64/0.70  fof(f249,plain,(
% 2.64/0.70    ( ! [X0,X1] : (~v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | m1_subset_1(sK2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k1_xboole_0 | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | v5_pre_topc(X1,sK0,X0)) ) | (~spl3_3 | ~spl3_5)),
% 2.64/0.70    inference(forward_demodulation,[],[f248,f153])).
% 2.64/0.70  fof(f248,plain,(
% 2.64/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | m1_subset_1(sK2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k1_xboole_0 | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | v5_pre_topc(X1,sK0,X0)) ) | (~spl3_3 | ~spl3_5)),
% 2.64/0.70    inference(forward_demodulation,[],[f247,f153])).
% 2.64/0.70  fof(f247,plain,(
% 2.64/0.70    ( ! [X0,X1] : (m1_subset_1(sK2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | v5_pre_topc(X1,sK0,X0)) ) | ~spl3_3),
% 2.64/0.70    inference(resolution,[],[f69,f114])).
% 2.64/0.70  fof(f69,plain,(
% 2.64/0.70    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | v5_pre_topc(X2,X0,X1)) )),
% 2.64/0.70    inference(cnf_transformation,[],[f50])).
% 2.64/0.70  fof(f867,plain,(
% 2.64/0.70    spl3_60 | spl3_61 | ~spl3_3 | ~spl3_5 | ~spl3_16 | ~spl3_19 | ~spl3_22),
% 2.64/0.70    inference(avatar_split_clause,[],[f509,f382,f345,f281,f124,f112,f864,f861])).
% 2.64/0.70  fof(f509,plain,(
% 2.64/0.70    ( ! [X0] : (k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))) ) | (~spl3_3 | ~spl3_5 | ~spl3_16 | ~spl3_19 | ~spl3_22)),
% 2.64/0.70    inference(forward_demodulation,[],[f508,f413])).
% 2.64/0.70  fof(f508,plain,(
% 2.64/0.70    ( ! [X0] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))) ) | (~spl3_3 | ~spl3_5 | ~spl3_16 | ~spl3_22)),
% 2.64/0.70    inference(subsumption_resolution,[],[f507,f283])).
% 2.64/0.70  fof(f507,plain,(
% 2.64/0.70    ( ! [X0] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),X0),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))) ) | (~spl3_3 | ~spl3_5 | ~spl3_22)),
% 2.64/0.70    inference(superposition,[],[f240,f384])).
% 2.64/0.70  fof(f240,plain,(
% 2.64/0.70    ( ! [X0,X1] : (~v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | v3_pre_topc(sK2(sK0,X0,X1),X0) | k2_struct_0(X0) = k1_xboole_0 | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | v5_pre_topc(X1,sK0,X0)) ) | (~spl3_3 | ~spl3_5)),
% 2.64/0.70    inference(forward_demodulation,[],[f239,f153])).
% 2.64/0.70  fof(f239,plain,(
% 2.64/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | v3_pre_topc(sK2(sK0,X0,X1),X0) | k2_struct_0(X0) = k1_xboole_0 | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | v5_pre_topc(X1,sK0,X0)) ) | (~spl3_3 | ~spl3_5)),
% 2.64/0.70    inference(forward_demodulation,[],[f238,f153])).
% 2.64/0.70  fof(f238,plain,(
% 2.64/0.70    ( ! [X0,X1] : (v3_pre_topc(sK2(sK0,X0,X1),X0) | k2_struct_0(X0) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | v5_pre_topc(X1,sK0,X0)) ) | ~spl3_3),
% 2.64/0.70    inference(resolution,[],[f71,f114])).
% 2.64/0.70  fof(f71,plain,(
% 2.64/0.70    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v3_pre_topc(sK2(X0,X1,X2),X1) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | v5_pre_topc(X2,X0,X1)) )),
% 2.64/0.70    inference(cnf_transformation,[],[f50])).
% 2.64/0.70  fof(f842,plain,(
% 2.64/0.70    spl3_57 | ~spl3_19 | ~spl3_22),
% 2.64/0.70    inference(avatar_split_clause,[],[f413,f382,f345,f839])).
% 2.64/0.70  fof(f632,plain,(
% 2.64/0.70    spl3_25 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_14),
% 2.64/0.70    inference(avatar_split_clause,[],[f290,f255,f117,f112,f107,f102,f427])).
% 2.64/0.70  fof(f255,plain,(
% 2.64/0.70    spl3_14 <=> r2_hidden(sK1,u1_pre_topc(sK0))),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.64/0.70  fof(f290,plain,(
% 2.64/0.70    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_14)),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f104,f109,f114,f119,f257,f83])).
% 2.64/0.70  fof(f83,plain,(
% 2.64/0.70    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.64/0.70    inference(cnf_transformation,[],[f52])).
% 2.64/0.70  fof(f52,plain,(
% 2.64/0.70    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.64/0.70    inference(nnf_transformation,[],[f33])).
% 2.64/0.70  fof(f33,plain,(
% 2.64/0.70    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.64/0.70    inference(flattening,[],[f32])).
% 2.64/0.70  fof(f32,plain,(
% 2.64/0.70    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.64/0.70    inference(ennf_transformation,[],[f13])).
% 2.64/0.70  fof(f13,axiom,(
% 2.64/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 2.64/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).
% 2.64/0.70  fof(f257,plain,(
% 2.64/0.70    r2_hidden(sK1,u1_pre_topc(sK0)) | ~spl3_14),
% 2.64/0.70    inference(avatar_component_clause,[],[f255])).
% 2.64/0.70  fof(f546,plain,(
% 2.64/0.70    spl3_35 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_17 | ~spl3_22),
% 2.64/0.70    inference(avatar_split_clause,[],[f504,f382,f286,f124,f112,f107,f102,f543])).
% 2.64/0.70  fof(f504,plain,(
% 2.64/0.70    v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_17 | ~spl3_22)),
% 2.64/0.70    inference(subsumption_resolution,[],[f503,f337])).
% 2.64/0.70  fof(f337,plain,(
% 2.64/0.70    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_17),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f288,f96])).
% 2.64/0.70  fof(f503,plain,(
% 2.64/0.70    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_22)),
% 2.64/0.70    inference(duplicate_literal_removal,[],[f502])).
% 2.64/0.70  fof(f502,plain,(
% 2.64/0.70    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_22)),
% 2.64/0.70    inference(superposition,[],[f237,f384])).
% 2.64/0.70  fof(f237,plain,(
% 2.64/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(X0,k6_tmap_1(sK0,X0))) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5)),
% 2.64/0.70    inference(forward_demodulation,[],[f236,f153])).
% 2.64/0.70  fof(f236,plain,(
% 2.64/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,k6_tmap_1(sK0,X0))) ) | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 2.64/0.70    inference(subsumption_resolution,[],[f235,f104])).
% 2.64/0.70  fof(f235,plain,(
% 2.64/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,k6_tmap_1(sK0,X0)) | v2_struct_0(sK0)) ) | (~spl3_2 | ~spl3_3)),
% 2.64/0.70    inference(subsumption_resolution,[],[f234,f114])).
% 2.64/0.70  fof(f234,plain,(
% 2.64/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v3_pre_topc(X0,k6_tmap_1(sK0,X0)) | v2_struct_0(sK0)) ) | ~spl3_2),
% 2.64/0.70    inference(resolution,[],[f98,f109])).
% 2.64/0.70  fof(f98,plain,(
% 2.64/0.70    ( ! [X2,X0] : (~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(X2,k6_tmap_1(X0,X2)) | v2_struct_0(X0)) )),
% 2.64/0.70    inference(equality_resolution,[],[f85])).
% 2.64/0.70  fof(f85,plain,(
% 2.64/0.70    ( ! [X2,X0,X1] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.64/0.70    inference(cnf_transformation,[],[f35])).
% 2.64/0.70  fof(f35,plain,(
% 2.64/0.70    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.64/0.70    inference(flattening,[],[f34])).
% 2.64/0.70  fof(f34,plain,(
% 2.64/0.70    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.64/0.70    inference(ennf_transformation,[],[f15])).
% 2.64/0.70  fof(f15,axiom,(
% 2.64/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 2.64/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).
% 2.64/0.70  fof(f525,plain,(
% 2.64/0.70    spl3_31 | ~spl3_17),
% 2.64/0.70    inference(avatar_split_clause,[],[f337,f286,f522])).
% 2.64/0.70  fof(f520,plain,(
% 2.64/0.70    spl3_30 | ~spl3_5),
% 2.64/0.70    inference(avatar_split_clause,[],[f153,f124,f517])).
% 2.64/0.70  fof(f483,plain,(
% 2.64/0.70    spl3_29 | ~spl3_4 | ~spl3_5),
% 2.64/0.70    inference(avatar_split_clause,[],[f167,f124,f117,f480])).
% 2.64/0.70  fof(f167,plain,(
% 2.64/0.70    sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1) | (~spl3_4 | ~spl3_5)),
% 2.64/0.70    inference(forward_demodulation,[],[f164,f153])).
% 2.64/0.70  fof(f164,plain,(
% 2.64/0.70    sK1 = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),sK1) | ~spl3_4),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f119,f86])).
% 2.64/0.70  fof(f472,plain,(
% 2.64/0.70    spl3_28 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 2.64/0.70    inference(avatar_split_clause,[],[f229,f124,f117,f112,f107,f102,f469])).
% 2.64/0.70  fof(f229,plain,(
% 2.64/0.70    m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5)),
% 2.64/0.70    inference(forward_demodulation,[],[f228,f197])).
% 2.64/0.70  fof(f197,plain,(
% 2.64/0.70    k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5)),
% 2.64/0.70    inference(forward_demodulation,[],[f195,f153])).
% 2.64/0.70  fof(f195,plain,(
% 2.64/0.70    k7_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f104,f109,f114,f119,f80])).
% 2.64/0.70  fof(f80,plain,(
% 2.64/0.70    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 2.64/0.70    inference(cnf_transformation,[],[f29])).
% 2.64/0.70  fof(f29,plain,(
% 2.64/0.70    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.64/0.70    inference(flattening,[],[f28])).
% 2.64/0.70  fof(f28,plain,(
% 2.64/0.70    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.64/0.70    inference(ennf_transformation,[],[f9])).
% 2.64/0.70  fof(f9,axiom,(
% 2.64/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 2.64/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).
% 2.64/0.70  fof(f228,plain,(
% 2.64/0.70    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5)),
% 2.64/0.70    inference(forward_demodulation,[],[f227,f153])).
% 2.64/0.70  fof(f227,plain,(
% 2.64/0.70    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0)))) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5)),
% 2.64/0.70    inference(forward_demodulation,[],[f225,f204])).
% 2.64/0.70  fof(f225,plain,(
% 2.64/0.70    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f104,f109,f114,f119,f91])).
% 2.64/0.70  fof(f91,plain,(
% 2.64/0.70    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | v2_struct_0(X0)) )),
% 2.64/0.70    inference(cnf_transformation,[],[f40])).
% 2.64/0.70  fof(f40,plain,(
% 2.64/0.70    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.64/0.70    inference(flattening,[],[f39])).
% 2.64/0.70  fof(f39,plain,(
% 2.64/0.70    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.64/0.70    inference(ennf_transformation,[],[f11])).
% 2.64/0.70  fof(f11,axiom,(
% 2.64/0.70    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 2.64/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 2.64/0.70  fof(f467,plain,(
% 2.64/0.70    spl3_27 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_21),
% 2.64/0.70    inference(avatar_split_clause,[],[f456,f377,f117,f112,f107,f102,f452])).
% 2.64/0.70  fof(f456,plain,(
% 2.64/0.70    v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_21)),
% 2.64/0.70    inference(forward_demodulation,[],[f189,f379])).
% 2.64/0.70  fof(f189,plain,(
% 2.64/0.70    v1_funct_1(k7_tmap_1(sK0,sK1)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f104,f109,f114,f119,f89])).
% 2.64/0.70  fof(f89,plain,(
% 2.64/0.70    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_funct_1(k7_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 2.64/0.70    inference(cnf_transformation,[],[f40])).
% 2.64/0.70  fof(f465,plain,(
% 2.64/0.70    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_7 | ~spl3_21),
% 2.64/0.70    inference(avatar_contradiction_clause,[],[f464])).
% 2.64/0.70  fof(f464,plain,(
% 2.64/0.70    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_7 | ~spl3_21)),
% 2.64/0.70    inference(subsumption_resolution,[],[f463,f456])).
% 2.64/0.70  fof(f463,plain,(
% 2.64/0.70    ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | (spl3_7 | ~spl3_21)),
% 2.64/0.70    inference(forward_demodulation,[],[f134,f379])).
% 2.64/0.70  fof(f134,plain,(
% 2.64/0.70    ~v1_funct_1(k7_tmap_1(sK0,sK1)) | spl3_7),
% 2.64/0.70    inference(avatar_component_clause,[],[f133])).
% 2.64/0.70  fof(f133,plain,(
% 2.64/0.70    spl3_7 <=> v1_funct_1(k7_tmap_1(sK0,sK1))),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.64/0.70  fof(f441,plain,(
% 2.64/0.70    spl3_26 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 2.64/0.70    inference(avatar_split_clause,[],[f224,f124,f117,f112,f107,f102,f438])).
% 2.64/0.70  fof(f224,plain,(
% 2.64/0.70    v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5)),
% 2.64/0.70    inference(forward_demodulation,[],[f223,f197])).
% 2.64/0.70  fof(f223,plain,(
% 2.64/0.70    v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(sK0)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5)),
% 2.64/0.70    inference(forward_demodulation,[],[f222,f153])).
% 2.64/0.70  fof(f222,plain,(
% 2.64/0.70    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),k2_struct_0(sK0)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5)),
% 2.64/0.70    inference(forward_demodulation,[],[f221,f204])).
% 2.64/0.70  fof(f221,plain,(
% 2.64/0.70    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f104,f109,f114,f119,f90])).
% 2.64/0.70  fof(f90,plain,(
% 2.64/0.70    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.64/0.70    inference(cnf_transformation,[],[f40])).
% 2.64/0.70  fof(f385,plain,(
% 2.64/0.70    spl3_22 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 2.64/0.70    inference(avatar_split_clause,[],[f204,f124,f117,f112,f107,f102,f382])).
% 2.64/0.70  fof(f380,plain,(
% 2.64/0.70    spl3_21 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 2.64/0.70    inference(avatar_split_clause,[],[f197,f124,f117,f112,f107,f102,f377])).
% 2.64/0.70  fof(f348,plain,(
% 2.64/0.70    spl3_19 | ~spl3_16),
% 2.64/0.70    inference(avatar_split_clause,[],[f321,f281,f345])).
% 2.64/0.70  fof(f321,plain,(
% 2.64/0.70    l1_struct_0(k6_tmap_1(sK0,sK1)) | ~spl3_16),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f283,f66])).
% 2.64/0.70  fof(f66,plain,(
% 2.64/0.70    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.64/0.70    inference(cnf_transformation,[],[f22])).
% 2.64/0.70  fof(f22,plain,(
% 2.64/0.70    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.64/0.70    inference(ennf_transformation,[],[f7])).
% 2.64/0.70  fof(f7,axiom,(
% 2.64/0.70    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.64/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.64/0.70  fof(f289,plain,(
% 2.64/0.70    spl3_17 | ~spl3_5 | ~spl3_13),
% 2.64/0.70    inference(avatar_split_clause,[],[f246,f242,f124,f286])).
% 2.64/0.70  fof(f242,plain,(
% 2.64/0.70    spl3_13 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.64/0.70  fof(f246,plain,(
% 2.64/0.70    r1_tarski(sK1,k2_struct_0(sK0)) | (~spl3_5 | ~spl3_13)),
% 2.64/0.70    inference(forward_demodulation,[],[f244,f153])).
% 2.64/0.70  fof(f244,plain,(
% 2.64/0.70    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_13),
% 2.64/0.70    inference(avatar_component_clause,[],[f242])).
% 2.64/0.70  fof(f284,plain,(
% 2.64/0.70    spl3_16 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 2.64/0.70    inference(avatar_split_clause,[],[f184,f117,f112,f107,f102,f281])).
% 2.64/0.70  fof(f184,plain,(
% 2.64/0.70    l1_pre_topc(k6_tmap_1(sK0,sK1)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f104,f109,f114,f119,f88])).
% 2.64/0.70  fof(f88,plain,(
% 2.64/0.70    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | l1_pre_topc(k6_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 2.64/0.70    inference(cnf_transformation,[],[f38])).
% 2.64/0.70  fof(f38,plain,(
% 2.64/0.70    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.64/0.70    inference(flattening,[],[f37])).
% 2.64/0.70  fof(f37,plain,(
% 2.64/0.70    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.64/0.70    inference(ennf_transformation,[],[f18])).
% 2.64/0.70  fof(f18,plain,(
% 2.64/0.70    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 2.64/0.70    inference(pure_predicate_removal,[],[f10])).
% 2.64/0.70  fof(f10,axiom,(
% 2.64/0.70    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 2.64/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 2.64/0.70  fof(f258,plain,(
% 2.64/0.70    spl3_14 | ~spl3_3 | ~spl3_4 | ~spl3_6),
% 2.64/0.70    inference(avatar_split_clause,[],[f171,f129,f117,f112,f255])).
% 2.64/0.70  fof(f171,plain,(
% 2.64/0.70    r2_hidden(sK1,u1_pre_topc(sK0)) | (~spl3_3 | ~spl3_4 | ~spl3_6)),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f114,f131,f119,f75])).
% 2.64/0.70  fof(f131,plain,(
% 2.64/0.70    v3_pre_topc(sK1,sK0) | ~spl3_6),
% 2.64/0.70    inference(avatar_component_clause,[],[f129])).
% 2.64/0.70  fof(f245,plain,(
% 2.64/0.70    spl3_13 | ~spl3_4),
% 2.64/0.70    inference(avatar_split_clause,[],[f138,f117,f242])).
% 2.64/0.70  fof(f138,plain,(
% 2.64/0.70    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_4),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f119,f95])).
% 2.64/0.70  fof(f95,plain,(
% 2.64/0.70    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.64/0.70    inference(cnf_transformation,[],[f55])).
% 2.64/0.70  fof(f214,plain,(
% 2.64/0.70    ~spl3_9 | ~spl3_8 | ~spl3_10 | ~spl3_6 | ~spl3_7),
% 2.64/0.70    inference(avatar_split_clause,[],[f147,f133,f129,f159,f143,f149])).
% 2.64/0.70  fof(f149,plain,(
% 2.64/0.70    spl3_9 <=> v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.64/0.70  fof(f159,plain,(
% 2.64/0.70    spl3_10 <=> m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 2.64/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.64/0.70  fof(f147,plain,(
% 2.64/0.70    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | (~spl3_6 | ~spl3_7)),
% 2.64/0.70    inference(subsumption_resolution,[],[f137,f131])).
% 2.64/0.70  fof(f137,plain,(
% 2.64/0.70    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v3_pre_topc(sK1,sK0) | ~spl3_7),
% 2.64/0.70    inference(subsumption_resolution,[],[f64,f135])).
% 2.64/0.70  fof(f135,plain,(
% 2.64/0.70    v1_funct_1(k7_tmap_1(sK0,sK1)) | ~spl3_7),
% 2.64/0.70    inference(avatar_component_clause,[],[f133])).
% 2.64/0.70  fof(f64,plain,(
% 2.64/0.70    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 2.64/0.70    inference(cnf_transformation,[],[f46])).
% 2.64/0.70  fof(f46,plain,(
% 2.64/0.70    ((~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)) & ((m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) & v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) & v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) & v1_funct_1(k7_tmap_1(sK0,sK1))) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.64/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).
% 2.64/0.70  fof(f44,plain,(
% 2.64/0.70    ? [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k7_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1))))) | ~v5_pre_topc(k7_tmap_1(sK0,X1),sK0,k6_tmap_1(sK0,X1)) | ~v1_funct_2(k7_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1))) | ~v1_funct_1(k7_tmap_1(sK0,X1)) | ~v3_pre_topc(X1,sK0)) & ((m1_subset_1(k7_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1))))) & v5_pre_topc(k7_tmap_1(sK0,X1),sK0,k6_tmap_1(sK0,X1)) & v1_funct_2(k7_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1))) & v1_funct_1(k7_tmap_1(sK0,X1))) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.64/0.70    introduced(choice_axiom,[])).
% 2.64/0.70  fof(f45,plain,(
% 2.64/0.70    ? [X1] : ((~m1_subset_1(k7_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1))))) | ~v5_pre_topc(k7_tmap_1(sK0,X1),sK0,k6_tmap_1(sK0,X1)) | ~v1_funct_2(k7_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1))) | ~v1_funct_1(k7_tmap_1(sK0,X1)) | ~v3_pre_topc(X1,sK0)) & ((m1_subset_1(k7_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1))))) & v5_pre_topc(k7_tmap_1(sK0,X1),sK0,k6_tmap_1(sK0,X1)) & v1_funct_2(k7_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1))) & v1_funct_1(k7_tmap_1(sK0,X1))) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)) & ((m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) & v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) & v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) & v1_funct_1(k7_tmap_1(sK0,sK1))) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.64/0.70    introduced(choice_axiom,[])).
% 2.64/0.70  fof(f43,plain,(
% 2.64/0.70    ? [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.64/0.70    inference(flattening,[],[f42])).
% 2.64/0.70  fof(f42,plain,(
% 2.64/0.70    ? [X0] : (? [X1] : ((((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.64/0.70    inference(nnf_transformation,[],[f20])).
% 2.64/0.70  fof(f20,plain,(
% 2.64/0.70    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.64/0.70    inference(flattening,[],[f19])).
% 2.64/0.70  fof(f19,plain,(
% 2.64/0.70    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.64/0.70    inference(ennf_transformation,[],[f17])).
% 2.64/0.70  fof(f17,negated_conjecture,(
% 2.64/0.70    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 2.64/0.70    inference(negated_conjecture,[],[f16])).
% 2.64/0.70  fof(f16,conjecture,(
% 2.64/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 2.64/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_tmap_1)).
% 2.64/0.70  fof(f146,plain,(
% 2.64/0.70    spl3_6 | spl3_8),
% 2.64/0.70    inference(avatar_split_clause,[],[f62,f143,f129])).
% 2.64/0.70  fof(f62,plain,(
% 2.64/0.70    v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 2.64/0.70    inference(cnf_transformation,[],[f46])).
% 2.64/0.70  fof(f127,plain,(
% 2.64/0.70    spl3_5 | ~spl3_3),
% 2.64/0.70    inference(avatar_split_clause,[],[f121,f112,f124])).
% 2.64/0.70  fof(f121,plain,(
% 2.64/0.70    l1_struct_0(sK0) | ~spl3_3),
% 2.64/0.70    inference(unit_resulting_resolution,[],[f114,f66])).
% 2.64/0.70  fof(f120,plain,(
% 2.64/0.70    spl3_4),
% 2.64/0.70    inference(avatar_split_clause,[],[f59,f117])).
% 2.64/0.70  fof(f59,plain,(
% 2.64/0.70    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.64/0.70    inference(cnf_transformation,[],[f46])).
% 2.64/0.70  fof(f115,plain,(
% 2.64/0.70    spl3_3),
% 2.64/0.70    inference(avatar_split_clause,[],[f58,f112])).
% 2.64/0.70  fof(f58,plain,(
% 2.64/0.70    l1_pre_topc(sK0)),
% 2.64/0.70    inference(cnf_transformation,[],[f46])).
% 2.64/0.70  fof(f110,plain,(
% 2.64/0.70    spl3_2),
% 2.64/0.70    inference(avatar_split_clause,[],[f57,f107])).
% 2.64/0.70  fof(f57,plain,(
% 2.64/0.70    v2_pre_topc(sK0)),
% 2.64/0.70    inference(cnf_transformation,[],[f46])).
% 2.64/0.70  fof(f105,plain,(
% 2.64/0.70    ~spl3_1),
% 2.64/0.70    inference(avatar_split_clause,[],[f56,f102])).
% 2.64/0.70  fof(f56,plain,(
% 2.64/0.70    ~v2_struct_0(sK0)),
% 2.64/0.70    inference(cnf_transformation,[],[f46])).
% 2.64/0.70  % SZS output end Proof for theBenchmark
% 2.64/0.70  % (28991)------------------------------
% 2.64/0.70  % (28991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.70  % (28991)Termination reason: Refutation
% 2.64/0.70  
% 2.64/0.70  % (28991)Memory used [KB]: 14583
% 2.64/0.70  % (28991)Time elapsed: 0.291 s
% 2.64/0.70  % (28991)------------------------------
% 2.64/0.70  % (28991)------------------------------
% 2.64/0.70  % (28967)Success in time 0.341 s
%------------------------------------------------------------------------------
