%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:38 EST 2020

% Result     : Theorem 3.27s
% Output     : Refutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  321 ( 678 expanded)
%              Number of leaves         :   57 ( 278 expanded)
%              Depth                    :   31
%              Number of atoms          : 1716 (3399 expanded)
%              Number of equality atoms :  129 ( 191 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3616,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f144,f149,f154,f164,f169,f174,f179,f184,f194,f200,f387,f417,f444,f812,f816,f821,f836,f851,f1469,f1642,f1871,f1877,f1915,f2563,f3046,f3098,f3115,f3120,f3138,f3154,f3213,f3289,f3432,f3578,f3596,f3608,f3615])).

fof(f3615,plain,
    ( spl6_5
    | ~ spl6_7
    | ~ spl6_141
    | ~ spl6_167
    | spl6_190 ),
    inference(avatar_contradiction_clause,[],[f3614])).

fof(f3614,plain,
    ( $false
    | spl6_5
    | ~ spl6_7
    | ~ spl6_141
    | ~ spl6_167
    | spl6_190 ),
    inference(subsumption_resolution,[],[f3613,f163])).

fof(f163,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl6_5
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f3613,plain,
    ( v2_struct_0(sK2)
    | ~ spl6_7
    | ~ spl6_141
    | ~ spl6_167
    | spl6_190 ),
    inference(subsumption_resolution,[],[f3612,f173])).

fof(f173,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl6_7
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f3612,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ spl6_141
    | ~ spl6_167
    | spl6_190 ),
    inference(subsumption_resolution,[],[f3610,f3096])).

fof(f3096,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_167 ),
    inference(avatar_component_clause,[],[f3095])).

fof(f3095,plain,
    ( spl6_167
  <=> r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_167])])).

fof(f3610,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ spl6_141
    | spl6_190 ),
    inference(resolution,[],[f3607,f2562])).

fof(f2562,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl6_141 ),
    inference(avatar_component_clause,[],[f2561])).

fof(f2561,plain,
    ( spl6_141
  <=> ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_141])])).

fof(f3607,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2))
    | spl6_190 ),
    inference(avatar_component_clause,[],[f3605])).

fof(f3605,plain,
    ( spl6_190
  <=> v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_190])])).

fof(f3608,plain,
    ( ~ spl6_190
    | spl6_31
    | ~ spl6_99 ),
    inference(avatar_split_clause,[],[f3603,f1868,f372,f3605])).

fof(f372,plain,
    ( spl6_31
  <=> v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f1868,plain,
    ( spl6_99
  <=> k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).

fof(f3603,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2))
    | spl6_31
    | ~ spl6_99 ),
    inference(forward_demodulation,[],[f374,f1870])).

fof(f1870,plain,
    ( k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ spl6_99 ),
    inference(avatar_component_clause,[],[f1868])).

fof(f374,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
    | spl6_31 ),
    inference(avatar_component_clause,[],[f372])).

fof(f3596,plain,
    ( spl6_5
    | ~ spl6_7
    | ~ spl6_167
    | spl6_179
    | ~ spl6_188 ),
    inference(avatar_contradiction_clause,[],[f3595])).

fof(f3595,plain,
    ( $false
    | spl6_5
    | ~ spl6_7
    | ~ spl6_167
    | spl6_179
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f3594,f163])).

fof(f3594,plain,
    ( v2_struct_0(sK2)
    | ~ spl6_7
    | ~ spl6_167
    | spl6_179
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f3593,f3431])).

fof(f3431,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | spl6_179 ),
    inference(avatar_component_clause,[],[f3429])).

fof(f3429,plain,
    ( spl6_179
  <=> m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_179])])).

fof(f3593,plain,
    ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ spl6_7
    | ~ spl6_167
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f3586,f3096])).

fof(f3586,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ spl6_7
    | ~ spl6_188 ),
    inference(resolution,[],[f3577,f173])).

fof(f3577,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK0)
        | ~ r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1))
        | m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | v2_struct_0(X3) )
    | ~ spl6_188 ),
    inference(avatar_component_clause,[],[f3576])).

fof(f3576,plain,
    ( spl6_188
  <=> ! [X3] :
        ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_188])])).

fof(f3578,plain,
    ( spl6_188
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40
    | ~ spl6_60
    | ~ spl6_61
    | ~ spl6_87 ),
    inference(avatar_split_clause,[],[f3573,f1621,f848,f833,f441,f151,f146,f141,f3576])).

fof(f141,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f146,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f151,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f441,plain,
    ( spl6_40
  <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f833,plain,
    ( spl6_60
  <=> k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f848,plain,
    ( spl6_61
  <=> u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f1621,plain,
    ( spl6_87
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f3573,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40
    | ~ spl6_60
    | ~ spl6_61
    | ~ spl6_87 ),
    inference(forward_demodulation,[],[f3572,f835])).

fof(f835,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f833])).

fof(f3572,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40
    | ~ spl6_61
    | ~ spl6_87 ),
    inference(forward_demodulation,[],[f3571,f850])).

fof(f850,plain,
    ( u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0)
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f848])).

fof(f3571,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | ~ r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40
    | ~ spl6_87 ),
    inference(subsumption_resolution,[],[f495,f1622])).

fof(f1622,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_87 ),
    inference(avatar_component_clause,[],[f1621])).

fof(f495,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | ~ r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f494,f143])).

fof(f143,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f141])).

fof(f494,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | ~ r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f493,f148])).

fof(f148,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f146])).

fof(f493,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | ~ r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f476,f153])).

fof(f153,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f151])).

fof(f476,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | ~ r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_40 ),
    inference(superposition,[],[f112,f443])).

fof(f443,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f441])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_tmap_1)).

fof(f3432,plain,
    ( ~ spl6_179
    | spl6_34
    | ~ spl6_61
    | ~ spl6_99 ),
    inference(avatar_split_clause,[],[f3295,f1868,f848,f384,f3429])).

fof(f384,plain,
    ( spl6_34
  <=> m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f3295,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | spl6_34
    | ~ spl6_61
    | ~ spl6_99 ),
    inference(forward_demodulation,[],[f3294,f1870])).

fof(f3294,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | spl6_34
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f386,f850])).

fof(f386,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl6_34 ),
    inference(avatar_component_clause,[],[f384])).

fof(f3289,plain,
    ( spl6_5
    | ~ spl6_7
    | ~ spl6_167
    | spl6_172
    | ~ spl6_178 ),
    inference(avatar_contradiction_clause,[],[f3288])).

fof(f3288,plain,
    ( $false
    | spl6_5
    | ~ spl6_7
    | ~ spl6_167
    | spl6_172
    | ~ spl6_178 ),
    inference(subsumption_resolution,[],[f3287,f163])).

fof(f3287,plain,
    ( v2_struct_0(sK2)
    | ~ spl6_7
    | ~ spl6_167
    | spl6_172
    | ~ spl6_178 ),
    inference(subsumption_resolution,[],[f3286,f173])).

fof(f3286,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ spl6_167
    | spl6_172
    | ~ spl6_178 ),
    inference(subsumption_resolution,[],[f3279,f3096])).

fof(f3279,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | spl6_172
    | ~ spl6_178 ),
    inference(resolution,[],[f3212,f3153])).

fof(f3153,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | spl6_172 ),
    inference(avatar_component_clause,[],[f3151])).

fof(f3151,plain,
    ( spl6_172
  <=> v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_172])])).

fof(f3212,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X1),u1_struct_0(X1),u1_struct_0(sK0))
        | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1) )
    | ~ spl6_178 ),
    inference(avatar_component_clause,[],[f3211])).

fof(f3211,plain,
    ( spl6_178
  <=> ! [X1] :
        ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X1),u1_struct_0(X1),u1_struct_0(sK0))
        | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_178])])).

fof(f3213,plain,
    ( spl6_178
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40
    | ~ spl6_60
    | ~ spl6_61
    | ~ spl6_87 ),
    inference(avatar_split_clause,[],[f3208,f1621,f848,f833,f441,f151,f146,f141,f3211])).

fof(f3208,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X1),u1_struct_0(X1),u1_struct_0(sK0))
        | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40
    | ~ spl6_60
    | ~ spl6_61
    | ~ spl6_87 ),
    inference(forward_demodulation,[],[f3207,f835])).

fof(f3207,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(sK0))
        | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40
    | ~ spl6_61
    | ~ spl6_87 ),
    inference(forward_demodulation,[],[f3206,f850])).

fof(f3206,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40
    | ~ spl6_87 ),
    inference(subsumption_resolution,[],[f489,f1622])).

fof(f489,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f488,f143])).

fof(f488,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f487,f148])).

fof(f487,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f474,f153])).

fof(f474,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_40 ),
    inference(superposition,[],[f110,f443])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3154,plain,
    ( ~ spl6_172
    | spl6_32
    | ~ spl6_61
    | ~ spl6_99 ),
    inference(avatar_split_clause,[],[f3141,f1868,f848,f376,f3151])).

fof(f376,plain,
    ( spl6_32
  <=> v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f3141,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | spl6_32
    | ~ spl6_61
    | ~ spl6_99 ),
    inference(forward_demodulation,[],[f3140,f1870])).

fof(f3140,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | spl6_32
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f378,f850])).

fof(f378,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl6_32 ),
    inference(avatar_component_clause,[],[f376])).

fof(f3138,plain,
    ( ~ spl6_10
    | spl6_170 ),
    inference(avatar_contradiction_clause,[],[f3137])).

fof(f3137,plain,
    ( $false
    | ~ spl6_10
    | spl6_170 ),
    inference(subsumption_resolution,[],[f3135,f193])).

fof(f193,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl6_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f3135,plain,
    ( ~ l1_pre_topc(sK1)
    | spl6_170 ),
    inference(resolution,[],[f3114,f89])).

fof(f89,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f3114,plain,
    ( ~ l1_struct_0(sK1)
    | spl6_170 ),
    inference(avatar_component_clause,[],[f3112])).

fof(f3112,plain,
    ( spl6_170
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_170])])).

fof(f3120,plain,
    ( ~ spl6_11
    | spl6_169 ),
    inference(avatar_contradiction_clause,[],[f3119])).

fof(f3119,plain,
    ( $false
    | ~ spl6_11
    | spl6_169 ),
    inference(subsumption_resolution,[],[f3117,f199])).

fof(f199,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl6_11
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f3117,plain,
    ( ~ l1_pre_topc(sK2)
    | spl6_169 ),
    inference(resolution,[],[f3110,f89])).

fof(f3110,plain,
    ( ~ l1_struct_0(sK2)
    | spl6_169 ),
    inference(avatar_component_clause,[],[f3108])).

fof(f3108,plain,
    ( spl6_169
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_169])])).

fof(f3115,plain,
    ( ~ spl6_169
    | ~ spl6_170
    | ~ spl6_56
    | spl6_167 ),
    inference(avatar_split_clause,[],[f3102,f3095,f809,f3112,f3108])).

fof(f809,plain,
    ( spl6_56
  <=> r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f3102,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ spl6_56
    | spl6_167 ),
    inference(subsumption_resolution,[],[f3101,f811])).

fof(f811,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f809])).

fof(f3101,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | spl6_167 ),
    inference(resolution,[],[f3097,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f3097,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_167 ),
    inference(avatar_component_clause,[],[f3095])).

fof(f3098,plain,
    ( ~ spl6_167
    | spl6_5
    | ~ spl6_7
    | spl6_102
    | ~ spl6_166 ),
    inference(avatar_split_clause,[],[f3093,f3044,f1912,f171,f161,f3095])).

fof(f1912,plain,
    ( spl6_102
  <=> v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).

fof(f3044,plain,
    ( spl6_166
  <=> ! [X2] :
        ( v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X2),X2,k8_tmap_1(sK0,sK1))
        | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_166])])).

fof(f3093,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_5
    | ~ spl6_7
    | spl6_102
    | ~ spl6_166 ),
    inference(subsumption_resolution,[],[f3092,f163])).

fof(f3092,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK2)
    | ~ spl6_7
    | spl6_102
    | ~ spl6_166 ),
    inference(subsumption_resolution,[],[f3091,f173])).

fof(f3091,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | spl6_102
    | ~ spl6_166 ),
    inference(resolution,[],[f3045,f1914])).

fof(f1914,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k8_tmap_1(sK0,sK1))
    | spl6_102 ),
    inference(avatar_component_clause,[],[f1912])).

fof(f3045,plain,
    ( ! [X2] :
        ( v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X2),X2,k8_tmap_1(sK0,sK1))
        | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2) )
    | ~ spl6_166 ),
    inference(avatar_component_clause,[],[f3044])).

fof(f3046,plain,
    ( spl6_166
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40
    | ~ spl6_60
    | ~ spl6_87 ),
    inference(avatar_split_clause,[],[f2998,f1621,f833,f441,f151,f146,f141,f3044])).

fof(f2998,plain,
    ( ! [X2] :
        ( v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X2),X2,k8_tmap_1(sK0,sK1))
        | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40
    | ~ spl6_60
    | ~ spl6_87 ),
    inference(forward_demodulation,[],[f2997,f835])).

fof(f2997,plain,
    ( ! [X2] :
        ( v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1))
        | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40
    | ~ spl6_87 ),
    inference(subsumption_resolution,[],[f492,f1622])).

fof(f492,plain,
    ( ! [X2] :
        ( v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1))
        | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f491,f143])).

fof(f491,plain,
    ( ! [X2] :
        ( v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1))
        | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f490,f148])).

fof(f490,plain,
    ( ! [X2] :
        ( v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1))
        | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f475,f153])).

fof(f475,plain,
    ( ! [X2] :
        ( v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1))
        | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_40 ),
    inference(superposition,[],[f111,f443])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2563,plain,
    ( spl6_141
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40
    | ~ spl6_60
    | ~ spl6_87 ),
    inference(avatar_split_clause,[],[f2554,f1621,f833,f441,f151,f146,f141,f2561])).

fof(f2554,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40
    | ~ spl6_60
    | ~ spl6_87 ),
    inference(forward_demodulation,[],[f2553,f835])).

fof(f2553,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40
    | ~ spl6_87 ),
    inference(subsumption_resolution,[],[f486,f1622])).

fof(f486,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f485,f143])).

fof(f485,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f484,f148])).

fof(f484,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f473,f153])).

fof(f473,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_40 ),
    inference(superposition,[],[f109,f443])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1915,plain,
    ( ~ spl6_102
    | spl6_33
    | ~ spl6_99 ),
    inference(avatar_split_clause,[],[f1884,f1868,f380,f1912])).

fof(f380,plain,
    ( spl6_33
  <=> v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f1884,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k8_tmap_1(sK0,sK1))
    | spl6_33
    | ~ spl6_99 ),
    inference(backward_demodulation,[],[f382,f1870])).

fof(f382,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
    | spl6_33 ),
    inference(avatar_component_clause,[],[f380])).

fof(f1877,plain,
    ( spl6_1
    | ~ spl6_78
    | ~ spl6_98 ),
    inference(avatar_contradiction_clause,[],[f1876])).

fof(f1876,plain,
    ( $false
    | spl6_1
    | ~ spl6_78
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f1875,f143])).

fof(f1875,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_78
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f1873,f1459])).

fof(f1459,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f1458])).

fof(f1458,plain,
    ( spl6_78
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f1873,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_98 ),
    inference(resolution,[],[f1866,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f1866,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_98 ),
    inference(avatar_component_clause,[],[f1864])).

fof(f1864,plain,
    ( spl6_98
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f1871,plain,
    ( spl6_98
    | spl6_99
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_40
    | ~ spl6_60
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f1857,f848,f833,f441,f166,f151,f146,f141,f1868,f1864])).

fof(f166,plain,
    ( spl6_6
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1857,plain,
    ( k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_40
    | ~ spl6_60
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f1159,f835])).

fof(f1159,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_40
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f1158,f850])).

fof(f1158,plain,
    ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_40 ),
    inference(duplicate_literal_removal,[],[f1157])).

fof(f1157,plain,
    ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_40 ),
    inference(forward_demodulation,[],[f1156,f443])).

fof(f1156,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f1155,f153])).

fof(f1155,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f1154,f143])).

fof(f1154,plain,
    ( v2_struct_0(sK0)
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f1148,f148])).

fof(f1148,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl6_6 ),
    inference(resolution,[],[f701,f168])).

fof(f168,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f166])).

fof(f701,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k9_tmap_1(X0,X1) = k7_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f700,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f700,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k9_tmap_1(X0,X1) = k7_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v1_xboole_0(u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f699,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f699,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k9_tmap_1(X0,X1) = k7_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_2(k7_tmap_1(X0,u1_struct_0(X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f692])).

fof(f692,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k9_tmap_1(X0,X1) = k7_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_2(k7_tmap_1(X0,u1_struct_0(X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f680,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f680,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_tmap_1(X1,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | k9_tmap_1(X1,X0) = k7_tmap_1(X1,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ v1_funct_2(k7_tmap_1(X1,u1_struct_0(X0)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X0))) ) ),
    inference(subsumption_resolution,[],[f406,f257])).

fof(f257,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f256])).

fof(f256,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f125,f92])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f406,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | k9_tmap_1(X1,X0) = k7_tmap_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k7_tmap_1(X1,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))))
      | ~ v1_funct_2(k7_tmap_1(X1,u1_struct_0(X0)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))
      | ~ v1_funct_1(k7_tmap_1(X1,u1_struct_0(X0)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X0))) ) ),
    inference(subsumption_resolution,[],[f405,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).

fof(f405,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | k9_tmap_1(X1,X0) = k7_tmap_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k7_tmap_1(X1,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))))
      | ~ v1_funct_2(k7_tmap_1(X1,u1_struct_0(X0)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))
      | ~ v1_funct_1(k7_tmap_1(X1,u1_struct_0(X0)))
      | ~ v1_funct_1(k9_tmap_1(X1,X0))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X0))) ) ),
    inference(subsumption_resolution,[],[f404,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f404,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | k9_tmap_1(X1,X0) = k7_tmap_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k7_tmap_1(X1,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))))
      | ~ v1_funct_2(k7_tmap_1(X1,u1_struct_0(X0)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))
      | ~ v1_funct_1(k7_tmap_1(X1,u1_struct_0(X0)))
      | ~ v1_funct_2(k9_tmap_1(X1,X0),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))
      | ~ v1_funct_1(k9_tmap_1(X1,X0))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X0))) ) ),
    inference(subsumption_resolution,[],[f403,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f403,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | k9_tmap_1(X1,X0) = k7_tmap_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k7_tmap_1(X1,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))))
      | ~ v1_funct_2(k7_tmap_1(X1,u1_struct_0(X0)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))
      | ~ v1_funct_1(k7_tmap_1(X1,u1_struct_0(X0)))
      | ~ m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
      | ~ v1_funct_2(k9_tmap_1(X1,X0),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))
      | ~ v1_funct_1(k9_tmap_1(X1,X0))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X0))) ) ),
    inference(resolution,[],[f399,f132])).

fof(f132,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f399,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f398,f116])).

fof(f398,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f397,f117])).

fof(f397,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f396,f118])).

fof(f396,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f137,f92])).

fof(f137,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2)))
                    & u1_struct_0(X1) = sK5(X0,X1,X2)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f74,f75])).

fof(f75,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2)))
        & u1_struct_0(X1) = sK5(X0,X1,X2)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).

fof(f1642,plain,
    ( ~ spl6_3
    | ~ spl6_6
    | spl6_87 ),
    inference(avatar_contradiction_clause,[],[f1641])).

fof(f1641,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_6
    | spl6_87 ),
    inference(subsumption_resolution,[],[f1640,f153])).

fof(f1640,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_6
    | spl6_87 ),
    inference(subsumption_resolution,[],[f1638,f168])).

fof(f1638,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl6_87 ),
    inference(resolution,[],[f1623,f92])).

fof(f1623,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_87 ),
    inference(avatar_component_clause,[],[f1621])).

fof(f1469,plain,
    ( ~ spl6_3
    | spl6_78 ),
    inference(avatar_contradiction_clause,[],[f1468])).

fof(f1468,plain,
    ( $false
    | ~ spl6_3
    | spl6_78 ),
    inference(subsumption_resolution,[],[f1466,f153])).

fof(f1466,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_78 ),
    inference(resolution,[],[f1460,f89])).

fof(f1460,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_78 ),
    inference(avatar_component_clause,[],[f1458])).

fof(f851,plain,
    ( spl6_61
    | ~ spl6_6
    | ~ spl6_40
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f841,f819,f441,f166,f848])).

fof(f819,plain,
    ( spl6_58
  <=> ! [X0] :
        ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f841,plain,
    ( u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_40
    | ~ spl6_58 ),
    inference(forward_demodulation,[],[f837,f443])).

fof(f837,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_6
    | ~ spl6_58 ),
    inference(resolution,[],[f820,f168])).

fof(f820,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) )
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f819])).

fof(f836,plain,
    ( spl6_60
    | ~ spl6_6
    | ~ spl6_57 ),
    inference(avatar_split_clause,[],[f826,f814,f166,f833])).

fof(f814,plain,
    ( spl6_57
  <=> ! [X0] :
        ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f826,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_6
    | ~ spl6_57 ),
    inference(resolution,[],[f815,f168])).

fof(f815,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0)) )
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f814])).

fof(f821,plain,
    ( spl6_58
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f508,f151,f146,f141,f819])).

fof(f508,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f507,f143])).

fof(f507,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f505,f153])).

fof(f505,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f266,f148])).

fof(f266,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f265])).

fof(f265,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f107,f92])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f816,plain,
    ( spl6_57
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f468,f151,f146,f141,f814])).

fof(f468,plain,
    ( ! [X0] :
        ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f467,f143])).

fof(f467,plain,
    ( ! [X0] :
        ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f465,f153])).

fof(f465,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f260,f148])).

fof(f260,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f259])).

fof(f259,plain,(
    ! [X0,X1] :
      ( k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f106,f92])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

fof(f812,plain,
    ( spl6_56
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f807,f197,f191,f176,f809])).

fof(f176,plain,
    ( spl6_8
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f807,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f806,f199])).

fof(f806,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ l1_pre_topc(sK2)
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f805,f193])).

fof(f805,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f412,f178])).

fof(f178,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f176])).

fof(f412,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f195,f89])).

fof(f195,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f128,f89])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f444,plain,
    ( spl6_40
    | ~ spl6_6
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f421,f415,f166,f441])).

fof(f415,plain,
    ( spl6_38
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f421,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_6
    | ~ spl6_38 ),
    inference(resolution,[],[f416,f168])).

fof(f416,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0)) )
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f415])).

fof(f417,plain,
    ( spl6_38
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f335,f151,f146,f141,f415])).

fof(f335,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f334,f143])).

fof(f334,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f332,f153])).

fof(f332,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0))
        | v2_struct_0(sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f330,f148])).

fof(f330,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f329,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f329,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f328,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f328,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f327,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f327,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f135,f92])).

fof(f135,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK4(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK4(X0,X1,X2)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f70,f71])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK4(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK4(X0,X1,X2)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f387,plain,
    ( ~ spl6_31
    | ~ spl6_32
    | ~ spl6_33
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f86,f384,f380,f376,f372])).

fof(f86,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)) )
    & r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f64,f63,f62])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                  | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                  | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
                & r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),X2,k8_tmap_1(sK0,X1))
                | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,X1)))
                | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,X1)))))
              | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),X2,k8_tmap_1(sK0,X1))
              | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,X1)))
              | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2)) )
            & r1_tsep_1(X1,X2)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,sK1)))))
            | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),X2,k8_tmap_1(sK0,sK1))
            | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,sK1)))
            | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2)) )
          & r1_tsep_1(sK1,X2)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X2] :
        ( ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,sK1)))))
          | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),X2,k8_tmap_1(sK0,sK1))
          | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,sK1)))
          | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2)) )
        & r1_tsep_1(sK1,X2)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)) )
      & r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r1_tsep_1(X1,X2)
                 => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                    & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                    & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                    & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tsep_1(X1,X2)
               => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_tmap_1)).

fof(f200,plain,
    ( spl6_11
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f186,f182,f171,f197])).

fof(f182,plain,
    ( spl6_9
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f186,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(resolution,[],[f183,f173])).

fof(f183,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f182])).

fof(f194,plain,
    ( spl6_10
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f185,f182,f166,f191])).

fof(f185,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(resolution,[],[f183,f168])).

fof(f184,plain,
    ( spl6_9
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f180,f151,f182])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f91,f153])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f179,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f85,f176])).

fof(f85,plain,(
    r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f174,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f84,f171])).

fof(f84,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f169,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f82,f166])).

fof(f82,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f164,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f83,f161])).

fof(f83,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f154,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f80,f151])).

fof(f80,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f149,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f79,f146])).

fof(f79,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f144,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f78,f141])).

fof(f78,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:15:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (21759)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.48  % (21752)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (21750)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (21773)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.50  % (21754)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (21751)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (21760)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (21770)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (21768)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (21763)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (21755)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (21753)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (21748)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (21758)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (21766)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (21765)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (21756)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (21761)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (21772)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (21749)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (21771)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (21749)Refutation not found, incomplete strategy% (21749)------------------------------
% 0.21/0.54  % (21749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21749)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21749)Memory used [KB]: 10746
% 0.21/0.54  % (21749)Time elapsed: 0.117 s
% 0.21/0.54  % (21749)------------------------------
% 0.21/0.54  % (21749)------------------------------
% 0.21/0.54  % (21769)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (21762)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (21767)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.55  % (21764)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.56  % (21757)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 2.09/0.70  % (21757)Refutation not found, incomplete strategy% (21757)------------------------------
% 2.09/0.70  % (21757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.70  % (21757)Termination reason: Refutation not found, incomplete strategy
% 2.09/0.70  
% 2.09/0.70  % (21757)Memory used [KB]: 6140
% 2.09/0.70  % (21757)Time elapsed: 0.273 s
% 2.09/0.70  % (21757)------------------------------
% 2.09/0.70  % (21757)------------------------------
% 3.27/0.78  % (21750)Refutation found. Thanks to Tanya!
% 3.27/0.78  % SZS status Theorem for theBenchmark
% 3.27/0.78  % SZS output start Proof for theBenchmark
% 3.27/0.78  fof(f3616,plain,(
% 3.27/0.78    $false),
% 3.27/0.78    inference(avatar_sat_refutation,[],[f144,f149,f154,f164,f169,f174,f179,f184,f194,f200,f387,f417,f444,f812,f816,f821,f836,f851,f1469,f1642,f1871,f1877,f1915,f2563,f3046,f3098,f3115,f3120,f3138,f3154,f3213,f3289,f3432,f3578,f3596,f3608,f3615])).
% 3.27/0.78  fof(f3615,plain,(
% 3.27/0.78    spl6_5 | ~spl6_7 | ~spl6_141 | ~spl6_167 | spl6_190),
% 3.27/0.78    inference(avatar_contradiction_clause,[],[f3614])).
% 3.27/0.78  fof(f3614,plain,(
% 3.27/0.78    $false | (spl6_5 | ~spl6_7 | ~spl6_141 | ~spl6_167 | spl6_190)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3613,f163])).
% 3.27/0.78  fof(f163,plain,(
% 3.27/0.78    ~v2_struct_0(sK2) | spl6_5),
% 3.27/0.78    inference(avatar_component_clause,[],[f161])).
% 3.27/0.78  fof(f161,plain,(
% 3.27/0.78    spl6_5 <=> v2_struct_0(sK2)),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 3.27/0.78  fof(f3613,plain,(
% 3.27/0.78    v2_struct_0(sK2) | (~spl6_7 | ~spl6_141 | ~spl6_167 | spl6_190)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3612,f173])).
% 3.27/0.78  fof(f173,plain,(
% 3.27/0.78    m1_pre_topc(sK2,sK0) | ~spl6_7),
% 3.27/0.78    inference(avatar_component_clause,[],[f171])).
% 3.27/0.78  fof(f171,plain,(
% 3.27/0.78    spl6_7 <=> m1_pre_topc(sK2,sK0)),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 3.27/0.78  fof(f3612,plain,(
% 3.27/0.78    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | (~spl6_141 | ~spl6_167 | spl6_190)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3610,f3096])).
% 3.27/0.78  fof(f3096,plain,(
% 3.27/0.78    r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl6_167),
% 3.27/0.78    inference(avatar_component_clause,[],[f3095])).
% 3.27/0.78  fof(f3095,plain,(
% 3.27/0.78    spl6_167 <=> r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_167])])).
% 3.27/0.78  fof(f3610,plain,(
% 3.27/0.78    ~r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | (~spl6_141 | spl6_190)),
% 3.27/0.78    inference(resolution,[],[f3607,f2562])).
% 3.27/0.78  fof(f2562,plain,(
% 3.27/0.78    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | ~spl6_141),
% 3.27/0.78    inference(avatar_component_clause,[],[f2561])).
% 3.27/0.78  fof(f2561,plain,(
% 3.27/0.78    spl6_141 <=> ! [X0] : (v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_141])])).
% 3.27/0.78  fof(f3607,plain,(
% 3.27/0.78    ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2)) | spl6_190),
% 3.27/0.78    inference(avatar_component_clause,[],[f3605])).
% 3.27/0.78  fof(f3605,plain,(
% 3.27/0.78    spl6_190 <=> v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_190])])).
% 3.27/0.78  fof(f3608,plain,(
% 3.27/0.78    ~spl6_190 | spl6_31 | ~spl6_99),
% 3.27/0.78    inference(avatar_split_clause,[],[f3603,f1868,f372,f3605])).
% 3.27/0.78  fof(f372,plain,(
% 3.27/0.78    spl6_31 <=> v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 3.27/0.78  fof(f1868,plain,(
% 3.27/0.78    spl6_99 <=> k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).
% 3.27/0.78  fof(f3603,plain,(
% 3.27/0.78    ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2)) | (spl6_31 | ~spl6_99)),
% 3.27/0.78    inference(forward_demodulation,[],[f374,f1870])).
% 3.27/0.78  fof(f1870,plain,(
% 3.27/0.78    k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~spl6_99),
% 3.27/0.78    inference(avatar_component_clause,[],[f1868])).
% 3.27/0.78  fof(f374,plain,(
% 3.27/0.78    ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)) | spl6_31),
% 3.27/0.78    inference(avatar_component_clause,[],[f372])).
% 3.27/0.78  fof(f3596,plain,(
% 3.27/0.78    spl6_5 | ~spl6_7 | ~spl6_167 | spl6_179 | ~spl6_188),
% 3.27/0.78    inference(avatar_contradiction_clause,[],[f3595])).
% 3.27/0.78  fof(f3595,plain,(
% 3.27/0.78    $false | (spl6_5 | ~spl6_7 | ~spl6_167 | spl6_179 | ~spl6_188)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3594,f163])).
% 3.27/0.78  fof(f3594,plain,(
% 3.27/0.78    v2_struct_0(sK2) | (~spl6_7 | ~spl6_167 | spl6_179 | ~spl6_188)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3593,f3431])).
% 3.27/0.78  fof(f3431,plain,(
% 3.27/0.78    ~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | spl6_179),
% 3.27/0.78    inference(avatar_component_clause,[],[f3429])).
% 3.27/0.78  fof(f3429,plain,(
% 3.27/0.78    spl6_179 <=> m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_179])])).
% 3.27/0.78  fof(f3593,plain,(
% 3.27/0.78    m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | v2_struct_0(sK2) | (~spl6_7 | ~spl6_167 | ~spl6_188)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3586,f3096])).
% 3.27/0.78  fof(f3586,plain,(
% 3.27/0.78    ~r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | v2_struct_0(sK2) | (~spl6_7 | ~spl6_188)),
% 3.27/0.78    inference(resolution,[],[f3577,f173])).
% 3.27/0.78  fof(f3577,plain,(
% 3.27/0.78    ( ! [X3] : (~m1_pre_topc(X3,sK0) | ~r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1)) | m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | v2_struct_0(X3)) ) | ~spl6_188),
% 3.27/0.78    inference(avatar_component_clause,[],[f3576])).
% 3.27/0.78  fof(f3576,plain,(
% 3.27/0.78    spl6_188 <=> ! [X3] : (m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1)) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_188])])).
% 3.27/0.78  fof(f3578,plain,(
% 3.27/0.78    spl6_188 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40 | ~spl6_60 | ~spl6_61 | ~spl6_87),
% 3.27/0.78    inference(avatar_split_clause,[],[f3573,f1621,f848,f833,f441,f151,f146,f141,f3576])).
% 3.27/0.78  fof(f141,plain,(
% 3.27/0.78    spl6_1 <=> v2_struct_0(sK0)),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 3.27/0.78  fof(f146,plain,(
% 3.27/0.78    spl6_2 <=> v2_pre_topc(sK0)),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 3.27/0.78  fof(f151,plain,(
% 3.27/0.78    spl6_3 <=> l1_pre_topc(sK0)),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 3.27/0.78  fof(f441,plain,(
% 3.27/0.78    spl6_40 <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 3.27/0.78  fof(f833,plain,(
% 3.27/0.78    spl6_60 <=> k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 3.27/0.78  fof(f848,plain,(
% 3.27/0.78    spl6_61 <=> u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0)),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 3.27/0.78  fof(f1621,plain,(
% 3.27/0.78    spl6_87 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).
% 3.27/0.78  fof(f3573,plain,(
% 3.27/0.78    ( ! [X3] : (m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1)) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40 | ~spl6_60 | ~spl6_61 | ~spl6_87)),
% 3.27/0.78    inference(forward_demodulation,[],[f3572,f835])).
% 3.27/0.78  fof(f835,plain,(
% 3.27/0.78    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~spl6_60),
% 3.27/0.78    inference(avatar_component_clause,[],[f833])).
% 3.27/0.78  fof(f3572,plain,(
% 3.27/0.78    ( ! [X3] : (m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1)) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40 | ~spl6_61 | ~spl6_87)),
% 3.27/0.78    inference(forward_demodulation,[],[f3571,f850])).
% 3.27/0.78  fof(f850,plain,(
% 3.27/0.78    u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0) | ~spl6_61),
% 3.27/0.78    inference(avatar_component_clause,[],[f848])).
% 3.27/0.78  fof(f3571,plain,(
% 3.27/0.78    ( ! [X3] : (m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1)) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40 | ~spl6_87)),
% 3.27/0.78    inference(subsumption_resolution,[],[f495,f1622])).
% 3.27/0.78  fof(f1622,plain,(
% 3.27/0.78    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_87),
% 3.27/0.78    inference(avatar_component_clause,[],[f1621])).
% 3.27/0.78  fof(f495,plain,(
% 3.27/0.78    ( ! [X3] : (m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1)) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40)),
% 3.27/0.78    inference(subsumption_resolution,[],[f494,f143])).
% 3.27/0.78  fof(f143,plain,(
% 3.27/0.78    ~v2_struct_0(sK0) | spl6_1),
% 3.27/0.78    inference(avatar_component_clause,[],[f141])).
% 3.27/0.78  fof(f494,plain,(
% 3.27/0.78    ( ! [X3] : (m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1)) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_40)),
% 3.27/0.78    inference(subsumption_resolution,[],[f493,f148])).
% 3.27/0.78  fof(f148,plain,(
% 3.27/0.78    v2_pre_topc(sK0) | ~spl6_2),
% 3.27/0.78    inference(avatar_component_clause,[],[f146])).
% 3.27/0.78  fof(f493,plain,(
% 3.27/0.78    ( ! [X3] : (m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1)) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_40)),
% 3.27/0.78    inference(subsumption_resolution,[],[f476,f153])).
% 3.27/0.78  fof(f153,plain,(
% 3.27/0.78    l1_pre_topc(sK0) | ~spl6_3),
% 3.27/0.78    inference(avatar_component_clause,[],[f151])).
% 3.27/0.78  fof(f476,plain,(
% 3.27/0.78    ( ! [X3] : (m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~r1_xboole_0(u1_struct_0(X3),u1_struct_0(sK1)) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_40),
% 3.27/0.78    inference(superposition,[],[f112,f443])).
% 3.27/0.78  fof(f443,plain,(
% 3.27/0.78    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~spl6_40),
% 3.27/0.78    inference(avatar_component_clause,[],[f441])).
% 3.27/0.78  fof(f112,plain,(
% 3.27/0.78    ( ! [X2,X0,X1] : (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.78    inference(cnf_transformation,[],[f45])).
% 3.27/0.78  fof(f45,plain,(
% 3.27/0.78    ! [X0] : (! [X1] : (! [X2] : ((m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/0.78    inference(flattening,[],[f44])).
% 3.27/0.78  fof(f44,plain,(
% 3.27/0.78    ! [X0] : (! [X1] : (! [X2] : (((m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))) | ~r1_xboole_0(u1_struct_0(X2),X1)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.27/0.78    inference(ennf_transformation,[],[f19])).
% 3.27/0.78  fof(f19,axiom,(
% 3.27/0.78    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))))),
% 3.27/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_tmap_1)).
% 3.27/0.78  fof(f3432,plain,(
% 3.27/0.78    ~spl6_179 | spl6_34 | ~spl6_61 | ~spl6_99),
% 3.27/0.78    inference(avatar_split_clause,[],[f3295,f1868,f848,f384,f3429])).
% 3.27/0.78  fof(f384,plain,(
% 3.27/0.78    spl6_34 <=> m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 3.27/0.78  fof(f3295,plain,(
% 3.27/0.78    ~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | (spl6_34 | ~spl6_61 | ~spl6_99)),
% 3.27/0.78    inference(forward_demodulation,[],[f3294,f1870])).
% 3.27/0.78  fof(f3294,plain,(
% 3.27/0.78    ~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | (spl6_34 | ~spl6_61)),
% 3.27/0.78    inference(forward_demodulation,[],[f386,f850])).
% 3.27/0.78  fof(f386,plain,(
% 3.27/0.78    ~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))))) | spl6_34),
% 3.27/0.78    inference(avatar_component_clause,[],[f384])).
% 3.27/0.78  fof(f3289,plain,(
% 3.27/0.78    spl6_5 | ~spl6_7 | ~spl6_167 | spl6_172 | ~spl6_178),
% 3.27/0.78    inference(avatar_contradiction_clause,[],[f3288])).
% 3.27/0.78  fof(f3288,plain,(
% 3.27/0.78    $false | (spl6_5 | ~spl6_7 | ~spl6_167 | spl6_172 | ~spl6_178)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3287,f163])).
% 3.27/0.78  fof(f3287,plain,(
% 3.27/0.78    v2_struct_0(sK2) | (~spl6_7 | ~spl6_167 | spl6_172 | ~spl6_178)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3286,f173])).
% 3.27/0.78  fof(f3286,plain,(
% 3.27/0.78    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | (~spl6_167 | spl6_172 | ~spl6_178)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3279,f3096])).
% 3.27/0.78  fof(f3279,plain,(
% 3.27/0.78    ~r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | (spl6_172 | ~spl6_178)),
% 3.27/0.78    inference(resolution,[],[f3212,f3153])).
% 3.27/0.78  fof(f3153,plain,(
% 3.27/0.78    ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(sK0)) | spl6_172),
% 3.27/0.78    inference(avatar_component_clause,[],[f3151])).
% 3.27/0.78  fof(f3151,plain,(
% 3.27/0.78    spl6_172 <=> v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(sK0))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_172])])).
% 3.27/0.78  fof(f3212,plain,(
% 3.27/0.78    ( ! [X1] : (v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X1),u1_struct_0(X1),u1_struct_0(sK0)) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1)) ) | ~spl6_178),
% 3.27/0.78    inference(avatar_component_clause,[],[f3211])).
% 3.27/0.78  fof(f3211,plain,(
% 3.27/0.78    spl6_178 <=> ! [X1] : (v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X1),u1_struct_0(X1),u1_struct_0(sK0)) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_178])])).
% 3.27/0.78  fof(f3213,plain,(
% 3.27/0.78    spl6_178 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40 | ~spl6_60 | ~spl6_61 | ~spl6_87),
% 3.27/0.78    inference(avatar_split_clause,[],[f3208,f1621,f848,f833,f441,f151,f146,f141,f3211])).
% 3.27/0.78  fof(f3208,plain,(
% 3.27/0.78    ( ! [X1] : (v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X1),u1_struct_0(X1),u1_struct_0(sK0)) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40 | ~spl6_60 | ~spl6_61 | ~spl6_87)),
% 3.27/0.78    inference(forward_demodulation,[],[f3207,f835])).
% 3.27/0.78  fof(f3207,plain,(
% 3.27/0.78    ( ! [X1] : (v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(sK0)) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40 | ~spl6_61 | ~spl6_87)),
% 3.27/0.78    inference(forward_demodulation,[],[f3206,f850])).
% 3.27/0.78  fof(f3206,plain,(
% 3.27/0.78    ( ! [X1] : (v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40 | ~spl6_87)),
% 3.27/0.78    inference(subsumption_resolution,[],[f489,f1622])).
% 3.27/0.78  fof(f489,plain,(
% 3.27/0.78    ( ! [X1] : (v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40)),
% 3.27/0.78    inference(subsumption_resolution,[],[f488,f143])).
% 3.27/0.78  fof(f488,plain,(
% 3.27/0.78    ( ! [X1] : (v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_40)),
% 3.27/0.78    inference(subsumption_resolution,[],[f487,f148])).
% 3.27/0.78  fof(f487,plain,(
% 3.27/0.78    ( ! [X1] : (v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_40)),
% 3.27/0.78    inference(subsumption_resolution,[],[f474,f153])).
% 3.27/0.78  fof(f474,plain,(
% 3.27/0.78    ( ! [X1] : (v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_40),
% 3.27/0.78    inference(superposition,[],[f110,f443])).
% 3.27/0.78  fof(f110,plain,(
% 3.27/0.78    ( ! [X2,X0,X1] : (v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.78    inference(cnf_transformation,[],[f45])).
% 3.27/0.78  fof(f3154,plain,(
% 3.27/0.78    ~spl6_172 | spl6_32 | ~spl6_61 | ~spl6_99),
% 3.27/0.78    inference(avatar_split_clause,[],[f3141,f1868,f848,f376,f3151])).
% 3.27/0.78  fof(f376,plain,(
% 3.27/0.78    spl6_32 <=> v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 3.27/0.78  fof(f3141,plain,(
% 3.27/0.78    ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(sK0)) | (spl6_32 | ~spl6_61 | ~spl6_99)),
% 3.27/0.78    inference(forward_demodulation,[],[f3140,f1870])).
% 3.27/0.78  fof(f3140,plain,(
% 3.27/0.78    ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(sK0)) | (spl6_32 | ~spl6_61)),
% 3.27/0.78    inference(forward_demodulation,[],[f378,f850])).
% 3.27/0.78  fof(f378,plain,(
% 3.27/0.78    ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))) | spl6_32),
% 3.27/0.78    inference(avatar_component_clause,[],[f376])).
% 3.27/0.78  fof(f3138,plain,(
% 3.27/0.78    ~spl6_10 | spl6_170),
% 3.27/0.78    inference(avatar_contradiction_clause,[],[f3137])).
% 3.27/0.78  fof(f3137,plain,(
% 3.27/0.78    $false | (~spl6_10 | spl6_170)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3135,f193])).
% 3.27/0.78  fof(f193,plain,(
% 3.27/0.78    l1_pre_topc(sK1) | ~spl6_10),
% 3.27/0.78    inference(avatar_component_clause,[],[f191])).
% 3.27/0.78  fof(f191,plain,(
% 3.27/0.78    spl6_10 <=> l1_pre_topc(sK1)),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 3.27/0.78  fof(f3135,plain,(
% 3.27/0.78    ~l1_pre_topc(sK1) | spl6_170),
% 3.27/0.78    inference(resolution,[],[f3114,f89])).
% 3.27/0.78  fof(f89,plain,(
% 3.27/0.78    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.27/0.78    inference(cnf_transformation,[],[f27])).
% 3.27/0.78  fof(f27,plain,(
% 3.27/0.78    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.27/0.78    inference(ennf_transformation,[],[f1])).
% 3.27/0.78  fof(f1,axiom,(
% 3.27/0.78    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.27/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 3.27/0.78  fof(f3114,plain,(
% 3.27/0.78    ~l1_struct_0(sK1) | spl6_170),
% 3.27/0.78    inference(avatar_component_clause,[],[f3112])).
% 3.27/0.78  fof(f3112,plain,(
% 3.27/0.78    spl6_170 <=> l1_struct_0(sK1)),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_170])])).
% 3.27/0.78  fof(f3120,plain,(
% 3.27/0.78    ~spl6_11 | spl6_169),
% 3.27/0.78    inference(avatar_contradiction_clause,[],[f3119])).
% 3.27/0.78  fof(f3119,plain,(
% 3.27/0.78    $false | (~spl6_11 | spl6_169)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3117,f199])).
% 3.27/0.78  fof(f199,plain,(
% 3.27/0.78    l1_pre_topc(sK2) | ~spl6_11),
% 3.27/0.78    inference(avatar_component_clause,[],[f197])).
% 3.27/0.78  fof(f197,plain,(
% 3.27/0.78    spl6_11 <=> l1_pre_topc(sK2)),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 3.27/0.78  fof(f3117,plain,(
% 3.27/0.78    ~l1_pre_topc(sK2) | spl6_169),
% 3.27/0.78    inference(resolution,[],[f3110,f89])).
% 3.27/0.78  fof(f3110,plain,(
% 3.27/0.78    ~l1_struct_0(sK2) | spl6_169),
% 3.27/0.78    inference(avatar_component_clause,[],[f3108])).
% 3.27/0.78  fof(f3108,plain,(
% 3.27/0.78    spl6_169 <=> l1_struct_0(sK2)),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_169])])).
% 3.27/0.78  fof(f3115,plain,(
% 3.27/0.78    ~spl6_169 | ~spl6_170 | ~spl6_56 | spl6_167),
% 3.27/0.78    inference(avatar_split_clause,[],[f3102,f3095,f809,f3112,f3108])).
% 3.27/0.78  fof(f809,plain,(
% 3.27/0.78    spl6_56 <=> r1_tsep_1(sK2,sK1)),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).
% 3.27/0.78  fof(f3102,plain,(
% 3.27/0.78    ~l1_struct_0(sK1) | ~l1_struct_0(sK2) | (~spl6_56 | spl6_167)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3101,f811])).
% 3.27/0.78  fof(f811,plain,(
% 3.27/0.78    r1_tsep_1(sK2,sK1) | ~spl6_56),
% 3.27/0.78    inference(avatar_component_clause,[],[f809])).
% 3.27/0.78  fof(f3101,plain,(
% 3.27/0.78    ~r1_tsep_1(sK2,sK1) | ~l1_struct_0(sK1) | ~l1_struct_0(sK2) | spl6_167),
% 3.27/0.78    inference(resolution,[],[f3097,f87])).
% 3.27/0.78  fof(f87,plain,(
% 3.27/0.78    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.27/0.78    inference(cnf_transformation,[],[f66])).
% 3.27/0.78  fof(f66,plain,(
% 3.27/0.78    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.27/0.78    inference(nnf_transformation,[],[f26])).
% 3.27/0.78  fof(f26,plain,(
% 3.27/0.78    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.27/0.78    inference(ennf_transformation,[],[f9])).
% 3.27/0.78  fof(f9,axiom,(
% 3.27/0.78    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 3.27/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 3.27/0.78  fof(f3097,plain,(
% 3.27/0.78    ~r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | spl6_167),
% 3.27/0.78    inference(avatar_component_clause,[],[f3095])).
% 3.27/0.78  fof(f3098,plain,(
% 3.27/0.78    ~spl6_167 | spl6_5 | ~spl6_7 | spl6_102 | ~spl6_166),
% 3.27/0.78    inference(avatar_split_clause,[],[f3093,f3044,f1912,f171,f161,f3095])).
% 3.27/0.78  fof(f1912,plain,(
% 3.27/0.78    spl6_102 <=> v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k8_tmap_1(sK0,sK1))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).
% 3.27/0.78  fof(f3044,plain,(
% 3.27/0.78    spl6_166 <=> ! [X2] : (v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X2),X2,k8_tmap_1(sK0,sK1)) | ~r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2))),
% 3.27/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_166])])).
% 3.27/0.78  fof(f3093,plain,(
% 3.27/0.78    ~r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | (spl6_5 | ~spl6_7 | spl6_102 | ~spl6_166)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3092,f163])).
% 3.27/0.78  fof(f3092,plain,(
% 3.27/0.78    ~r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK2) | (~spl6_7 | spl6_102 | ~spl6_166)),
% 3.27/0.78    inference(subsumption_resolution,[],[f3091,f173])).
% 3.27/0.78  fof(f3091,plain,(
% 3.27/0.78    ~r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | (spl6_102 | ~spl6_166)),
% 3.27/0.78    inference(resolution,[],[f3045,f1914])).
% 3.27/0.78  fof(f1914,plain,(
% 3.27/0.78    ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k8_tmap_1(sK0,sK1)) | spl6_102),
% 3.27/0.78    inference(avatar_component_clause,[],[f1912])).
% 3.27/0.78  fof(f3045,plain,(
% 3.27/0.78    ( ! [X2] : (v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X2),X2,k8_tmap_1(sK0,sK1)) | ~r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2)) ) | ~spl6_166),
% 3.27/0.78    inference(avatar_component_clause,[],[f3044])).
% 3.27/0.80  fof(f3046,plain,(
% 3.27/0.80    spl6_166 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40 | ~spl6_60 | ~spl6_87),
% 3.27/0.80    inference(avatar_split_clause,[],[f2998,f1621,f833,f441,f151,f146,f141,f3044])).
% 3.27/0.80  fof(f2998,plain,(
% 3.27/0.80    ( ! [X2] : (v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X2),X2,k8_tmap_1(sK0,sK1)) | ~r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40 | ~spl6_60 | ~spl6_87)),
% 3.27/0.80    inference(forward_demodulation,[],[f2997,f835])).
% 3.27/0.80  fof(f2997,plain,(
% 3.27/0.80    ( ! [X2] : (v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1)) | ~r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40 | ~spl6_87)),
% 3.27/0.80    inference(subsumption_resolution,[],[f492,f1622])).
% 3.27/0.80  fof(f492,plain,(
% 3.27/0.80    ( ! [X2] : (v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1)) | ~r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40)),
% 3.27/0.80    inference(subsumption_resolution,[],[f491,f143])).
% 3.27/0.80  fof(f491,plain,(
% 3.27/0.80    ( ! [X2] : (v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1)) | ~r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_40)),
% 3.27/0.80    inference(subsumption_resolution,[],[f490,f148])).
% 3.27/0.80  fof(f490,plain,(
% 3.27/0.80    ( ! [X2] : (v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1)) | ~r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_40)),
% 3.27/0.80    inference(subsumption_resolution,[],[f475,f153])).
% 3.27/0.80  fof(f475,plain,(
% 3.27/0.80    ( ! [X2] : (v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1)) | ~r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_40),
% 3.27/0.80    inference(superposition,[],[f111,f443])).
% 3.27/0.80  fof(f111,plain,(
% 3.27/0.80    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f45])).
% 3.27/0.80  fof(f2563,plain,(
% 3.27/0.80    spl6_141 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40 | ~spl6_60 | ~spl6_87),
% 3.27/0.80    inference(avatar_split_clause,[],[f2554,f1621,f833,f441,f151,f146,f141,f2561])).
% 3.27/0.80  fof(f2554,plain,(
% 3.27/0.80    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40 | ~spl6_60 | ~spl6_87)),
% 3.27/0.80    inference(forward_demodulation,[],[f2553,f835])).
% 3.27/0.80  fof(f2553,plain,(
% 3.27/0.80    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40 | ~spl6_87)),
% 3.27/0.80    inference(subsumption_resolution,[],[f486,f1622])).
% 3.27/0.80  fof(f486,plain,(
% 3.27/0.80    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_40)),
% 3.27/0.80    inference(subsumption_resolution,[],[f485,f143])).
% 3.27/0.80  fof(f485,plain,(
% 3.27/0.80    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_40)),
% 3.27/0.80    inference(subsumption_resolution,[],[f484,f148])).
% 3.27/0.80  fof(f484,plain,(
% 3.27/0.80    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_40)),
% 3.27/0.80    inference(subsumption_resolution,[],[f473,f153])).
% 3.27/0.80  fof(f473,plain,(
% 3.27/0.80    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_40),
% 3.27/0.80    inference(superposition,[],[f109,f443])).
% 3.27/0.80  fof(f109,plain,(
% 3.27/0.80    ( ! [X2,X0,X1] : (v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f45])).
% 3.27/0.80  fof(f1915,plain,(
% 3.27/0.80    ~spl6_102 | spl6_33 | ~spl6_99),
% 3.27/0.80    inference(avatar_split_clause,[],[f1884,f1868,f380,f1912])).
% 3.27/0.80  fof(f380,plain,(
% 3.27/0.80    spl6_33 <=> v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))),
% 3.27/0.80    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 3.27/0.80  fof(f1884,plain,(
% 3.27/0.80    ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k8_tmap_1(sK0,sK1)) | (spl6_33 | ~spl6_99)),
% 3.27/0.80    inference(backward_demodulation,[],[f382,f1870])).
% 3.27/0.80  fof(f382,plain,(
% 3.27/0.80    ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1)) | spl6_33),
% 3.27/0.80    inference(avatar_component_clause,[],[f380])).
% 3.27/0.80  fof(f1877,plain,(
% 3.27/0.80    spl6_1 | ~spl6_78 | ~spl6_98),
% 3.27/0.80    inference(avatar_contradiction_clause,[],[f1876])).
% 3.27/0.80  fof(f1876,plain,(
% 3.27/0.80    $false | (spl6_1 | ~spl6_78 | ~spl6_98)),
% 3.27/0.80    inference(subsumption_resolution,[],[f1875,f143])).
% 3.27/0.80  fof(f1875,plain,(
% 3.27/0.80    v2_struct_0(sK0) | (~spl6_78 | ~spl6_98)),
% 3.27/0.80    inference(subsumption_resolution,[],[f1873,f1459])).
% 3.27/0.80  fof(f1459,plain,(
% 3.27/0.80    l1_struct_0(sK0) | ~spl6_78),
% 3.27/0.80    inference(avatar_component_clause,[],[f1458])).
% 3.27/0.80  fof(f1458,plain,(
% 3.27/0.80    spl6_78 <=> l1_struct_0(sK0)),
% 3.27/0.80    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 3.27/0.80  fof(f1873,plain,(
% 3.27/0.80    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl6_98),
% 3.27/0.80    inference(resolution,[],[f1866,f94])).
% 3.27/0.80  fof(f94,plain,(
% 3.27/0.80    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f33])).
% 3.27/0.80  fof(f33,plain,(
% 3.27/0.80    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.27/0.80    inference(flattening,[],[f32])).
% 3.27/0.80  fof(f32,plain,(
% 3.27/0.80    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.27/0.80    inference(ennf_transformation,[],[f4])).
% 3.27/0.80  fof(f4,axiom,(
% 3.27/0.80    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.27/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 3.27/0.80  fof(f1866,plain,(
% 3.27/0.80    v1_xboole_0(u1_struct_0(sK0)) | ~spl6_98),
% 3.27/0.80    inference(avatar_component_clause,[],[f1864])).
% 3.27/0.80  fof(f1864,plain,(
% 3.27/0.80    spl6_98 <=> v1_xboole_0(u1_struct_0(sK0))),
% 3.27/0.80    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).
% 3.27/0.80  fof(f1871,plain,(
% 3.27/0.80    spl6_98 | spl6_99 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_40 | ~spl6_60 | ~spl6_61),
% 3.27/0.80    inference(avatar_split_clause,[],[f1857,f848,f833,f441,f166,f151,f146,f141,f1868,f1864])).
% 3.27/0.80  fof(f166,plain,(
% 3.27/0.80    spl6_6 <=> m1_pre_topc(sK1,sK0)),
% 3.27/0.80    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 3.27/0.80  fof(f1857,plain,(
% 3.27/0.80    k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_40 | ~spl6_60 | ~spl6_61)),
% 3.27/0.80    inference(forward_demodulation,[],[f1159,f835])).
% 3.27/0.80  fof(f1159,plain,(
% 3.27/0.80    v1_xboole_0(u1_struct_0(sK0)) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_40 | ~spl6_61)),
% 3.27/0.80    inference(forward_demodulation,[],[f1158,f850])).
% 3.27/0.80  fof(f1158,plain,(
% 3.27/0.80    v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_40)),
% 3.27/0.80    inference(duplicate_literal_removal,[],[f1157])).
% 3.27/0.80  fof(f1157,plain,(
% 3.27/0.80    v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_40)),
% 3.27/0.80    inference(forward_demodulation,[],[f1156,f443])).
% 3.27/0.80  fof(f1156,plain,(
% 3.27/0.80    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6)),
% 3.27/0.80    inference(subsumption_resolution,[],[f1155,f153])).
% 3.27/0.80  fof(f1155,plain,(
% 3.27/0.80    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | v1_xboole_0(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) | (spl6_1 | ~spl6_2 | ~spl6_6)),
% 3.27/0.80    inference(subsumption_resolution,[],[f1154,f143])).
% 3.27/0.80  fof(f1154,plain,(
% 3.27/0.80    v2_struct_0(sK0) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | v1_xboole_0(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) | (~spl6_2 | ~spl6_6)),
% 3.27/0.80    inference(subsumption_resolution,[],[f1148,f148])).
% 3.27/0.80  fof(f1148,plain,(
% 3.27/0.80    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | v1_xboole_0(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) | ~spl6_6),
% 3.27/0.80    inference(resolution,[],[f701,f168])).
% 3.27/0.80  fof(f168,plain,(
% 3.27/0.80    m1_pre_topc(sK1,sK0) | ~spl6_6),
% 3.27/0.80    inference(avatar_component_clause,[],[f166])).
% 3.27/0.80  fof(f701,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k9_tmap_1(X0,X1) = k7_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X0) | v1_xboole_0(u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))) )),
% 3.27/0.80    inference(subsumption_resolution,[],[f700,f92])).
% 3.27/0.80  fof(f92,plain,(
% 3.27/0.80    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f30])).
% 3.27/0.80  fof(f30,plain,(
% 3.27/0.80    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.27/0.80    inference(ennf_transformation,[],[f20])).
% 3.27/0.80  fof(f20,axiom,(
% 3.27/0.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.27/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 3.27/0.80  fof(f700,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k9_tmap_1(X0,X1) = k7_tmap_1(X0,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v1_xboole_0(u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 3.27/0.80    inference(subsumption_resolution,[],[f699,f126])).
% 3.27/0.80  fof(f126,plain,(
% 3.27/0.80    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f55])).
% 3.27/0.80  fof(f55,plain,(
% 3.27/0.80    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/0.80    inference(flattening,[],[f54])).
% 3.27/0.80  fof(f54,plain,(
% 3.27/0.80    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.27/0.80    inference(ennf_transformation,[],[f12])).
% 3.27/0.80  fof(f12,axiom,(
% 3.27/0.80    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 3.27/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 3.27/0.80  fof(f699,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k9_tmap_1(X0,X1) = k7_tmap_1(X0,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | ~v1_funct_2(k7_tmap_1(X0,u1_struct_0(X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))) | v1_xboole_0(u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 3.27/0.80    inference(duplicate_literal_removal,[],[f692])).
% 3.27/0.80  fof(f692,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k9_tmap_1(X0,X1) = k7_tmap_1(X0,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | ~v1_funct_2(k7_tmap_1(X0,u1_struct_0(X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))) | v1_xboole_0(u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(resolution,[],[f680,f127])).
% 3.27/0.80  fof(f127,plain,(
% 3.27/0.80    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f55])).
% 3.27/0.80  fof(f680,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~m1_subset_1(k7_tmap_1(X1,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0)))))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | k9_tmap_1(X1,X0) = k7_tmap_1(X1,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~v1_funct_2(k7_tmap_1(X1,u1_struct_0(X0)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0)))) | v1_xboole_0(u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X0)))) )),
% 3.27/0.80    inference(subsumption_resolution,[],[f406,f257])).
% 3.27/0.80  fof(f257,plain,(
% 3.27/0.80    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0)) )),
% 3.27/0.80    inference(duplicate_literal_removal,[],[f256])).
% 3.27/0.80  fof(f256,plain,(
% 3.27/0.80    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.27/0.80    inference(resolution,[],[f125,f92])).
% 3.27/0.80  fof(f125,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f55])).
% 3.27/0.80  fof(f406,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | k9_tmap_1(X1,X0) = k7_tmap_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k7_tmap_1(X1,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0)))))) | ~v1_funct_2(k7_tmap_1(X1,u1_struct_0(X0)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0)))) | ~v1_funct_1(k7_tmap_1(X1,u1_struct_0(X0))) | v1_xboole_0(u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X0)))) )),
% 3.27/0.80    inference(subsumption_resolution,[],[f405,f116])).
% 3.27/0.80  fof(f116,plain,(
% 3.27/0.80    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f49])).
% 3.27/0.80  fof(f49,plain,(
% 3.27/0.80    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/0.80    inference(flattening,[],[f48])).
% 3.27/0.80  fof(f48,plain,(
% 3.27/0.80    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.27/0.80    inference(ennf_transformation,[],[f14])).
% 3.27/0.80  fof(f14,axiom,(
% 3.27/0.80    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 3.27/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).
% 3.27/0.80  fof(f405,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | k9_tmap_1(X1,X0) = k7_tmap_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k7_tmap_1(X1,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0)))))) | ~v1_funct_2(k7_tmap_1(X1,u1_struct_0(X0)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0)))) | ~v1_funct_1(k7_tmap_1(X1,u1_struct_0(X0))) | ~v1_funct_1(k9_tmap_1(X1,X0)) | v1_xboole_0(u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X0)))) )),
% 3.27/0.80    inference(subsumption_resolution,[],[f404,f117])).
% 3.27/0.80  fof(f117,plain,(
% 3.27/0.80    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f49])).
% 3.27/0.80  fof(f404,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | k9_tmap_1(X1,X0) = k7_tmap_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k7_tmap_1(X1,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0)))))) | ~v1_funct_2(k7_tmap_1(X1,u1_struct_0(X0)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0)))) | ~v1_funct_1(k7_tmap_1(X1,u1_struct_0(X0))) | ~v1_funct_2(k9_tmap_1(X1,X0),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0))) | ~v1_funct_1(k9_tmap_1(X1,X0)) | v1_xboole_0(u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X0)))) )),
% 3.27/0.80    inference(subsumption_resolution,[],[f403,f118])).
% 3.27/0.80  fof(f118,plain,(
% 3.27/0.80    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f49])).
% 3.27/0.80  fof(f403,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | k9_tmap_1(X1,X0) = k7_tmap_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k7_tmap_1(X1,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0)))))) | ~v1_funct_2(k7_tmap_1(X1,u1_struct_0(X0)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0)))) | ~v1_funct_1(k7_tmap_1(X1,u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0))))) | ~v1_funct_2(k9_tmap_1(X1,X0),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0))) | ~v1_funct_1(k9_tmap_1(X1,X0)) | v1_xboole_0(u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X0)))) )),
% 3.27/0.80    inference(resolution,[],[f399,f132])).
% 3.27/0.80  fof(f132,plain,(
% 3.27/0.80    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f77])).
% 3.27/0.80  fof(f77,plain,(
% 3.27/0.80    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.27/0.80    inference(nnf_transformation,[],[f61])).
% 3.27/0.80  fof(f61,plain,(
% 3.27/0.80    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.27/0.80    inference(flattening,[],[f60])).
% 3.27/0.80  fof(f60,plain,(
% 3.27/0.80    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.27/0.80    inference(ennf_transformation,[],[f5])).
% 3.27/0.80  fof(f5,axiom,(
% 3.27/0.80    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.27/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 3.27/0.80  fof(f399,plain,(
% 3.27/0.80    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(subsumption_resolution,[],[f398,f116])).
% 3.27/0.80  fof(f398,plain,(
% 3.27/0.80    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(subsumption_resolution,[],[f397,f117])).
% 3.27/0.80  fof(f397,plain,(
% 3.27/0.80    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(subsumption_resolution,[],[f396,f118])).
% 3.27/0.80  fof(f396,plain,(
% 3.27/0.80    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(subsumption_resolution,[],[f137,f92])).
% 3.27/0.80  fof(f137,plain,(
% 3.27/0.80    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(equality_resolution,[],[f136])).
% 3.27/0.80  fof(f136,plain,(
% 3.27/0.80    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(equality_resolution,[],[f102])).
% 3.27/0.80  fof(f102,plain,(
% 3.27/0.80    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f76])).
% 3.27/0.80  fof(f76,plain,(
% 3.27/0.80    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2))) & u1_struct_0(X1) = sK5(X0,X1,X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f74,f75])).
% 3.27/0.80  fof(f75,plain,(
% 3.27/0.80    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2))) & u1_struct_0(X1) = sK5(X0,X1,X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.27/0.80    introduced(choice_axiom,[])).
% 3.27/0.80  fof(f74,plain,(
% 3.27/0.80    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/0.80    inference(rectify,[],[f73])).
% 3.27/0.80  fof(f73,plain,(
% 3.27/0.80    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/0.80    inference(nnf_transformation,[],[f39])).
% 3.27/0.80  fof(f39,plain,(
% 3.27/0.80    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/0.80    inference(flattening,[],[f38])).
% 3.27/0.80  fof(f38,plain,(
% 3.27/0.80    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.27/0.80    inference(ennf_transformation,[],[f8])).
% 3.27/0.80  fof(f8,axiom,(
% 3.27/0.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 3.27/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).
% 3.27/0.80  fof(f1642,plain,(
% 3.27/0.80    ~spl6_3 | ~spl6_6 | spl6_87),
% 3.27/0.80    inference(avatar_contradiction_clause,[],[f1641])).
% 3.27/0.80  fof(f1641,plain,(
% 3.27/0.80    $false | (~spl6_3 | ~spl6_6 | spl6_87)),
% 3.27/0.80    inference(subsumption_resolution,[],[f1640,f153])).
% 3.27/0.80  fof(f1640,plain,(
% 3.27/0.80    ~l1_pre_topc(sK0) | (~spl6_6 | spl6_87)),
% 3.27/0.80    inference(subsumption_resolution,[],[f1638,f168])).
% 3.27/0.80  fof(f1638,plain,(
% 3.27/0.80    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl6_87),
% 3.27/0.80    inference(resolution,[],[f1623,f92])).
% 3.27/0.80  fof(f1623,plain,(
% 3.27/0.80    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_87),
% 3.27/0.80    inference(avatar_component_clause,[],[f1621])).
% 3.27/0.80  fof(f1469,plain,(
% 3.27/0.80    ~spl6_3 | spl6_78),
% 3.27/0.80    inference(avatar_contradiction_clause,[],[f1468])).
% 3.27/0.80  fof(f1468,plain,(
% 3.27/0.80    $false | (~spl6_3 | spl6_78)),
% 3.27/0.80    inference(subsumption_resolution,[],[f1466,f153])).
% 3.27/0.80  fof(f1466,plain,(
% 3.27/0.80    ~l1_pre_topc(sK0) | spl6_78),
% 3.27/0.80    inference(resolution,[],[f1460,f89])).
% 3.27/0.80  fof(f1460,plain,(
% 3.27/0.80    ~l1_struct_0(sK0) | spl6_78),
% 3.27/0.80    inference(avatar_component_clause,[],[f1458])).
% 3.27/0.80  fof(f851,plain,(
% 3.27/0.80    spl6_61 | ~spl6_6 | ~spl6_40 | ~spl6_58),
% 3.27/0.80    inference(avatar_split_clause,[],[f841,f819,f441,f166,f848])).
% 3.27/0.80  fof(f819,plain,(
% 3.27/0.80    spl6_58 <=> ! [X0] : (u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0))),
% 3.27/0.80    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 3.27/0.80  fof(f841,plain,(
% 3.27/0.80    u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0) | (~spl6_6 | ~spl6_40 | ~spl6_58)),
% 3.27/0.80    inference(forward_demodulation,[],[f837,f443])).
% 3.27/0.80  fof(f837,plain,(
% 3.27/0.80    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | (~spl6_6 | ~spl6_58)),
% 3.27/0.80    inference(resolution,[],[f820,f168])).
% 3.27/0.80  fof(f820,plain,(
% 3.27/0.80    ( ! [X0] : (~m1_pre_topc(X0,sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))) ) | ~spl6_58),
% 3.27/0.80    inference(avatar_component_clause,[],[f819])).
% 3.27/0.80  fof(f836,plain,(
% 3.27/0.80    spl6_60 | ~spl6_6 | ~spl6_57),
% 3.27/0.80    inference(avatar_split_clause,[],[f826,f814,f166,f833])).
% 3.27/0.80  fof(f814,plain,(
% 3.27/0.80    spl6_57 <=> ! [X0] : (k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0))),
% 3.27/0.80    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 3.27/0.80  fof(f826,plain,(
% 3.27/0.80    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) | (~spl6_6 | ~spl6_57)),
% 3.27/0.80    inference(resolution,[],[f815,f168])).
% 3.27/0.80  fof(f815,plain,(
% 3.27/0.80    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0))) ) | ~spl6_57),
% 3.27/0.80    inference(avatar_component_clause,[],[f814])).
% 3.27/0.80  fof(f821,plain,(
% 3.27/0.80    spl6_58 | spl6_1 | ~spl6_2 | ~spl6_3),
% 3.27/0.80    inference(avatar_split_clause,[],[f508,f151,f146,f141,f819])).
% 3.27/0.80  fof(f508,plain,(
% 3.27/0.80    ( ! [X0] : (u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 3.27/0.80    inference(subsumption_resolution,[],[f507,f143])).
% 3.27/0.80  fof(f507,plain,(
% 3.27/0.80    ( ! [X0] : (u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0)) ) | (~spl6_2 | ~spl6_3)),
% 3.27/0.80    inference(subsumption_resolution,[],[f505,f153])).
% 3.27/0.80  fof(f505,plain,(
% 3.27/0.80    ( ! [X0] : (~l1_pre_topc(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0)) ) | ~spl6_2),
% 3.27/0.80    inference(resolution,[],[f266,f148])).
% 3.27/0.80  fof(f266,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0)) )),
% 3.27/0.80    inference(duplicate_literal_removal,[],[f265])).
% 3.27/0.80  fof(f265,plain,(
% 3.27/0.80    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.27/0.80    inference(resolution,[],[f107,f92])).
% 3.27/0.80  fof(f107,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f43])).
% 3.27/0.80  fof(f43,plain,(
% 3.27/0.80    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/0.80    inference(flattening,[],[f42])).
% 3.27/0.80  fof(f42,plain,(
% 3.27/0.80    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.27/0.80    inference(ennf_transformation,[],[f18])).
% 3.27/0.80  fof(f18,axiom,(
% 3.27/0.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 3.27/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 3.27/0.80  fof(f816,plain,(
% 3.27/0.80    spl6_57 | spl6_1 | ~spl6_2 | ~spl6_3),
% 3.27/0.80    inference(avatar_split_clause,[],[f468,f151,f146,f141,f814])).
% 3.27/0.80  fof(f468,plain,(
% 3.27/0.80    ( ! [X0] : (k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 3.27/0.80    inference(subsumption_resolution,[],[f467,f143])).
% 3.27/0.80  fof(f467,plain,(
% 3.27/0.80    ( ! [X0] : (k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0)) ) | (~spl6_2 | ~spl6_3)),
% 3.27/0.80    inference(subsumption_resolution,[],[f465,f153])).
% 3.27/0.80  fof(f465,plain,(
% 3.27/0.80    ( ! [X0] : (~l1_pre_topc(sK0) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0)) ) | ~spl6_2),
% 3.27/0.80    inference(resolution,[],[f260,f148])).
% 3.27/0.80  fof(f260,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0)) )),
% 3.27/0.80    inference(duplicate_literal_removal,[],[f259])).
% 3.27/0.80  fof(f259,plain,(
% 3.27/0.80    ( ! [X0,X1] : (k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.27/0.80    inference(resolution,[],[f106,f92])).
% 3.27/0.80  fof(f106,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f41])).
% 3.27/0.80  fof(f41,plain,(
% 3.27/0.80    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/0.80    inference(flattening,[],[f40])).
% 3.27/0.80  fof(f40,plain,(
% 3.27/0.80    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.27/0.80    inference(ennf_transformation,[],[f6])).
% 3.27/0.80  fof(f6,axiom,(
% 3.27/0.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 3.27/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).
% 3.27/0.80  fof(f812,plain,(
% 3.27/0.80    spl6_56 | ~spl6_8 | ~spl6_10 | ~spl6_11),
% 3.27/0.80    inference(avatar_split_clause,[],[f807,f197,f191,f176,f809])).
% 3.27/0.80  fof(f176,plain,(
% 3.27/0.80    spl6_8 <=> r1_tsep_1(sK1,sK2)),
% 3.27/0.80    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 3.27/0.80  fof(f807,plain,(
% 3.27/0.80    r1_tsep_1(sK2,sK1) | (~spl6_8 | ~spl6_10 | ~spl6_11)),
% 3.27/0.80    inference(subsumption_resolution,[],[f806,f199])).
% 3.27/0.80  fof(f806,plain,(
% 3.27/0.80    r1_tsep_1(sK2,sK1) | ~l1_pre_topc(sK2) | (~spl6_8 | ~spl6_10)),
% 3.27/0.80    inference(subsumption_resolution,[],[f805,f193])).
% 3.27/0.80  fof(f805,plain,(
% 3.27/0.80    r1_tsep_1(sK2,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK2) | ~spl6_8),
% 3.27/0.80    inference(resolution,[],[f412,f178])).
% 3.27/0.80  fof(f178,plain,(
% 3.27/0.80    r1_tsep_1(sK1,sK2) | ~spl6_8),
% 3.27/0.80    inference(avatar_component_clause,[],[f176])).
% 3.27/0.80  fof(f412,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 3.27/0.80    inference(resolution,[],[f195,f89])).
% 3.27/0.80  fof(f195,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~l1_struct_0(X1) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.27/0.80    inference(resolution,[],[f128,f89])).
% 3.27/0.80  fof(f128,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~l1_struct_0(X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | r1_tsep_1(X1,X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f57])).
% 3.27/0.80  fof(f57,plain,(
% 3.27/0.80    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.27/0.80    inference(flattening,[],[f56])).
% 3.27/0.80  fof(f56,plain,(
% 3.27/0.80    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.27/0.80    inference(ennf_transformation,[],[f17])).
% 3.27/0.80  fof(f17,axiom,(
% 3.27/0.80    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 3.27/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 3.27/0.80  fof(f444,plain,(
% 3.27/0.80    spl6_40 | ~spl6_6 | ~spl6_38),
% 3.27/0.80    inference(avatar_split_clause,[],[f421,f415,f166,f441])).
% 3.27/0.80  fof(f415,plain,(
% 3.27/0.80    spl6_38 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0)))),
% 3.27/0.80    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 3.27/0.80  fof(f421,plain,(
% 3.27/0.80    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl6_6 | ~spl6_38)),
% 3.27/0.80    inference(resolution,[],[f416,f168])).
% 3.27/0.80  fof(f416,plain,(
% 3.27/0.80    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0))) ) | ~spl6_38),
% 3.27/0.80    inference(avatar_component_clause,[],[f415])).
% 3.27/0.80  fof(f417,plain,(
% 3.27/0.80    spl6_38 | spl6_1 | ~spl6_2 | ~spl6_3),
% 3.27/0.80    inference(avatar_split_clause,[],[f335,f151,f146,f141,f415])).
% 3.27/0.80  fof(f335,plain,(
% 3.27/0.80    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 3.27/0.80    inference(subsumption_resolution,[],[f334,f143])).
% 3.27/0.80  fof(f334,plain,(
% 3.27/0.80    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3)),
% 3.27/0.80    inference(subsumption_resolution,[],[f332,f153])).
% 3.27/0.80  fof(f332,plain,(
% 3.27/0.80    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0)) | v2_struct_0(sK0)) ) | ~spl6_2),
% 3.27/0.80    inference(resolution,[],[f330,f148])).
% 3.27/0.80  fof(f330,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(subsumption_resolution,[],[f329,f113])).
% 3.27/0.80  fof(f113,plain,(
% 3.27/0.80    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f47])).
% 3.27/0.80  fof(f47,plain,(
% 3.27/0.80    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/0.80    inference(flattening,[],[f46])).
% 3.27/0.80  fof(f46,plain,(
% 3.27/0.80    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.27/0.80    inference(ennf_transformation,[],[f13])).
% 3.27/0.80  fof(f13,axiom,(
% 3.27/0.80    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 3.27/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 3.27/0.80  fof(f329,plain,(
% 3.27/0.80    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(subsumption_resolution,[],[f328,f114])).
% 3.27/0.80  fof(f114,plain,(
% 3.27/0.80    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f47])).
% 3.27/0.80  fof(f328,plain,(
% 3.27/0.80    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(subsumption_resolution,[],[f327,f115])).
% 3.27/0.80  fof(f115,plain,(
% 3.27/0.80    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f47])).
% 3.27/0.80  fof(f327,plain,(
% 3.27/0.80    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(subsumption_resolution,[],[f135,f92])).
% 3.27/0.80  fof(f135,plain,(
% 3.27/0.80    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(equality_resolution,[],[f134])).
% 3.27/0.80  fof(f134,plain,(
% 3.27/0.80    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(equality_resolution,[],[f98])).
% 3.27/0.80  fof(f98,plain,(
% 3.27/0.80    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f72])).
% 3.27/0.80  fof(f72,plain,(
% 3.27/0.80    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK4(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK4(X0,X1,X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f70,f71])).
% 3.27/0.80  fof(f71,plain,(
% 3.27/0.80    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK4(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK4(X0,X1,X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.27/0.80    introduced(choice_axiom,[])).
% 3.27/0.80  fof(f70,plain,(
% 3.27/0.80    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/0.80    inference(rectify,[],[f69])).
% 3.27/0.80  fof(f69,plain,(
% 3.27/0.80    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/0.80    inference(nnf_transformation,[],[f37])).
% 3.27/0.80  fof(f37,plain,(
% 3.27/0.80    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/0.80    inference(flattening,[],[f36])).
% 3.27/0.80  fof(f36,plain,(
% 3.27/0.80    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.27/0.80    inference(ennf_transformation,[],[f7])).
% 3.27/0.80  fof(f7,axiom,(
% 3.27/0.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 3.27/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).
% 3.27/0.80  fof(f387,plain,(
% 3.27/0.80    ~spl6_31 | ~spl6_32 | ~spl6_33 | ~spl6_34),
% 3.27/0.80    inference(avatar_split_clause,[],[f86,f384,f380,f376,f372])).
% 3.27/0.80  fof(f86,plain,(
% 3.27/0.80    ~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))),
% 3.27/0.80    inference(cnf_transformation,[],[f65])).
% 3.27/0.80  fof(f65,plain,(
% 3.27/0.80    (((~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))) & r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.27/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f64,f63,f62])).
% 3.27/0.80  fof(f62,plain,(
% 3.27/0.80    ? [X0] : (? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,X1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),X2,k8_tmap_1(sK0,X1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,X1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.27/0.80    introduced(choice_axiom,[])).
% 3.27/0.80  fof(f63,plain,(
% 3.27/0.80    ? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,X1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),X2,k8_tmap_1(sK0,X1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,X1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : ((~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),X2,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2))) & r1_tsep_1(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 3.27/0.80    introduced(choice_axiom,[])).
% 3.27/0.80  fof(f64,plain,(
% 3.27/0.80    ? [X2] : ((~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),X2,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2))) & r1_tsep_1(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => ((~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))) & r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 3.27/0.80    introduced(choice_axiom,[])).
% 3.27/0.80  fof(f25,plain,(
% 3.27/0.80    ? [X0] : (? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.27/0.80    inference(flattening,[],[f24])).
% 3.27/0.80  fof(f24,plain,(
% 3.27/0.80    ? [X0] : (? [X1] : (? [X2] : (((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.27/0.80    inference(ennf_transformation,[],[f23])).
% 3.27/0.80  fof(f23,negated_conjecture,(
% 3.27/0.80    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)))))))),
% 3.27/0.80    inference(negated_conjecture,[],[f22])).
% 3.27/0.80  fof(f22,conjecture,(
% 3.27/0.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)))))))),
% 3.27/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_tmap_1)).
% 3.27/0.80  fof(f200,plain,(
% 3.27/0.80    spl6_11 | ~spl6_7 | ~spl6_9),
% 3.27/0.80    inference(avatar_split_clause,[],[f186,f182,f171,f197])).
% 3.27/0.80  fof(f182,plain,(
% 3.27/0.80    spl6_9 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0))),
% 3.27/0.80    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 3.27/0.80  fof(f186,plain,(
% 3.27/0.80    l1_pre_topc(sK2) | (~spl6_7 | ~spl6_9)),
% 3.27/0.80    inference(resolution,[],[f183,f173])).
% 3.27/0.80  fof(f183,plain,(
% 3.27/0.80    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) ) | ~spl6_9),
% 3.27/0.80    inference(avatar_component_clause,[],[f182])).
% 3.27/0.80  fof(f194,plain,(
% 3.27/0.80    spl6_10 | ~spl6_6 | ~spl6_9),
% 3.27/0.80    inference(avatar_split_clause,[],[f185,f182,f166,f191])).
% 3.27/0.80  fof(f185,plain,(
% 3.27/0.80    l1_pre_topc(sK1) | (~spl6_6 | ~spl6_9)),
% 3.27/0.80    inference(resolution,[],[f183,f168])).
% 3.27/0.80  fof(f184,plain,(
% 3.27/0.80    spl6_9 | ~spl6_3),
% 3.27/0.80    inference(avatar_split_clause,[],[f180,f151,f182])).
% 3.27/0.80  fof(f180,plain,(
% 3.27/0.80    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) ) | ~spl6_3),
% 3.27/0.80    inference(resolution,[],[f91,f153])).
% 3.27/0.80  fof(f91,plain,(
% 3.27/0.80    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 3.27/0.80    inference(cnf_transformation,[],[f29])).
% 3.27/0.80  fof(f29,plain,(
% 3.27/0.80    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.27/0.80    inference(ennf_transformation,[],[f2])).
% 3.27/0.80  fof(f2,axiom,(
% 3.27/0.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.27/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 3.27/0.80  fof(f179,plain,(
% 3.27/0.80    spl6_8),
% 3.27/0.80    inference(avatar_split_clause,[],[f85,f176])).
% 3.27/0.80  fof(f85,plain,(
% 3.27/0.80    r1_tsep_1(sK1,sK2)),
% 3.27/0.80    inference(cnf_transformation,[],[f65])).
% 3.27/0.80  fof(f174,plain,(
% 3.27/0.80    spl6_7),
% 3.27/0.80    inference(avatar_split_clause,[],[f84,f171])).
% 3.27/0.80  fof(f84,plain,(
% 3.27/0.80    m1_pre_topc(sK2,sK0)),
% 3.27/0.80    inference(cnf_transformation,[],[f65])).
% 3.27/0.80  fof(f169,plain,(
% 3.27/0.80    spl6_6),
% 3.27/0.80    inference(avatar_split_clause,[],[f82,f166])).
% 3.27/0.80  fof(f82,plain,(
% 3.27/0.80    m1_pre_topc(sK1,sK0)),
% 3.27/0.80    inference(cnf_transformation,[],[f65])).
% 3.27/0.80  fof(f164,plain,(
% 3.27/0.80    ~spl6_5),
% 3.27/0.80    inference(avatar_split_clause,[],[f83,f161])).
% 3.27/0.80  fof(f83,plain,(
% 3.27/0.80    ~v2_struct_0(sK2)),
% 3.27/0.80    inference(cnf_transformation,[],[f65])).
% 3.27/0.80  fof(f154,plain,(
% 3.27/0.80    spl6_3),
% 3.27/0.80    inference(avatar_split_clause,[],[f80,f151])).
% 3.27/0.80  fof(f80,plain,(
% 3.27/0.80    l1_pre_topc(sK0)),
% 3.27/0.80    inference(cnf_transformation,[],[f65])).
% 3.27/0.80  fof(f149,plain,(
% 3.27/0.80    spl6_2),
% 3.27/0.80    inference(avatar_split_clause,[],[f79,f146])).
% 3.27/0.80  fof(f79,plain,(
% 3.27/0.80    v2_pre_topc(sK0)),
% 3.27/0.80    inference(cnf_transformation,[],[f65])).
% 3.27/0.80  fof(f144,plain,(
% 3.27/0.80    ~spl6_1),
% 3.27/0.80    inference(avatar_split_clause,[],[f78,f141])).
% 3.27/0.80  fof(f78,plain,(
% 3.27/0.80    ~v2_struct_0(sK0)),
% 3.27/0.80    inference(cnf_transformation,[],[f65])).
% 3.27/0.80  % SZS output end Proof for theBenchmark
% 3.27/0.80  % (21750)------------------------------
% 3.27/0.80  % (21750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.80  % (21750)Termination reason: Refutation
% 3.27/0.80  
% 3.27/0.80  % (21750)Memory used [KB]: 9722
% 3.27/0.80  % (21750)Time elapsed: 0.356 s
% 3.27/0.80  % (21750)------------------------------
% 3.27/0.80  % (21750)------------------------------
% 3.27/0.81  % (21745)Success in time 0.446 s
%------------------------------------------------------------------------------
