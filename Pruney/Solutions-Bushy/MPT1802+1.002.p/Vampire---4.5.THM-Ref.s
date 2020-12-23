%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1802+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:35 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  278 ( 736 expanded)
%              Number of leaves         :   48 ( 305 expanded)
%              Depth                    :   22
%              Number of atoms          : 1422 (3150 expanded)
%              Number of equality atoms :   62 ( 166 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1093,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f120,f124,f128,f137,f141,f145,f189,f238,f242,f250,f254,f258,f262,f286,f290,f294,f298,f312,f321,f325,f467,f471,f484,f488,f556,f587,f595,f865,f889,f959,f1069,f1090,f1092])).

fof(f1092,plain,
    ( spl6_73
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_40
    | ~ spl6_42
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_74
    | ~ spl6_91 ),
    inference(avatar_split_clause,[],[f1091,f1088,f887,f593,f585,f554,f486,f143,f126,f122,f118,f884])).

fof(f884,plain,
    ( spl6_73
  <=> k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f118,plain,
    ( spl6_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f122,plain,
    ( spl6_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f126,plain,
    ( spl6_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f143,plain,
    ( spl6_9
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f486,plain,
    ( spl6_40
  <=> v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f554,plain,
    ( spl6_42
  <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f585,plain,
    ( spl6_46
  <=> v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f593,plain,
    ( spl6_48
  <=> m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f887,plain,
    ( spl6_74
  <=> u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f1088,plain,
    ( spl6_91
  <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f1091,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_40
    | ~ spl6_42
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_74
    | ~ spl6_91 ),
    inference(subsumption_resolution,[],[f968,f1089])).

fof(f1089,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_91 ),
    inference(avatar_component_clause,[],[f1088])).

fof(f968,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_40
    | ~ spl6_42
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_74 ),
    inference(forward_demodulation,[],[f967,f555])).

fof(f555,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f554])).

fof(f967,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_40
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f966,f119])).

fof(f119,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f966,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_40
    | ~ spl6_46
    | ~ spl6_48
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f965,f594])).

fof(f594,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f593])).

fof(f965,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | v2_struct_0(sK0)
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_40
    | ~ spl6_46
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f964,f586])).

fof(f586,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f585])).

fof(f964,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | v2_struct_0(sK0)
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_40
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f963,f487])).

fof(f487,plain,
    ( v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f486])).

fof(f963,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | v2_struct_0(sK0)
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f962,f144])).

fof(f144,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f143])).

fof(f962,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | v2_struct_0(sK0)
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f961,f127])).

fof(f127,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f961,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | v2_struct_0(sK0)
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_4
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f960,f123])).

fof(f123,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f960,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | v2_struct_0(sK0)
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_74 ),
    inference(superposition,[],[f77,f888])).

fof(f888,plain,
    ( u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f887])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | v2_struct_0(X0)
      | k9_tmap_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_tmap_1)).

fof(f1090,plain,
    ( spl6_69
    | spl6_91
    | ~ spl6_21
    | ~ spl6_35
    | ~ spl6_39
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f1078,f1067,f482,f465,f284,f1088,f856])).

fof(f856,plain,
    ( spl6_69
  <=> v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f284,plain,
    ( spl6_21
  <=> v1_funct_1(k9_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f465,plain,
    ( spl6_35
  <=> v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f482,plain,
    ( spl6_39
  <=> m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f1067,plain,
    ( spl6_88
  <=> ! [X1,X3,X2] :
        ( v1_xboole_0(X1)
        | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),X3,X1,k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        | ~ v1_funct_2(X2,X3,X1)
        | ~ v1_funct_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f1078,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl6_21
    | ~ spl6_35
    | ~ spl6_39
    | ~ spl6_88 ),
    inference(subsumption_resolution,[],[f1077,f285])).

fof(f285,plain,
    ( v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f284])).

fof(f1077,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ spl6_35
    | ~ spl6_39
    | ~ spl6_88 ),
    inference(subsumption_resolution,[],[f1072,f466])).

fof(f466,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f465])).

fof(f1072,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ spl6_39
    | ~ spl6_88 ),
    inference(resolution,[],[f1068,f483])).

fof(f483,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f482])).

fof(f1068,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),X3,X1,k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(X2,X3,X1)
        | ~ v1_funct_1(X2) )
    | ~ spl6_88 ),
    inference(avatar_component_clause,[],[f1067])).

fof(f1069,plain,
    ( spl6_69
    | spl6_88
    | ~ spl6_40
    | ~ spl6_46
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f652,f593,f585,f486,f1067,f856])).

fof(f652,plain,
    ( ! [X2,X3,X1] :
        ( v1_xboole_0(X1)
        | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X3,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),X3,X1,k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1))) )
    | ~ spl6_40
    | ~ spl6_46
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f651,f586])).

fof(f651,plain,
    ( ! [X2,X3,X1] :
        ( v1_xboole_0(X1)
        | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X3,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),X3,X1,k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1))) )
    | ~ spl6_40
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f628,f487])).

fof(f628,plain,
    ( ! [X2,X3,X1] :
        ( v1_xboole_0(X1)
        | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
        | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X3,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),X3,X1,k7_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1))) )
    | ~ spl6_48 ),
    inference(resolution,[],[f594,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

fof(f959,plain,
    ( spl6_1
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_12
    | spl6_14
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_29
    | ~ spl6_30
    | ~ spl6_73 ),
    inference(avatar_contradiction_clause,[],[f958])).

fof(f958,plain,
    ( $false
    | spl6_1
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_12
    | spl6_14
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_29
    | ~ spl6_30
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f957,f253])).

fof(f253,plain,
    ( ~ r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl6_14
  <=> r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f957,plain,
    ( r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3)
    | spl6_1
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_29
    | ~ spl6_30
    | ~ spl6_73 ),
    inference(forward_demodulation,[],[f956,f885])).

fof(f885,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_73 ),
    inference(avatar_component_clause,[],[f884])).

fof(f956,plain,
    ( r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),sK3)
    | spl6_1
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_29
    | ~ spl6_30 ),
    inference(resolution,[],[f828,f241])).

fof(f241,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl6_12
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f828,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),X0) )
    | spl6_1
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_29
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f827,f136])).

fof(f136,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_7
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f827,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,sK0)
        | r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | spl6_1
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_29
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f826,f111])).

fof(f111,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f826,plain,
    ( ! [X0] :
        ( v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_29
    | ~ spl6_30 ),
    inference(resolution,[],[f410,f324])).

fof(f324,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl6_30
  <=> r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f410,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) )
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f409,f406])).

fof(f406,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f405,f119])).

fof(f405,plain,
    ( v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f404,f297])).

fof(f297,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl6_24
  <=> l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f404,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f403,f293])).

fof(f293,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl6_23
  <=> v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f403,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f402,f289])).

fof(f289,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl6_22
  <=> v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f402,plain,
    ( ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f401,f144])).

fof(f401,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f400,f127])).

fof(f400,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_4
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f388,f123])).

fof(f388,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_29 ),
    inference(resolution,[],[f320,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X3
      | k6_tmap_1(X0,X3) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f320,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl6_29
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f409,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_tmap_1(X0,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1) )
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f408,f119])).

fof(f408,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_tmap_1(X0,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f407,f127])).

fof(f407,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_tmap_1(X0,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1) )
    | ~ spl6_4
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f389,f123])).

fof(f389,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_tmap_1(X0,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1) )
    | ~ spl6_29 ),
    inference(resolution,[],[f320,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tmap_1)).

fof(f889,plain,
    ( spl6_73
    | spl6_74
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_40
    | ~ spl6_46
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f642,f593,f585,f486,f143,f126,f122,f118,f887,f884])).

fof(f642,plain,
    ( u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_40
    | ~ spl6_46
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f641,f119])).

fof(f641,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_40
    | ~ spl6_46
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f640,f586])).

fof(f640,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0)
    | u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_40
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f639,f487])).

fof(f639,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0)
    | u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f638,f144])).

fof(f638,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0)
    | u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f637,f127])).

fof(f637,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0)
    | u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_4
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f626,f123])).

fof(f626,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0)
    | u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_48 ),
    inference(resolution,[],[f594,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | v2_struct_0(X0)
      | u1_struct_0(X1) = sK4(X0,X1,X2)
      | k9_tmap_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f865,plain,
    ( ~ spl6_27
    | spl6_36
    | ~ spl6_69 ),
    inference(avatar_contradiction_clause,[],[f864])).

fof(f864,plain,
    ( $false
    | ~ spl6_27
    | spl6_36
    | ~ spl6_69 ),
    inference(subsumption_resolution,[],[f863,f470])).

fof(f470,plain,
    ( ~ v2_struct_0(k8_tmap_1(sK0,sK1))
    | spl6_36 ),
    inference(avatar_component_clause,[],[f469])).

fof(f469,plain,
    ( spl6_36
  <=> v2_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f863,plain,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl6_27
    | ~ spl6_69 ),
    inference(subsumption_resolution,[],[f862,f311])).

fof(f311,plain,
    ( l1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl6_27
  <=> l1_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f862,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK0,sK1))
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl6_69 ),
    inference(resolution,[],[f857,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f857,plain,
    ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f856])).

fof(f595,plain,
    ( spl6_48
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f421,f319,f296,f292,f288,f143,f126,f122,f118,f593])).

fof(f421,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f420,f406])).

fof(f420,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f419,f119])).

fof(f419,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f418,f127])).

fof(f418,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))
    | ~ spl6_4
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f392,f123])).

fof(f392,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))
    | ~ spl6_29 ),
    inference(resolution,[],[f320,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f587,plain,
    ( spl6_46
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f417,f319,f296,f292,f288,f143,f126,f122,f118,f585])).

fof(f417,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f416,f406])).

fof(f416,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f415,f119])).

fof(f415,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f414,f127])).

fof(f414,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | ~ spl6_4
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f391,f123])).

fof(f391,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | ~ spl6_29 ),
    inference(resolution,[],[f320,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f556,plain,
    ( spl6_42
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f406,f319,f296,f292,f288,f143,f126,f122,f118,f554])).

fof(f488,plain,
    ( spl6_40
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f413,f319,f126,f122,f118,f486])).

fof(f413,plain,
    ( v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f412,f119])).

fof(f412,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f411,f127])).

fof(f411,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_4
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f390,f123])).

fof(f390,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_29 ),
    inference(resolution,[],[f320,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_1(k7_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f484,plain,
    ( spl6_39
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f214,f143,f126,f122,f118,f482])).

fof(f214,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f213,f119])).

fof(f213,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f212,f127])).

fof(f212,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ spl6_4
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f197,f123])).

fof(f197,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ spl6_9 ),
    inference(resolution,[],[f144,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_tmap_1)).

fof(f471,plain,
    ( ~ spl6_36
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f437,f319,f296,f292,f288,f143,f126,f122,f118,f469])).

fof(f437,plain,
    ( ~ v2_struct_0(k8_tmap_1(sK0,sK1))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f436,f406])).

fof(f436,plain,
    ( ~ v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f435,f119])).

fof(f435,plain,
    ( v2_struct_0(sK0)
    | ~ v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f434,f127])).

fof(f434,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_4
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f396,f123])).

fof(f396,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_29 ),
    inference(resolution,[],[f320,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
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
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(f467,plain,
    ( spl6_35
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f211,f143,f126,f122,f118,f465])).

fof(f211,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f210,f119])).

fof(f210,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f209,f127])).

fof(f209,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl6_4
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f196,f123])).

fof(f196,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl6_9 ),
    inference(resolution,[],[f144,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f325,plain,
    ( spl6_30
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f266,f260,f256,f248,f323])).

fof(f248,plain,
    ( spl6_13
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f256,plain,
    ( spl6_15
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f260,plain,
    ( spl6_16
  <=> r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f266,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f265,f249])).

fof(f249,plain,
    ( l1_struct_0(sK2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f248])).

fof(f265,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_struct_0(sK2)
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f263,f257])).

fof(f257,plain,
    ( l1_struct_0(sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f256])).

fof(f263,plain,
    ( ~ l1_struct_0(sK1)
    | r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_struct_0(sK2)
    | ~ spl6_16 ),
    inference(resolution,[],[f261,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f261,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f260])).

fof(f321,plain,
    ( spl6_29
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f233,f143,f126,f319])).

fof(f233,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f204,f127])).

fof(f204,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_9 ),
    inference(resolution,[],[f144,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f312,plain,
    ( spl6_27
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f300,f296,f310])).

fof(f300,plain,
    ( l1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl6_24 ),
    inference(resolution,[],[f297,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f298,plain,
    ( spl6_24
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f223,f143,f126,f122,f118,f296])).

fof(f223,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f222,f119])).

fof(f222,plain,
    ( v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f221,f127])).

fof(f221,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f200,f123])).

fof(f200,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_9 ),
    inference(resolution,[],[f144,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f294,plain,
    ( spl6_23
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f220,f143,f126,f122,f118,f292])).

fof(f220,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f219,f119])).

fof(f219,plain,
    ( v2_struct_0(sK0)
    | v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f218,f127])).

fof(f218,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f199,f123])).

fof(f199,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_9 ),
    inference(resolution,[],[f144,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f290,plain,
    ( spl6_22
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f217,f143,f126,f122,f118,f288])).

fof(f217,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f216,f119])).

fof(f216,plain,
    ( v2_struct_0(sK0)
    | v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f215,f127])).

fof(f215,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f198,f123])).

fof(f198,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_9 ),
    inference(resolution,[],[f144,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f286,plain,
    ( spl6_21
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f208,f143,f126,f122,f118,f284])).

fof(f208,plain,
    ( v1_funct_1(k9_tmap_1(sK0,sK1))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f207,f119])).

fof(f207,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f206,f127])).

fof(f206,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f195,f123])).

fof(f195,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ spl6_9 ),
    inference(resolution,[],[f144,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_1(k9_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f262,plain,
    ( spl6_16
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f244,f236,f187,f139,f260])).

fof(f139,plain,
    ( spl6_8
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f187,plain,
    ( spl6_10
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f236,plain,
    ( spl6_11
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f244,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f193,f243])).

fof(f243,plain,
    ( l1_struct_0(sK1)
    | ~ spl6_11 ),
    inference(resolution,[],[f237,f102])).

fof(f237,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f236])).

fof(f193,plain,
    ( ~ l1_struct_0(sK1)
    | r1_tsep_1(sK2,sK1)
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f191,f192])).

fof(f192,plain,
    ( l1_struct_0(sK2)
    | ~ spl6_10 ),
    inference(resolution,[],[f188,f102])).

fof(f188,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f187])).

fof(f191,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | r1_tsep_1(sK2,sK1)
    | ~ spl6_8 ),
    inference(resolution,[],[f140,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f140,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f258,plain,
    ( spl6_15
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f243,f236,f256])).

fof(f254,plain,(
    ~ spl6_14 ),
    inference(avatar_split_clause,[],[f60,f252])).

fof(f60,plain,(
    ~ r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
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
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
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
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X2))
                     => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
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
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_tmap_1)).

fof(f250,plain,
    ( spl6_13
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f192,f187,f248])).

fof(f242,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f59,f240])).

fof(f59,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f238,plain,
    ( spl6_11
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f234,f143,f126,f236])).

fof(f234,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f205,f127])).

fof(f205,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1)
    | ~ spl6_9 ),
    inference(resolution,[],[f144,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f189,plain,
    ( spl6_10
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f185,f135,f126,f187])).

fof(f185,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f156,f127])).

fof(f156,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f136,f89])).

fof(f145,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f65,f143])).

fof(f65,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f141,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f63,f139])).

fof(f63,plain,(
    r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f137,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f62,f135])).

fof(f62,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f128,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f68,f126])).

fof(f68,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f124,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f67,f122])).

fof(f67,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f120,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f66,f118])).

fof(f66,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f112,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f61,f110])).

fof(f61,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

%------------------------------------------------------------------------------
