%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t92_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:53 EDT 2019

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 294 expanded)
%              Number of leaves         :   41 ( 126 expanded)
%              Depth                    :    8
%              Number of atoms          :  504 ( 966 expanded)
%              Number of equality atoms :   93 ( 194 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2093,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f133,f147,f154,f161,f182,f206,f245,f336,f343,f410,f416,f463,f478,f486,f503,f517,f551,f564,f612,f620,f720,f787,f802,f1328,f2008,f2092])).

fof(f2092,plain,
    ( ~ spl5_4
    | spl5_105
    | ~ spl5_224 ),
    inference(avatar_contradiction_clause,[],[f2091])).

fof(f2091,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_105
    | ~ spl5_224 ),
    inference(subsumption_resolution,[],[f2087,f611])).

fof(f611,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
    | ~ spl5_105 ),
    inference(avatar_component_clause,[],[f610])).

fof(f610,plain,
    ( spl5_105
  <=> k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).

fof(f2087,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
    | ~ spl5_4
    | ~ spl5_224 ),
    inference(resolution,[],[f2007,f146])).

fof(f146,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl5_4
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f2007,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl5_224 ),
    inference(avatar_component_clause,[],[f2006])).

fof(f2006,plain,
    ( spl5_224
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_224])])).

fof(f2008,plain,
    ( spl5_224
    | ~ spl5_106
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f1333,f1326,f618,f2006])).

fof(f618,plain,
    ( spl5_106
  <=> ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f1326,plain,
    ( spl5_172
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_172])])).

fof(f1333,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl5_106
    | ~ spl5_172 ),
    inference(subsumption_resolution,[],[f1330,f619])).

fof(f619,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
    | ~ spl5_106 ),
    inference(avatar_component_clause,[],[f618])).

fof(f1330,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl5_172 ),
    inference(resolution,[],[f1327,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t92_funct_2.p',d10_xboole_0)).

fof(f1327,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
        | ~ r1_tarski(X0,sK0) )
    | ~ spl5_172 ),
    inference(avatar_component_clause,[],[f1326])).

fof(f1328,plain,
    ( spl5_172
    | ~ spl5_18
    | ~ spl5_114 ),
    inference(avatar_split_clause,[],[f1323,f697,f204,f1326])).

fof(f204,plain,
    ( spl5_18
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f697,plain,
    ( spl5_114
  <=> k1_relat_1(sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f1323,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) )
    | ~ spl5_18
    | ~ spl5_114 ),
    inference(forward_demodulation,[],[f248,f698])).

fof(f698,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ spl5_114 ),
    inference(avatar_component_clause,[],[f697])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) )
    | ~ spl5_18 ),
    inference(resolution,[],[f90,f205])).

fof(f205,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f204])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t92_funct_2.p',t146_funct_1)).

fof(f802,plain,
    ( spl5_114
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_46
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f791,f785,f341,f180,f152,f697])).

fof(f152,plain,
    ( spl5_6
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f180,plain,
    ( spl5_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f341,plain,
    ( spl5_46
  <=> k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f785,plain,
    ( spl5_124
  <=> ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_funct_2(sK2,X0,X0)
        | k1_relset_1(X0,X0,sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f791,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_46
    | ~ spl5_124 ),
    inference(backward_demodulation,[],[f790,f342])).

fof(f342,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f341])).

fof(f790,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_124 ),
    inference(subsumption_resolution,[],[f789,f181])).

fof(f181,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f180])).

fof(f789,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_relset_1(sK0,sK0,sK2) = sK0
    | ~ spl5_6
    | ~ spl5_124 ),
    inference(resolution,[],[f786,f153])).

fof(f153,plain,
    ( v1_funct_2(sK2,sK0,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f786,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,X0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | k1_relset_1(X0,X0,sK2) = X0 )
    | ~ spl5_124 ),
    inference(avatar_component_clause,[],[f785])).

fof(f787,plain,
    ( spl5_124
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f316,f131,f785])).

fof(f131,plain,
    ( spl5_0
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f316,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_funct_2(sK2,X0,X0)
        | k1_relset_1(X0,X0,sK2) = X0 )
    | ~ spl5_0 ),
    inference(resolution,[],[f98,f132])).

fof(f132,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f131])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t92_funct_2.p',t67_funct_2)).

fof(f720,plain,
    ( ~ spl5_0
    | ~ spl5_8
    | ~ spl5_14
    | spl5_101 ),
    inference(avatar_contradiction_clause,[],[f719])).

fof(f719,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_8
    | ~ spl5_14
    | ~ spl5_101 ),
    inference(unit_resulting_resolution,[],[f132,f160,f181,f578,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t92_funct_2.p',cc2_funct_2)).

fof(f578,plain,
    ( ~ v2_funct_1(sK2)
    | ~ spl5_101 ),
    inference(avatar_component_clause,[],[f577])).

fof(f577,plain,
    ( spl5_101
  <=> ~ v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).

fof(f160,plain,
    ( v3_funct_2(sK2,sK0,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl5_8
  <=> v3_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f620,plain,
    ( spl5_106
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f588,f580,f204,f131,f618])).

fof(f580,plain,
    ( spl5_100
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f588,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_100 ),
    inference(subsumption_resolution,[],[f587,f205])).

fof(f587,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl5_0
    | ~ spl5_100 ),
    inference(subsumption_resolution,[],[f586,f132])).

fof(f586,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl5_100 ),
    inference(resolution,[],[f581,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t92_funct_2.p',t152_funct_1)).

fof(f581,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_100 ),
    inference(avatar_component_clause,[],[f580])).

fof(f612,plain,
    ( ~ spl5_105
    | ~ spl5_82
    | spl5_97 ),
    inference(avatar_split_clause,[],[f573,f562,f476,f610])).

fof(f476,plain,
    ( spl5_82
  <=> ! [X3] : k8_relset_1(sK0,sK0,sK2,X3) = k10_relat_1(sK2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f562,plain,
    ( spl5_97
  <=> k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f573,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
    | ~ spl5_82
    | ~ spl5_97 ),
    inference(superposition,[],[f563,f477])).

fof(f477,plain,
    ( ! [X3] : k8_relset_1(sK0,sK0,sK2,X3) = k10_relat_1(sK2,X3)
    | ~ spl5_82 ),
    inference(avatar_component_clause,[],[f476])).

fof(f563,plain,
    ( k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) != sK1
    | ~ spl5_97 ),
    inference(avatar_component_clause,[],[f562])).

fof(f564,plain,
    ( ~ spl5_97
    | spl5_45
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f552,f461,f334,f562])).

fof(f334,plain,
    ( spl5_45
  <=> k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f461,plain,
    ( spl5_76
  <=> ! [X3] : k7_relset_1(sK0,sK0,sK2,X3) = k9_relat_1(sK2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f552,plain,
    ( k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) != sK1
    | ~ spl5_45
    | ~ spl5_76 ),
    inference(forward_demodulation,[],[f335,f462])).

fof(f462,plain,
    ( ! [X3] : k7_relset_1(sK0,sK0,sK2,X3) = k9_relat_1(sK2,X3)
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f461])).

fof(f335,plain,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f334])).

fof(f551,plain,
    ( spl5_92
    | ~ spl5_4
    | ~ spl5_90 ),
    inference(avatar_split_clause,[],[f509,f501,f145,f512])).

fof(f512,plain,
    ( spl5_92
  <=> k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f501,plain,
    ( spl5_90
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f509,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
    | ~ spl5_4
    | ~ spl5_90 ),
    inference(resolution,[],[f502,f146])).

fof(f502,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl5_90 ),
    inference(avatar_component_clause,[],[f501])).

fof(f517,plain,
    ( ~ spl5_93
    | ~ spl5_76
    | spl5_85 ),
    inference(avatar_split_clause,[],[f492,f484,f461,f515])).

fof(f515,plain,
    ( spl5_93
  <=> k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f484,plain,
    ( spl5_85
  <=> k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f492,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1
    | ~ spl5_76
    | ~ spl5_85 ),
    inference(superposition,[],[f485,f462])).

fof(f485,plain,
    ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
    | ~ spl5_85 ),
    inference(avatar_component_clause,[],[f484])).

fof(f503,plain,
    ( spl5_90
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f498,f402,f204,f131,f501])).

fof(f402,plain,
    ( spl5_60
  <=> k2_relat_1(sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f498,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f298,f403])).

fof(f403,plain,
    ( k2_relat_1(sK2) = sK0
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f402])).

fof(f298,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl5_0
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f297,f205])).

fof(f297,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
        | ~ v1_relat_1(sK2) )
    | ~ spl5_0 ),
    inference(resolution,[],[f95,f132])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t92_funct_2.p',t147_funct_1)).

fof(f486,plain,
    ( ~ spl5_85
    | ~ spl5_14
    | spl5_43 ),
    inference(avatar_split_clause,[],[f473,f328,f180,f484])).

fof(f328,plain,
    ( spl5_43
  <=> k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f473,plain,
    ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
    | ~ spl5_14
    | ~ spl5_43 ),
    inference(backward_demodulation,[],[f313,f329])).

fof(f329,plain,
    ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f328])).

fof(f313,plain,
    ( ! [X3] : k8_relset_1(sK0,sK0,sK2,X3) = k10_relat_1(sK2,X3)
    | ~ spl5_14 ),
    inference(resolution,[],[f121,f181])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t92_funct_2.p',redefinition_k8_relset_1)).

fof(f478,plain,
    ( spl5_82
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f313,f180,f476])).

fof(f463,plain,
    ( spl5_76
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f306,f180,f461])).

fof(f306,plain,
    ( ! [X3] : k7_relset_1(sK0,sK0,sK2,X3) = k9_relat_1(sK2,X3)
    | ~ spl5_14 ),
    inference(resolution,[],[f120,f181])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t92_funct_2.p',redefinition_k7_relset_1)).

fof(f416,plain,
    ( ~ spl5_0
    | ~ spl5_8
    | ~ spl5_14
    | spl5_63 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_8
    | ~ spl5_14
    | ~ spl5_63 ),
    inference(unit_resulting_resolution,[],[f132,f160,f181,f409,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f409,plain,
    ( ~ v2_funct_2(sK2,sK0)
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f408])).

fof(f408,plain,
    ( spl5_63
  <=> ~ v2_funct_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f410,plain,
    ( spl5_60
    | ~ spl5_63
    | ~ spl5_18
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f247,f243,f204,f408,f402])).

fof(f243,plain,
    ( spl5_26
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f247,plain,
    ( ~ v2_funct_2(sK2,sK0)
    | k2_relat_1(sK2) = sK0
    | ~ spl5_18
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f246,f205])).

fof(f246,plain,
    ( ~ v2_funct_2(sK2,sK0)
    | k2_relat_1(sK2) = sK0
    | ~ v1_relat_1(sK2)
    | ~ spl5_26 ),
    inference(resolution,[],[f244,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t92_funct_2.p',d3_funct_2)).

fof(f244,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f243])).

fof(f343,plain,
    ( spl5_46
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f260,f180,f341])).

fof(f260,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl5_14 ),
    inference(resolution,[],[f108,f181])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t92_funct_2.p',redefinition_k1_relset_1)).

fof(f336,plain,
    ( ~ spl5_43
    | ~ spl5_45 ),
    inference(avatar_split_clause,[],[f86,f334,f328])).

fof(f86,plain,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,
    ( ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f73])).

fof(f73,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
          | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
        & r1_tarski(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
   => ( ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
        | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 )
      & r1_tarski(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t92_funct_2.p',t92_funct_2)).

fof(f245,plain,
    ( spl5_26
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f229,f180,f243])).

fof(f229,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl5_14 ),
    inference(resolution,[],[f112,f181])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t92_funct_2.p',cc2_relset_1)).

fof(f206,plain,
    ( spl5_18
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f198,f180,f204])).

fof(f198,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_14 ),
    inference(resolution,[],[f106,f181])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t92_funct_2.p',cc1_relset_1)).

fof(f182,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f84,f180])).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f74])).

fof(f161,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f83,f159])).

fof(f83,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f74])).

fof(f154,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f82,f152])).

fof(f82,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f74])).

fof(f147,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f85,f145])).

fof(f85,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f74])).

fof(f133,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f81,f131])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).
%------------------------------------------------------------------------------
