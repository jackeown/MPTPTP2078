%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 395 expanded)
%              Number of leaves         :   56 ( 184 expanded)
%              Depth                    :   11
%              Number of atoms          :  664 (1361 expanded)
%              Number of equality atoms :  139 ( 313 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (13577)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f635,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f85,f89,f93,f97,f101,f105,f111,f116,f124,f134,f138,f145,f148,f153,f168,f184,f199,f211,f221,f251,f275,f279,f284,f300,f355,f382,f383,f386,f408,f504,f558,f565,f607,f613,f614,f616,f633])).

fof(f633,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | sK1 != k2_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f616,plain,
    ( ~ spl3_66
    | ~ spl3_11
    | ~ spl3_21
    | ~ spl3_25
    | spl3_39
    | ~ spl3_41
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f615,f563,f379,f350,f209,f181,f122,f609])).

fof(f609,plain,
    ( spl3_66
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f122,plain,
    ( spl3_11
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f181,plain,
    ( spl3_21
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f209,plain,
    ( spl3_25
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f350,plain,
    ( spl3_39
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f379,plain,
    ( spl3_41
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f563,plain,
    ( spl3_61
  <=> k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f615,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_11
    | ~ spl3_21
    | ~ spl3_25
    | spl3_39
    | ~ spl3_41
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f541,f564])).

fof(f564,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f563])).

fof(f541,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_11
    | ~ spl3_21
    | ~ spl3_25
    | spl3_39
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f540,f380])).

fof(f380,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f379])).

fof(f540,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_11
    | ~ spl3_21
    | ~ spl3_25
    | spl3_39 ),
    inference(trivial_inequality_removal,[],[f539])).

fof(f539,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_11
    | ~ spl3_21
    | ~ spl3_25
    | spl3_39 ),
    inference(forward_demodulation,[],[f538,f249])).

fof(f249,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f209])).

fof(f538,plain,
    ( k1_xboole_0 != sK1
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_11
    | ~ spl3_21
    | spl3_39 ),
    inference(forward_demodulation,[],[f537,f182])).

fof(f182,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f181])).

fof(f537,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_11
    | spl3_39 ),
    inference(forward_demodulation,[],[f529,f123])).

fof(f123,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f122])).

fof(f529,plain,
    ( k1_xboole_0 != k1_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_39 ),
    inference(superposition,[],[f351,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f351,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | spl3_39 ),
    inference(avatar_component_clause,[],[f350])).

fof(f614,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | sK1 != k2_relat_1(sK2)
    | k1_xboole_0 != sK2
    | k1_xboole_0 != k2_funct_1(k1_xboole_0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f613,plain,(
    spl3_65 ),
    inference(avatar_contradiction_clause,[],[f612])).

fof(f612,plain,
    ( $false
    | spl3_65 ),
    inference(resolution,[],[f606,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f606,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0))
    | spl3_65 ),
    inference(avatar_component_clause,[],[f605])).

fof(f605,plain,
    ( spl3_65
  <=> r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f607,plain,
    ( ~ spl3_65
    | spl3_56
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f599,f563,f502,f605])).

fof(f502,plain,
    ( spl3_56
  <=> r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f599,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0))
    | spl3_56
    | ~ spl3_61 ),
    inference(superposition,[],[f503,f564])).

fof(f503,plain,
    ( ~ r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0))
    | spl3_56 ),
    inference(avatar_component_clause,[],[f502])).

fof(f565,plain,
    ( spl3_61
    | ~ spl3_9
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f560,f556,f103,f563])).

fof(f103,plain,
    ( spl3_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f556,plain,
    ( spl3_60
  <=> v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f560,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_9
    | ~ spl3_60 ),
    inference(resolution,[],[f557,f112])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_9 ),
    inference(resolution,[],[f57,f104])).

fof(f104,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f557,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f556])).

fof(f558,plain,
    ( spl3_60
    | ~ spl3_9
    | ~ spl3_34
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f554,f379,f282,f103,f556])).

fof(f282,plain,
    ( spl3_34
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f554,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl3_9
    | ~ spl3_34
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f543,f380])).

fof(f543,plain,
    ( v1_xboole_0(k2_funct_1(sK2))
    | ~ spl3_9
    | ~ spl3_34 ),
    inference(resolution,[],[f283,f117])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_xboole_0(X0) )
    | ~ spl3_9 ),
    inference(resolution,[],[f55,f104])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f283,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f282])).

fof(f504,plain,
    ( ~ spl3_56
    | spl3_47 ),
    inference(avatar_split_clause,[],[f500,f406,f502])).

fof(f406,plain,
    ( spl3_47
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f500,plain,
    ( ~ r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0))
    | spl3_47 ),
    inference(resolution,[],[f407,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f407,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_47 ),
    inference(avatar_component_clause,[],[f406])).

fof(f408,plain,
    ( ~ spl3_47
    | spl3_3
    | ~ spl3_25
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f404,f379,f209,f79,f406])).

fof(f79,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f404,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_25
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f403,f380])).

fof(f403,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f80,f249])).

fof(f80,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f386,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k1_xboole_0 != k2_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 != sK0
    | sK0 = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f383,plain,
    ( sK1 != k2_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | sK0 != k1_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f382,plain,
    ( spl3_41
    | spl3_38
    | ~ spl3_33
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f376,f273,f277,f347,f379])).

fof(f347,plain,
    ( spl3_38
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f277,plain,
    ( spl3_33
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f273,plain,
    ( spl3_32
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f376,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl3_32 ),
    inference(resolution,[],[f274,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f274,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f273])).

fof(f355,plain,
    ( spl3_38
    | ~ spl3_39
    | ~ spl3_40
    | spl3_2
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f345,f209,f76,f353,f350,f347])).

fof(f353,plain,
    ( spl3_40
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f76,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f345,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | k1_xboole_0 = sK0
    | spl3_2
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f344,f249])).

fof(f344,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_2
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f342,f249])).

fof(f342,plain,
    ( sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_2 ),
    inference(resolution,[],[f63,f77])).

fof(f77,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f300,plain,
    ( sK1 != k2_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | sK0 != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f284,plain,
    ( spl3_34
    | ~ spl3_20
    | ~ spl3_23
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f280,f209,f197,f173,f282])).

fof(f173,plain,
    ( spl3_20
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f197,plain,
    ( spl3_23
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f280,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_20
    | ~ spl3_23
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f263,f220])).

fof(f220,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f173])).

fof(f263,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))
    | ~ spl3_23
    | ~ spl3_25 ),
    inference(superposition,[],[f198,f249])).

fof(f198,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f197])).

fof(f279,plain,
    ( spl3_33
    | ~ spl3_7
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f262,f209,f95,f277])).

fof(f95,plain,
    ( spl3_7
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f262,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_25 ),
    inference(superposition,[],[f96,f249])).

fof(f96,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f275,plain,
    ( spl3_32
    | ~ spl3_6
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f261,f209,f91,f273])).

fof(f91,plain,
    ( spl3_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f261,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl3_6
    | ~ spl3_25 ),
    inference(superposition,[],[f92,f249])).

fof(f92,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f251,plain,
    ( spl3_28
    | spl3_25
    | ~ spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f241,f91,f95,f209,f247])).

fof(f247,plain,
    ( spl3_28
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f241,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f238,f92])).

fof(f238,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | k1_relat_1(X5) = X3 ) ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f61,f59])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f221,plain,
    ( ~ spl3_10
    | spl3_20
    | ~ spl3_25
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f195,f181,f209,f173,f108])).

fof(f108,plain,
    ( spl3_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f195,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_21 ),
    inference(superposition,[],[f47,f182])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

% (13576)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f36,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f211,plain,
    ( ~ spl3_25
    | spl3_16
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f192,f181,f143,f209])).

fof(f143,plain,
    ( spl3_16
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f192,plain,
    ( k1_xboole_0 != sK1
    | spl3_16
    | ~ spl3_21 ),
    inference(superposition,[],[f144,f182])).

fof(f144,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f143])).

fof(f199,plain,
    ( spl3_23
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f188,f181,f160,f197])).

fof(f160,plain,
    ( spl3_18
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f188,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f161,f182])).

fof(f161,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f160])).

fof(f184,plain,
    ( ~ spl3_6
    | spl3_21
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f178,f83,f181,f91])).

fof(f83,plain,
    ( spl3_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f178,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_4 ),
    inference(superposition,[],[f84,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f84,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f168,plain,
    ( ~ spl3_12
    | ~ spl3_1
    | spl3_18
    | ~ spl3_11
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f167,f151,f122,f160,f73,f129])).

fof(f129,plain,
    ( spl3_12
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f73,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f151,plain,
    ( spl3_17
  <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f167,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_11
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f156,f123])).

fof(f156,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_17 ),
    inference(superposition,[],[f50,f152])).

fof(f152,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f151])).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f153,plain,
    ( ~ spl3_10
    | ~ spl3_8
    | spl3_17
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f149,f87,f151,f99,f108])).

fof(f99,plain,
    ( spl3_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f87,plain,
    ( spl3_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f149,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f54,f88])).

fof(f88,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f148,plain,
    ( ~ spl3_10
    | ~ spl3_8
    | spl3_12 ),
    inference(avatar_split_clause,[],[f146,f129,f99,f108])).

fof(f146,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_12 ),
    inference(resolution,[],[f130,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f130,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f145,plain,
    ( ~ spl3_12
    | spl3_15
    | ~ spl3_16
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f127,f122,f143,f140,f129])).

fof(f140,plain,
    ( spl3_15
  <=> k1_xboole_0 = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f127,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_11 ),
    inference(superposition,[],[f46,f123])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f138,plain,
    ( ~ spl3_12
    | ~ spl3_1
    | spl3_14
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f126,f122,f136,f73,f129])).

fof(f136,plain,
    ( spl3_14
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f126,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_11 ),
    inference(superposition,[],[f49,f123])).

fof(f49,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f134,plain,
    ( ~ spl3_12
    | ~ spl3_1
    | spl3_13
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f125,f122,f132,f73,f129])).

fof(f132,plain,
    ( spl3_13
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f125,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_11 ),
    inference(superposition,[],[f50,f123])).

fof(f124,plain,
    ( ~ spl3_10
    | ~ spl3_8
    | spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f120,f87,f122,f99,f108])).

fof(f120,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f53,f88])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f116,plain,
    ( ~ spl3_6
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl3_6
    | spl3_10 ),
    inference(subsumption_resolution,[],[f92,f114])).

fof(f114,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_10 ),
    inference(resolution,[],[f58,f109])).

fof(f109,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f111,plain,
    ( ~ spl3_10
    | ~ spl3_8
    | spl3_1 ),
    inference(avatar_split_clause,[],[f106,f73,f99,f108])).

fof(f106,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(resolution,[],[f52,f74])).

fof(f74,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f52,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f105,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f44,f103])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f101,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f38,f99])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f97,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f39,f95])).

fof(f39,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f40,f91])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f41,f87])).

fof(f41,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f42,f83])).

fof(f42,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f43,f79,f76,f73])).

fof(f43,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:33:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (13586)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.47  % (13588)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (13580)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (13578)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (13581)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (13588)Refutation not found, incomplete strategy% (13588)------------------------------
% 0.22/0.49  % (13588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (13588)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (13588)Memory used [KB]: 1663
% 0.22/0.49  % (13588)Time elapsed: 0.078 s
% 0.22/0.49  % (13588)------------------------------
% 0.22/0.49  % (13588)------------------------------
% 0.22/0.49  % (13590)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (13575)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (13582)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (13591)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (13581)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  % (13577)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  fof(f635,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f81,f85,f89,f93,f97,f101,f105,f111,f116,f124,f134,f138,f145,f148,f153,f168,f184,f199,f211,f221,f251,f275,f279,f284,f300,f355,f382,f383,f386,f408,f504,f558,f565,f607,f613,f614,f616,f633])).
% 0.22/0.51  fof(f633,plain,(
% 0.22/0.51    k1_xboole_0 != k2_relat_1(sK2) | sK1 != k2_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f616,plain,(
% 0.22/0.51    ~spl3_66 | ~spl3_11 | ~spl3_21 | ~spl3_25 | spl3_39 | ~spl3_41 | ~spl3_61),
% 0.22/0.51    inference(avatar_split_clause,[],[f615,f563,f379,f350,f209,f181,f122,f609])).
% 0.22/0.51  fof(f609,plain,(
% 0.22/0.51    spl3_66 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    spl3_11 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    spl3_21 <=> sK1 = k2_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.51  fof(f209,plain,(
% 0.22/0.51    spl3_25 <=> k1_xboole_0 = sK1),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.51  fof(f350,plain,(
% 0.22/0.51    spl3_39 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.22/0.51  fof(f379,plain,(
% 0.22/0.51    spl3_41 <=> k1_xboole_0 = sK2),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.22/0.51  fof(f563,plain,(
% 0.22/0.51    spl3_61 <=> k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.22/0.51  fof(f615,plain,(
% 0.22/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_11 | ~spl3_21 | ~spl3_25 | spl3_39 | ~spl3_41 | ~spl3_61)),
% 0.22/0.51    inference(forward_demodulation,[],[f541,f564])).
% 0.22/0.51  fof(f564,plain,(
% 0.22/0.51    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl3_61),
% 0.22/0.51    inference(avatar_component_clause,[],[f563])).
% 0.22/0.51  fof(f541,plain,(
% 0.22/0.51    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_11 | ~spl3_21 | ~spl3_25 | spl3_39 | ~spl3_41)),
% 0.22/0.51    inference(forward_demodulation,[],[f540,f380])).
% 0.22/0.51  fof(f380,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | ~spl3_41),
% 0.22/0.51    inference(avatar_component_clause,[],[f379])).
% 0.22/0.51  fof(f540,plain,(
% 0.22/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_11 | ~spl3_21 | ~spl3_25 | spl3_39)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f539])).
% 0.22/0.51  fof(f539,plain,(
% 0.22/0.51    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_11 | ~spl3_21 | ~spl3_25 | spl3_39)),
% 0.22/0.51    inference(forward_demodulation,[],[f538,f249])).
% 0.22/0.51  fof(f249,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | ~spl3_25),
% 0.22/0.51    inference(avatar_component_clause,[],[f209])).
% 0.22/0.51  fof(f538,plain,(
% 0.22/0.51    k1_xboole_0 != sK1 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_11 | ~spl3_21 | spl3_39)),
% 0.22/0.51    inference(forward_demodulation,[],[f537,f182])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    sK1 = k2_relat_1(sK2) | ~spl3_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f181])).
% 0.22/0.51  fof(f537,plain,(
% 0.22/0.51    k1_xboole_0 != k2_relat_1(sK2) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_11 | spl3_39)),
% 0.22/0.51    inference(forward_demodulation,[],[f529,f123])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f122])).
% 0.22/0.51  fof(f529,plain,(
% 0.22/0.51    k1_xboole_0 != k1_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_39),
% 0.22/0.51    inference(superposition,[],[f351,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.51  fof(f351,plain,(
% 0.22/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | spl3_39),
% 0.22/0.51    inference(avatar_component_clause,[],[f350])).
% 0.22/0.51  fof(f614,plain,(
% 0.22/0.51    k1_xboole_0 != k2_relat_1(sK2) | sK1 != k2_relat_1(sK2) | k1_xboole_0 != sK2 | k1_xboole_0 != k2_funct_1(k1_xboole_0) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f613,plain,(
% 0.22/0.51    spl3_65),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f612])).
% 0.22/0.51  fof(f612,plain,(
% 0.22/0.51    $false | spl3_65),
% 0.22/0.51    inference(resolution,[],[f606,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.51  fof(f606,plain,(
% 0.22/0.51    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0)) | spl3_65),
% 0.22/0.51    inference(avatar_component_clause,[],[f605])).
% 0.22/0.51  fof(f605,plain,(
% 0.22/0.51    spl3_65 <=> r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 0.22/0.51  fof(f607,plain,(
% 0.22/0.51    ~spl3_65 | spl3_56 | ~spl3_61),
% 0.22/0.51    inference(avatar_split_clause,[],[f599,f563,f502,f605])).
% 0.22/0.51  fof(f502,plain,(
% 0.22/0.51    spl3_56 <=> r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.22/0.51  fof(f599,plain,(
% 0.22/0.51    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0)) | (spl3_56 | ~spl3_61)),
% 0.22/0.51    inference(superposition,[],[f503,f564])).
% 0.22/0.51  fof(f503,plain,(
% 0.22/0.51    ~r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0)) | spl3_56),
% 0.22/0.51    inference(avatar_component_clause,[],[f502])).
% 0.22/0.51  fof(f565,plain,(
% 0.22/0.51    spl3_61 | ~spl3_9 | ~spl3_60),
% 0.22/0.51    inference(avatar_split_clause,[],[f560,f556,f103,f563])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    spl3_9 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.51  fof(f556,plain,(
% 0.22/0.51    spl3_60 <=> v1_xboole_0(k2_funct_1(k1_xboole_0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 0.22/0.51  fof(f560,plain,(
% 0.22/0.51    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_9 | ~spl3_60)),
% 0.22/0.51    inference(resolution,[],[f557,f112])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_9),
% 0.22/0.51    inference(resolution,[],[f57,f104])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0) | ~spl3_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f103])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.51  fof(f557,plain,(
% 0.22/0.51    v1_xboole_0(k2_funct_1(k1_xboole_0)) | ~spl3_60),
% 0.22/0.51    inference(avatar_component_clause,[],[f556])).
% 0.22/0.51  fof(f558,plain,(
% 0.22/0.51    spl3_60 | ~spl3_9 | ~spl3_34 | ~spl3_41),
% 0.22/0.51    inference(avatar_split_clause,[],[f554,f379,f282,f103,f556])).
% 0.22/0.51  fof(f282,plain,(
% 0.22/0.51    spl3_34 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.51  fof(f554,plain,(
% 0.22/0.51    v1_xboole_0(k2_funct_1(k1_xboole_0)) | (~spl3_9 | ~spl3_34 | ~spl3_41)),
% 0.22/0.51    inference(forward_demodulation,[],[f543,f380])).
% 0.22/0.51  fof(f543,plain,(
% 0.22/0.51    v1_xboole_0(k2_funct_1(sK2)) | (~spl3_9 | ~spl3_34)),
% 0.22/0.51    inference(resolution,[],[f283,f117])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(X0)) ) | ~spl3_9),
% 0.22/0.51    inference(resolution,[],[f55,f104])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.22/0.51  fof(f283,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_34),
% 0.22/0.51    inference(avatar_component_clause,[],[f282])).
% 0.22/0.51  fof(f504,plain,(
% 0.22/0.51    ~spl3_56 | spl3_47),
% 0.22/0.51    inference(avatar_split_clause,[],[f500,f406,f502])).
% 0.22/0.51  fof(f406,plain,(
% 0.22/0.51    spl3_47 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.22/0.51  fof(f500,plain,(
% 0.22/0.51    ~r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0)) | spl3_47),
% 0.22/0.51    inference(resolution,[],[f407,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.51    inference(unused_predicate_definition_removal,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.51  fof(f407,plain,(
% 0.22/0.51    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_47),
% 0.22/0.51    inference(avatar_component_clause,[],[f406])).
% 0.22/0.51  fof(f408,plain,(
% 0.22/0.51    ~spl3_47 | spl3_3 | ~spl3_25 | ~spl3_41),
% 0.22/0.51    inference(avatar_split_clause,[],[f404,f379,f209,f79,f406])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f404,plain,(
% 0.22/0.51    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_25 | ~spl3_41)),
% 0.22/0.51    inference(forward_demodulation,[],[f403,f380])).
% 0.22/0.51  fof(f403,plain,(
% 0.22/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_25)),
% 0.22/0.51    inference(forward_demodulation,[],[f80,f249])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f79])).
% 0.22/0.51  fof(f386,plain,(
% 0.22/0.51    k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | k1_xboole_0 != k2_relat_1(k2_funct_1(sK2)) | k1_xboole_0 != sK0 | sK0 = k1_relat_1(sK2)),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f383,plain,(
% 0.22/0.51    sK1 != k2_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | sK0 != k1_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f382,plain,(
% 0.22/0.51    spl3_41 | spl3_38 | ~spl3_33 | ~spl3_32),
% 0.22/0.51    inference(avatar_split_clause,[],[f376,f273,f277,f347,f379])).
% 0.22/0.51  fof(f347,plain,(
% 0.22/0.51    spl3_38 <=> k1_xboole_0 = sK0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.22/0.51  fof(f277,plain,(
% 0.22/0.51    spl3_33 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.51  fof(f273,plain,(
% 0.22/0.51    spl3_32 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.51  fof(f376,plain,(
% 0.22/0.51    ~v1_funct_2(sK2,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl3_32),
% 0.22/0.51    inference(resolution,[],[f274,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.22/0.51    inference(equality_resolution,[],[f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(nnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(flattening,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.51  fof(f274,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl3_32),
% 0.22/0.51    inference(avatar_component_clause,[],[f273])).
% 0.22/0.51  fof(f355,plain,(
% 0.22/0.51    spl3_38 | ~spl3_39 | ~spl3_40 | spl3_2 | ~spl3_25),
% 0.22/0.51    inference(avatar_split_clause,[],[f345,f209,f76,f353,f350,f347])).
% 0.22/0.51  fof(f353,plain,(
% 0.22/0.51    spl3_40 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f345,plain,(
% 0.22/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | k1_xboole_0 = sK0 | (spl3_2 | ~spl3_25)),
% 0.22/0.51    inference(forward_demodulation,[],[f344,f249])).
% 0.22/0.51  fof(f344,plain,(
% 0.22/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | k1_xboole_0 = sK0 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl3_2 | ~spl3_25)),
% 0.22/0.51    inference(forward_demodulation,[],[f342,f249])).
% 0.22/0.51  fof(f342,plain,(
% 0.22/0.51    sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | k1_xboole_0 = sK0 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_2),
% 0.22/0.51    inference(resolution,[],[f63,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f76])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f37])).
% 0.22/0.51  fof(f300,plain,(
% 0.22/0.51    sK1 != k2_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | sK0 != k1_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f284,plain,(
% 0.22/0.51    spl3_34 | ~spl3_20 | ~spl3_23 | ~spl3_25),
% 0.22/0.51    inference(avatar_split_clause,[],[f280,f209,f197,f173,f282])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    spl3_20 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    spl3_23 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.51  fof(f280,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_20 | ~spl3_23 | ~spl3_25)),
% 0.22/0.51    inference(forward_demodulation,[],[f263,f220])).
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    k1_xboole_0 = k1_relat_1(sK2) | ~spl3_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f173])).
% 0.22/0.51  fof(f263,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) | (~spl3_23 | ~spl3_25)),
% 0.22/0.51    inference(superposition,[],[f198,f249])).
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~spl3_23),
% 0.22/0.51    inference(avatar_component_clause,[],[f197])).
% 0.22/0.51  fof(f279,plain,(
% 0.22/0.51    spl3_33 | ~spl3_7 | ~spl3_25),
% 0.22/0.51    inference(avatar_split_clause,[],[f262,f209,f95,f277])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    spl3_7 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.51  fof(f262,plain,(
% 0.22/0.51    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl3_7 | ~spl3_25)),
% 0.22/0.51    inference(superposition,[],[f96,f249])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    v1_funct_2(sK2,sK0,sK1) | ~spl3_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f95])).
% 0.22/0.51  fof(f275,plain,(
% 0.22/0.51    spl3_32 | ~spl3_6 | ~spl3_25),
% 0.22/0.51    inference(avatar_split_clause,[],[f261,f209,f91,f273])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    spl3_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.51  fof(f261,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl3_6 | ~spl3_25)),
% 0.22/0.51    inference(superposition,[],[f92,f249])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f91])).
% 0.22/0.51  fof(f251,plain,(
% 0.22/0.51    spl3_28 | spl3_25 | ~spl3_7 | ~spl3_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f241,f91,f95,f209,f247])).
% 0.22/0.51  fof(f247,plain,(
% 0.22/0.51    spl3_28 <=> sK0 = k1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.51  fof(f241,plain,(
% 0.22/0.51    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relat_1(sK2) | ~spl3_6),
% 0.22/0.51    inference(resolution,[],[f238,f92])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | k1_relat_1(X5) = X3) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f235])).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.22/0.51    inference(superposition,[],[f61,f59])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f37])).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    ~spl3_10 | spl3_20 | ~spl3_25 | ~spl3_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f195,f181,f209,f173,f108])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    spl3_10 <=> v1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.51  fof(f195,plain,(
% 0.22/0.51    k1_xboole_0 != sK1 | k1_xboole_0 = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_21),
% 0.22/0.51    inference(superposition,[],[f47,f182])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  % (13576)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    ~spl3_25 | spl3_16 | ~spl3_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f192,f181,f143,f209])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    spl3_16 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    k1_xboole_0 != sK1 | (spl3_16 | ~spl3_21)),
% 0.22/0.51    inference(superposition,[],[f144,f182])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    k1_xboole_0 != k2_relat_1(sK2) | spl3_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f143])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    spl3_23 | ~spl3_18 | ~spl3_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f188,f181,f160,f197])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    spl3_18 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl3_18 | ~spl3_21)),
% 0.22/0.51    inference(superposition,[],[f161,f182])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f160])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    ~spl3_6 | spl3_21 | ~spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f178,f83,f181,f91])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    spl3_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.51  fof(f178,plain,(
% 0.22/0.51    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_4),
% 0.22/0.51    inference(superposition,[],[f84,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl3_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f83])).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    ~spl3_12 | ~spl3_1 | spl3_18 | ~spl3_11 | ~spl3_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f167,f151,f122,f160,f73,f129])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    spl3_12 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    spl3_17 <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_11 | ~spl3_17)),
% 0.22/0.51    inference(forward_demodulation,[],[f156,f123])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_17),
% 0.22/0.51    inference(superposition,[],[f50,f152])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~spl3_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f151])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    ~spl3_10 | ~spl3_8 | spl3_17 | ~spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f149,f87,f151,f99,f108])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    spl3_8 <=> v1_funct_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    spl3_5 <=> v2_funct_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_5),
% 0.22/0.51    inference(resolution,[],[f54,f88])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    v2_funct_1(sK2) | ~spl3_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f87])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ~spl3_10 | ~spl3_8 | spl3_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f146,f129,f99,f108])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_12),
% 0.22/0.51    inference(resolution,[],[f130,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    ~v1_relat_1(k2_funct_1(sK2)) | spl3_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f129])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    ~spl3_12 | spl3_15 | ~spl3_16 | ~spl3_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f127,f122,f143,f140,f129])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    spl3_15 <=> k1_xboole_0 = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_11),
% 0.22/0.51    inference(superposition,[],[f46,f123])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    ~spl3_12 | ~spl3_1 | spl3_14 | ~spl3_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f126,f122,f136,f73,f129])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    spl3_14 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_11),
% 0.22/0.51    inference(superposition,[],[f49,f123])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ~spl3_12 | ~spl3_1 | spl3_13 | ~spl3_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f125,f122,f132,f73,f129])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    spl3_13 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_11),
% 0.22/0.51    inference(superposition,[],[f50,f123])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    ~spl3_10 | ~spl3_8 | spl3_11 | ~spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f120,f87,f122,f99,f108])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_5),
% 0.22/0.51    inference(resolution,[],[f53,f88])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    ~spl3_6 | spl3_10),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f115])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    $false | (~spl3_6 | spl3_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f92,f114])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_10),
% 0.22/0.51    inference(resolution,[],[f58,f109])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ~v1_relat_1(sK2) | spl3_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f108])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    ~spl3_10 | ~spl3_8 | spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f106,f73,f99,f108])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_1),
% 0.22/0.51    inference(resolution,[],[f52,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f73])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    spl3_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f44,f103])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    spl3_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f38,f99])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    v1_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.51    inference(negated_conjecture,[],[f14])).
% 0.22/0.51  fof(f14,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    spl3_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f39,f95])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    spl3_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f40,f91])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f41,f87])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    v2_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f42,f83])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f43,f79,f76,f73])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (13581)------------------------------
% 0.22/0.51  % (13581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13581)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (13581)Memory used [KB]: 11001
% 0.22/0.51  % (13581)Time elapsed: 0.088 s
% 0.22/0.51  % (13581)------------------------------
% 0.22/0.51  % (13581)------------------------------
% 0.22/0.51  % (13579)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (13574)Success in time 0.147 s
%------------------------------------------------------------------------------
