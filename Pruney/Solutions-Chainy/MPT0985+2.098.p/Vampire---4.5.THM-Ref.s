%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 340 expanded)
%              Number of leaves         :   48 ( 156 expanded)
%              Depth                    :    9
%              Number of atoms          :  565 (1157 expanded)
%              Number of equality atoms :  100 ( 215 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f534,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f81,f85,f89,f93,f97,f101,f107,f111,f121,f126,f136,f141,f144,f156,f167,f207,f208,f209,f224,f235,f243,f270,f355,f396,f454,f469,f498,f501,f513,f520,f526,f533])).

fof(f533,plain,
    ( ~ spl3_58
    | ~ spl3_56
    | spl3_60 ),
    inference(avatar_split_clause,[],[f532,f524,f474,f496])).

fof(f496,plain,
    ( spl3_58
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f474,plain,
    ( spl3_56
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f524,plain,
    ( spl3_60
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f532,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_56
    | spl3_60 ),
    inference(trivial_inequality_removal,[],[f531])).

fof(f531,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_56
    | spl3_60 ),
    inference(forward_demodulation,[],[f529,f475])).

fof(f475,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f474])).

fof(f529,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_60 ),
    inference(superposition,[],[f525,f56])).

fof(f56,plain,(
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

fof(f525,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | spl3_60 ),
    inference(avatar_component_clause,[],[f524])).

fof(f526,plain,
    ( ~ spl3_58
    | ~ spl3_60
    | spl3_59 ),
    inference(avatar_split_clause,[],[f521,f518,f524,f496])).

fof(f518,plain,
    ( spl3_59
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f521,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_59 ),
    inference(resolution,[],[f519,f66])).

fof(f66,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f32])).

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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f519,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl3_59 ),
    inference(avatar_component_clause,[],[f518])).

fof(f520,plain,
    ( ~ spl3_59
    | spl3_2
    | ~ spl3_23
    | ~ spl3_34
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f516,f466,f260,f204,f72,f518])).

fof(f72,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f204,plain,
    ( spl3_23
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f260,plain,
    ( spl3_34
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f466,plain,
    ( spl3_54
  <=> k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f516,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_23
    | ~ spl3_34
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f515,f467])).

fof(f467,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f466])).

fof(f515,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_23
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f514,f261])).

fof(f261,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f260])).

fof(f514,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f73,f205])).

fof(f205,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f204])).

fof(f73,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f513,plain,(
    spl3_58 ),
    inference(avatar_contradiction_clause,[],[f512])).

fof(f512,plain,
    ( $false
    | spl3_58 ),
    inference(resolution,[],[f497,f43])).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f497,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_58 ),
    inference(avatar_component_clause,[],[f496])).

fof(f501,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k2_funct_1(k1_xboole_0)
    | k1_xboole_0 != sK1
    | sK1 != k2_relat_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f498,plain,
    ( ~ spl3_58
    | spl3_47
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f491,f466,f347,f496])).

fof(f347,plain,
    ( spl3_47
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f491,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_47
    | ~ spl3_54 ),
    inference(superposition,[],[f348,f467])).

fof(f348,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_47 ),
    inference(avatar_component_clause,[],[f347])).

fof(f469,plain,
    ( spl3_54
    | ~ spl3_9
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f462,f452,f99,f466])).

fof(f99,plain,
    ( spl3_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f452,plain,
    ( spl3_53
  <=> v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f462,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_9
    | ~ spl3_53 ),
    inference(resolution,[],[f453,f108])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_9 ),
    inference(resolution,[],[f53,f100])).

fof(f100,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f453,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f452])).

fof(f454,plain,
    ( spl3_53
    | ~ spl3_9
    | ~ spl3_30
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f450,f260,f241,f99,f452])).

fof(f241,plain,
    ( spl3_30
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f450,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl3_9
    | ~ spl3_30
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f440,f261])).

fof(f440,plain,
    ( v1_xboole_0(k2_funct_1(sK2))
    | ~ spl3_9
    | ~ spl3_30 ),
    inference(resolution,[],[f242,f113])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_xboole_0(X0) )
    | ~ spl3_9 ),
    inference(resolution,[],[f51,f100])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f242,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f241])).

fof(f396,plain,
    ( ~ spl3_47
    | spl3_27
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f306,f260,f222,f347])).

fof(f222,plain,
    ( spl3_27
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f306,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_27
    | ~ spl3_34 ),
    inference(superposition,[],[f223,f261])).

fof(f223,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f222])).

fof(f355,plain,
    ( spl3_34
    | ~ spl3_9
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f287,f268,f99,f260])).

fof(f268,plain,
    ( spl3_36
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f287,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_9
    | ~ spl3_36 ),
    inference(resolution,[],[f269,f108])).

fof(f269,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f268])).

fof(f270,plain,
    ( spl3_36
    | ~ spl3_9
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f257,f233,f99,f268])).

fof(f233,plain,
    ( spl3_28
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f257,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_9
    | ~ spl3_28 ),
    inference(resolution,[],[f234,f115])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | v1_xboole_0(X0) )
    | ~ spl3_9 ),
    inference(resolution,[],[f52,f100])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f234,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f233])).

fof(f243,plain,
    ( spl3_30
    | ~ spl3_18
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f228,f204,f165,f241])).

fof(f165,plain,
    ( spl3_18
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f228,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))
    | ~ spl3_18
    | ~ spl3_23 ),
    inference(superposition,[],[f166,f205])).

fof(f166,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f165])).

fof(f235,plain,
    ( spl3_28
    | ~ spl3_6
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f226,f204,f87,f233])).

% (6997)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f87,plain,
    ( spl3_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f226,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl3_6
    | ~ spl3_23 ),
    inference(superposition,[],[f88,f205])).

fof(f88,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f224,plain,
    ( ~ spl3_27
    | spl3_3
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f220,f204,f75,f222])).

fof(f75,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f220,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f76,f205])).

fof(f76,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f209,plain,
    ( sK1 != k2_relat_1(sK2)
    | sK0 != k1_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f208,plain,
    ( sK1 != k2_relat_1(sK2)
    | sK0 != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f207,plain,
    ( spl3_22
    | spl3_23
    | ~ spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f198,f87,f91,f204,f201])).

fof(f201,plain,
    ( spl3_22
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f91,plain,
    ( spl3_7
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f198,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f193,f88])).

fof(f193,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | k1_relat_1(X5) = X3 ) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f57,f56])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f167,plain,
    ( spl3_18
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f160,f153,f134,f165])).

fof(f134,plain,
    ( spl3_14
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f153,plain,
    ( spl3_16
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f160,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(superposition,[],[f135,f154])).

fof(f154,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f153])).

fof(f135,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f156,plain,
    ( ~ spl3_6
    | spl3_16
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f150,f79,f153,f87])).

fof(f79,plain,
    ( spl3_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f150,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_4 ),
    inference(superposition,[],[f80,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f80,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f144,plain,
    ( ~ spl3_10
    | ~ spl3_8
    | spl3_13 ),
    inference(avatar_split_clause,[],[f142,f131,f95,f104])).

fof(f104,plain,
    ( spl3_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f95,plain,
    ( spl3_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f131,plain,
    ( spl3_13
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f142,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_13 ),
    inference(resolution,[],[f132,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f132,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f141,plain,
    ( ~ spl3_13
    | ~ spl3_1
    | spl3_15
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f137,f124,f119,f139,f69,f131])).

fof(f69,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f139,plain,
    ( spl3_15
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f119,plain,
    ( spl3_11
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f124,plain,
    ( spl3_12
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f137,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f128,f125])).

fof(f125,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f128,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_11 ),
    inference(superposition,[],[f45,f120])).

fof(f120,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f119])).

fof(f45,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f136,plain,
    ( ~ spl3_13
    | ~ spl3_1
    | spl3_14
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f129,f124,f119,f134,f69,f131])).

fof(f129,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f127,f125])).

fof(f127,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_11 ),
    inference(superposition,[],[f46,f120])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f126,plain,
    ( ~ spl3_10
    | ~ spl3_8
    | spl3_12
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f122,f83,f124,f95,f104])).

fof(f83,plain,
    ( spl3_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f122,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f50,f84])).

fof(f84,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f121,plain,
    ( ~ spl3_10
    | ~ spl3_8
    | spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f117,f83,f119,f95,f104])).

fof(f117,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f49,f84])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f111,plain,
    ( ~ spl3_6
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl3_6
    | spl3_10 ),
    inference(subsumption_resolution,[],[f88,f109])).

fof(f109,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_10 ),
    inference(resolution,[],[f54,f105])).

fof(f105,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f107,plain,
    ( ~ spl3_10
    | ~ spl3_8
    | spl3_1 ),
    inference(avatar_split_clause,[],[f102,f69,f95,f104])).

fof(f102,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(resolution,[],[f48,f70])).

fof(f70,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f42,f99])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f97,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f36,f95])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f33])).

fof(f33,plain,
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

fof(f93,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f37,f91])).

fof(f37,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f38,f87])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f39,f83])).

fof(f39,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f40,f79])).

fof(f40,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f41,f75,f72,f69])).

fof(f41,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:44:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (6995)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (7004)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (6996)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (7003)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (7003)Refutation not found, incomplete strategy% (7003)------------------------------
% 0.21/0.50  % (7003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7003)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (7003)Memory used [KB]: 1663
% 0.21/0.50  % (7003)Time elapsed: 0.073 s
% 0.21/0.50  % (7003)------------------------------
% 0.21/0.50  % (7003)------------------------------
% 0.21/0.50  % (6996)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f534,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f77,f81,f85,f89,f93,f97,f101,f107,f111,f121,f126,f136,f141,f144,f156,f167,f207,f208,f209,f224,f235,f243,f270,f355,f396,f454,f469,f498,f501,f513,f520,f526,f533])).
% 0.21/0.50  fof(f533,plain,(
% 0.21/0.50    ~spl3_58 | ~spl3_56 | spl3_60),
% 0.21/0.50    inference(avatar_split_clause,[],[f532,f524,f474,f496])).
% 0.21/0.50  fof(f496,plain,(
% 0.21/0.50    spl3_58 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.21/0.50  fof(f474,plain,(
% 0.21/0.50    spl3_56 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.21/0.50  fof(f524,plain,(
% 0.21/0.50    spl3_60 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 0.21/0.50  fof(f532,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_56 | spl3_60)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f531])).
% 0.21/0.50  fof(f531,plain,(
% 0.21/0.50    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_56 | spl3_60)),
% 0.21/0.50    inference(forward_demodulation,[],[f529,f475])).
% 0.21/0.50  fof(f475,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_56),
% 0.21/0.50    inference(avatar_component_clause,[],[f474])).
% 0.21/0.50  fof(f529,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_60),
% 0.21/0.50    inference(superposition,[],[f525,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f525,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | spl3_60),
% 0.21/0.50    inference(avatar_component_clause,[],[f524])).
% 0.21/0.50  fof(f526,plain,(
% 0.21/0.50    ~spl3_58 | ~spl3_60 | spl3_59),
% 0.21/0.50    inference(avatar_split_clause,[],[f521,f518,f524,f496])).
% 0.21/0.50  fof(f518,plain,(
% 0.21/0.50    spl3_59 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.21/0.50  fof(f521,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_59),
% 0.21/0.50    inference(resolution,[],[f519,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.50    inference(equality_resolution,[],[f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f519,plain,(
% 0.21/0.50    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | spl3_59),
% 0.21/0.50    inference(avatar_component_clause,[],[f518])).
% 0.21/0.50  fof(f520,plain,(
% 0.21/0.50    ~spl3_59 | spl3_2 | ~spl3_23 | ~spl3_34 | ~spl3_54),
% 0.21/0.50    inference(avatar_split_clause,[],[f516,f466,f260,f204,f72,f518])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    spl3_23 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    spl3_34 <=> k1_xboole_0 = sK2),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.50  fof(f466,plain,(
% 0.21/0.50    spl3_54 <=> k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.21/0.50  fof(f516,plain,(
% 0.21/0.50    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl3_2 | ~spl3_23 | ~spl3_34 | ~spl3_54)),
% 0.21/0.50    inference(forward_demodulation,[],[f515,f467])).
% 0.21/0.50  fof(f467,plain,(
% 0.21/0.50    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl3_54),
% 0.21/0.50    inference(avatar_component_clause,[],[f466])).
% 0.21/0.50  fof(f515,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl3_2 | ~spl3_23 | ~spl3_34)),
% 0.21/0.50    inference(forward_demodulation,[],[f514,f261])).
% 0.21/0.50  fof(f261,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | ~spl3_34),
% 0.21/0.50    inference(avatar_component_clause,[],[f260])).
% 0.21/0.50  fof(f514,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl3_2 | ~spl3_23)),
% 0.21/0.50    inference(forward_demodulation,[],[f73,f205])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~spl3_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f204])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f72])).
% 0.21/0.50  fof(f513,plain,(
% 0.21/0.50    spl3_58),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f512])).
% 0.21/0.50  fof(f512,plain,(
% 0.21/0.50    $false | spl3_58),
% 0.21/0.50    inference(resolution,[],[f497,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.50  fof(f497,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_58),
% 0.21/0.50    inference(avatar_component_clause,[],[f496])).
% 0.21/0.50  fof(f501,plain,(
% 0.21/0.50    k1_xboole_0 != sK2 | k1_xboole_0 != k2_funct_1(k1_xboole_0) | k1_xboole_0 != sK1 | sK1 != k2_relat_1(sK2) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f498,plain,(
% 0.21/0.50    ~spl3_58 | spl3_47 | ~spl3_54),
% 0.21/0.50    inference(avatar_split_clause,[],[f491,f466,f347,f496])).
% 0.21/0.50  fof(f347,plain,(
% 0.21/0.50    spl3_47 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.50  fof(f491,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_47 | ~spl3_54)),
% 0.21/0.50    inference(superposition,[],[f348,f467])).
% 0.21/0.50  fof(f348,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_47),
% 0.21/0.50    inference(avatar_component_clause,[],[f347])).
% 0.21/0.50  fof(f469,plain,(
% 0.21/0.50    spl3_54 | ~spl3_9 | ~spl3_53),
% 0.21/0.50    inference(avatar_split_clause,[],[f462,f452,f99,f466])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl3_9 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.50  fof(f452,plain,(
% 0.21/0.50    spl3_53 <=> v1_xboole_0(k2_funct_1(k1_xboole_0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.21/0.50  fof(f462,plain,(
% 0.21/0.50    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_9 | ~spl3_53)),
% 0.21/0.50    inference(resolution,[],[f453,f108])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_9),
% 0.21/0.50    inference(resolution,[],[f53,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0) | ~spl3_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f99])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.50  fof(f453,plain,(
% 0.21/0.50    v1_xboole_0(k2_funct_1(k1_xboole_0)) | ~spl3_53),
% 0.21/0.50    inference(avatar_component_clause,[],[f452])).
% 0.21/0.50  fof(f454,plain,(
% 0.21/0.50    spl3_53 | ~spl3_9 | ~spl3_30 | ~spl3_34),
% 0.21/0.50    inference(avatar_split_clause,[],[f450,f260,f241,f99,f452])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    spl3_30 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.50  fof(f450,plain,(
% 0.21/0.50    v1_xboole_0(k2_funct_1(k1_xboole_0)) | (~spl3_9 | ~spl3_30 | ~spl3_34)),
% 0.21/0.50    inference(forward_demodulation,[],[f440,f261])).
% 0.21/0.50  fof(f440,plain,(
% 0.21/0.50    v1_xboole_0(k2_funct_1(sK2)) | (~spl3_9 | ~spl3_30)),
% 0.21/0.50    inference(resolution,[],[f242,f113])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(X0)) ) | ~spl3_9),
% 0.21/0.50    inference(resolution,[],[f51,f100])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) | ~spl3_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f241])).
% 0.21/0.50  fof(f396,plain,(
% 0.21/0.50    ~spl3_47 | spl3_27 | ~spl3_34),
% 0.21/0.50    inference(avatar_split_clause,[],[f306,f260,f222,f347])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    spl3_27 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.50  fof(f306,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_27 | ~spl3_34)),
% 0.21/0.50    inference(superposition,[],[f223,f261])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f222])).
% 0.21/0.50  fof(f355,plain,(
% 0.21/0.50    spl3_34 | ~spl3_9 | ~spl3_36),
% 0.21/0.50    inference(avatar_split_clause,[],[f287,f268,f99,f260])).
% 0.21/0.50  fof(f268,plain,(
% 0.21/0.50    spl3_36 <=> v1_xboole_0(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | (~spl3_9 | ~spl3_36)),
% 0.21/0.50    inference(resolution,[],[f269,f108])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    v1_xboole_0(sK2) | ~spl3_36),
% 0.21/0.50    inference(avatar_component_clause,[],[f268])).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    spl3_36 | ~spl3_9 | ~spl3_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f257,f233,f99,f268])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    spl3_28 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    v1_xboole_0(sK2) | (~spl3_9 | ~spl3_28)),
% 0.21/0.50    inference(resolution,[],[f234,f115])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) ) | ~spl3_9),
% 0.21/0.50    inference(resolution,[],[f52,f100])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl3_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f233])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    spl3_30 | ~spl3_18 | ~spl3_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f228,f204,f165,f241])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    spl3_18 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) | (~spl3_18 | ~spl3_23)),
% 0.21/0.50    inference(superposition,[],[f166,f205])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~spl3_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f165])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    spl3_28 | ~spl3_6 | ~spl3_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f226,f204,f87,f233])).
% 0.21/0.50  % (6997)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl3_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f226,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl3_6 | ~spl3_23)),
% 0.21/0.50    inference(superposition,[],[f88,f205])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f87])).
% 0.21/0.50  fof(f224,plain,(
% 0.21/0.50    ~spl3_27 | spl3_3 | ~spl3_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f220,f204,f75,f222])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_23)),
% 0.21/0.50    inference(forward_demodulation,[],[f76,f205])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f75])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    sK1 != k2_relat_1(sK2) | sK0 != k1_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    sK1 != k2_relat_1(sK2) | sK0 != k1_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    spl3_22 | spl3_23 | ~spl3_7 | ~spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f198,f87,f91,f204,f201])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    spl3_22 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl3_7 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relat_1(sK2) | ~spl3_6),
% 0.21/0.50    inference(resolution,[],[f193,f88])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | k1_relat_1(X5) = X3) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f190])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.50    inference(superposition,[],[f57,f56])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    spl3_18 | ~spl3_14 | ~spl3_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f160,f153,f134,f165])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    spl3_14 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    spl3_16 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl3_14 | ~spl3_16)),
% 0.21/0.50    inference(superposition,[],[f135,f154])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    sK1 = k2_relat_1(sK2) | ~spl3_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f153])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f134])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    ~spl3_6 | spl3_16 | ~spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f150,f79,f153,f87])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    spl3_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_4),
% 0.21/0.50    inference(superposition,[],[f80,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f79])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    ~spl3_10 | ~spl3_8 | spl3_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f142,f131,f95,f104])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl3_10 <=> v1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    spl3_8 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl3_13 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_13),
% 0.21/0.50    inference(resolution,[],[f132,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    ~v1_relat_1(k2_funct_1(sK2)) | spl3_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f131])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    ~spl3_13 | ~spl3_1 | spl3_15 | ~spl3_11 | ~spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f137,f124,f119,f139,f69,f131])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    spl3_15 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl3_11 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    spl3_12 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_11 | ~spl3_12)),
% 0.21/0.50    inference(forward_demodulation,[],[f128,f125])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f124])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_11),
% 0.21/0.50    inference(superposition,[],[f45,f120])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f119])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    ~spl3_13 | ~spl3_1 | spl3_14 | ~spl3_11 | ~spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f129,f124,f119,f134,f69,f131])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_11 | ~spl3_12)),
% 0.21/0.50    inference(forward_demodulation,[],[f127,f125])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_11),
% 0.21/0.50    inference(superposition,[],[f46,f120])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    ~spl3_10 | ~spl3_8 | spl3_12 | ~spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f122,f83,f124,f95,f104])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    spl3_5 <=> v2_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_5),
% 0.21/0.50    inference(resolution,[],[f50,f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    v2_funct_1(sK2) | ~spl3_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f83])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ~spl3_10 | ~spl3_8 | spl3_11 | ~spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f117,f83,f119,f95,f104])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_5),
% 0.21/0.50    inference(resolution,[],[f49,f84])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    ~spl3_6 | spl3_10),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f110])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    $false | (~spl3_6 | spl3_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f88,f109])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_10),
% 0.21/0.50    inference(resolution,[],[f54,f105])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | spl3_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f104])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ~spl3_10 | ~spl3_8 | spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f102,f69,f95,f104])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_1),
% 0.21/0.50    inference(resolution,[],[f48,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f69])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f99])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl3_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f36,f95])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f14])).
% 0.21/0.50  fof(f14,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f37,f91])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f38,f87])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f39,f83])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    v2_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f40,f79])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f41,f75,f72,f69])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (6996)------------------------------
% 0.21/0.50  % (6996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (6996)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (6996)Memory used [KB]: 10874
% 0.21/0.50  % (6996)Time elapsed: 0.075 s
% 0.21/0.50  % (6996)------------------------------
% 0.21/0.50  % (6996)------------------------------
% 0.21/0.51  % (6989)Success in time 0.138 s
%------------------------------------------------------------------------------
