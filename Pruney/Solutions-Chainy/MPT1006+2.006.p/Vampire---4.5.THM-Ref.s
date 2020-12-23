%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 181 expanded)
%              Number of leaves         :   27 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  331 ( 518 expanded)
%              Number of equality atoms :   97 ( 188 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f233,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f74,f82,f86,f90,f94,f110,f113,f125,f141,f166,f210,f219,f230])).

fof(f230,plain,(
    ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl3_19 ),
    inference(resolution,[],[f205,f41])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f205,plain,
    ( ! [X2,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl3_19
  <=> ! [X1,X2] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f219,plain,
    ( ~ spl3_10
    | ~ spl3_11
    | spl3_16
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl3_10
    | ~ spl3_11
    | spl3_16
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f165,f213])).

fof(f213,plain,
    ( ! [X1] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(superposition,[],[f212,f178])).

fof(f178,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k1_xboole_0) = k10_relat_1(k1_xboole_0,X1) ),
    inference(resolution,[],[f172,f41])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f52,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f212,plain,
    ( ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f148,f211])).

fof(f211,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl3_20 ),
    inference(resolution,[],[f209,f40])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f209,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl3_20
  <=> ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ r1_tarski(k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) )
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f147,f124])).

fof(f124,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_11
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f147,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
        | ~ v1_funct_2(sK2,k1_xboole_0,X0) )
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f145,f124])).

fof(f145,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK2)
        | ~ v1_funct_2(sK2,k1_xboole_0,X0) )
    | ~ spl3_10 ),
    inference(resolution,[],[f105,f109])).

fof(f109,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl3_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f105,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f66,f61])).

fof(f61,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f66,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f165,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl3_16
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f210,plain,
    ( spl3_19
    | ~ spl3_14
    | spl3_20
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f202,f92,f88,f208,f139,f204])).

fof(f139,plain,
    ( spl3_14
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f88,plain,
    ( spl3_6
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f92,plain,
    ( spl3_7
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f202,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ r1_tarski(k1_xboole_0,X0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f201,f93])).

fof(f93,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f201,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ v1_funct_1(k1_xboole_0)
        | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl3_6 ),
    inference(superposition,[],[f142,f89])).

fof(f89,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f45,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f166,plain,
    ( ~ spl3_16
    | ~ spl3_9
    | spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f162,f123,f68,f100,f164])).

fof(f100,plain,
    ( spl3_9
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f68,plain,
    ( spl3_1
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f162,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl3_1
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f161,f124])).

fof(f161,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl3_1
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f160,f61])).

fof(f160,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_1
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f158,f124])).

fof(f158,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_1 ),
    inference(superposition,[],[f69,f59])).

fof(f69,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f141,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f129,f123,f80,f139])).

fof(f80,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f129,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(superposition,[],[f81,f124])).

fof(f81,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f125,plain,
    ( spl3_11
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f120,f108,f84,f123])).

fof(f84,plain,
    ( spl3_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f120,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(resolution,[],[f119,f109])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f117,f61])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_xboole_0 = X0 )
    | ~ spl3_5 ),
    inference(resolution,[],[f114,f85])).

fof(f85,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f43,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f113,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f101,f41])).

fof(f101,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f110,plain,
    ( spl3_10
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f106,f72,f108])).

fof(f72,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f106,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f73,f61])).

fof(f73,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f94,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f38,f92])).

fof(f38,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f90,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f39,f88])).

fof(f39,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f86,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f37,f84])).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f82,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f33,f80])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_2(sK2,k1_xboole_0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
      & v1_funct_2(sK2,k1_xboole_0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

fof(f74,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f35,f72])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f36,f68])).

fof(f36,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:03:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (5502)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.41  % (5502)Refutation not found, incomplete strategy% (5502)------------------------------
% 0.21/0.41  % (5502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (5502)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.41  
% 0.21/0.41  % (5502)Memory used [KB]: 1663
% 0.21/0.41  % (5502)Time elapsed: 0.004 s
% 0.21/0.41  % (5502)------------------------------
% 0.21/0.41  % (5502)------------------------------
% 0.21/0.45  % (5495)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.45  % (5495)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f233,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f70,f74,f82,f86,f90,f94,f110,f113,f125,f141,f166,f210,f219,f230])).
% 0.21/0.45  fof(f230,plain,(
% 0.21/0.45    ~spl3_19),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f227])).
% 0.21/0.45  fof(f227,plain,(
% 0.21/0.45    $false | ~spl3_19),
% 0.21/0.45    inference(resolution,[],[f205,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.45  fof(f205,plain,(
% 0.21/0.45    ( ! [X2,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl3_19),
% 0.21/0.45    inference(avatar_component_clause,[],[f204])).
% 0.21/0.45  fof(f204,plain,(
% 0.21/0.45    spl3_19 <=> ! [X1,X2] : ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.45  fof(f219,plain,(
% 0.21/0.45    ~spl3_10 | ~spl3_11 | spl3_16 | ~spl3_20),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f217])).
% 0.21/0.45  fof(f217,plain,(
% 0.21/0.45    $false | (~spl3_10 | ~spl3_11 | spl3_16 | ~spl3_20)),
% 0.21/0.45    inference(subsumption_resolution,[],[f165,f213])).
% 0.21/0.45  fof(f213,plain,(
% 0.21/0.45    ( ! [X1] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)) ) | (~spl3_10 | ~spl3_11 | ~spl3_20)),
% 0.21/0.45    inference(superposition,[],[f212,f178])).
% 0.21/0.45  fof(f178,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = k10_relat_1(k1_xboole_0,X1)) )),
% 0.21/0.45    inference(resolution,[],[f172,f41])).
% 0.21/0.45  fof(f172,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)) )),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f169])).
% 0.21/0.45  fof(f169,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(superposition,[],[f52,f59])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.45  fof(f212,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) ) | (~spl3_10 | ~spl3_11 | ~spl3_20)),
% 0.21/0.45    inference(subsumption_resolution,[],[f148,f211])).
% 0.21/0.45  fof(f211,plain,(
% 0.21/0.45    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl3_20),
% 0.21/0.45    inference(resolution,[],[f209,f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.45  fof(f209,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl3_20),
% 0.21/0.45    inference(avatar_component_clause,[],[f208])).
% 0.21/0.45  fof(f208,plain,(
% 0.21/0.45    spl3_20 <=> ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.45  fof(f148,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) ) | (~spl3_10 | ~spl3_11)),
% 0.21/0.45    inference(forward_demodulation,[],[f147,f124])).
% 0.21/0.45  fof(f124,plain,(
% 0.21/0.45    k1_xboole_0 = sK2 | ~spl3_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f123])).
% 0.21/0.45  fof(f123,plain,(
% 0.21/0.45    spl3_11 <=> k1_xboole_0 = sK2),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.45  fof(f147,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) | ~v1_funct_2(sK2,k1_xboole_0,X0)) ) | (~spl3_10 | ~spl3_11)),
% 0.21/0.45    inference(forward_demodulation,[],[f145,f124])).
% 0.21/0.45  fof(f145,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK2) | ~v1_funct_2(sK2,k1_xboole_0,X0)) ) | ~spl3_10),
% 0.21/0.45    inference(resolution,[],[f105,f109])).
% 0.21/0.45  fof(f109,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f108])).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    spl3_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.45  fof(f105,plain,(
% 0.21/0.45    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f66,f61])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.45    inference(equality_resolution,[],[f48])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.45    inference(flattening,[],[f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.45    inference(equality_resolution,[],[f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(nnf_transformation,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(flattening,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.45  fof(f165,plain,(
% 0.21/0.45    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | spl3_16),
% 0.21/0.45    inference(avatar_component_clause,[],[f164])).
% 0.21/0.45  fof(f164,plain,(
% 0.21/0.45    spl3_16 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.45  fof(f210,plain,(
% 0.21/0.45    spl3_19 | ~spl3_14 | spl3_20 | ~spl3_6 | ~spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f202,f92,f88,f208,f139,f204])).
% 0.21/0.45  fof(f139,plain,(
% 0.21/0.45    spl3_14 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    spl3_6 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    spl3_7 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.45  fof(f202,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | (~spl3_6 | ~spl3_7)),
% 0.21/0.45    inference(forward_demodulation,[],[f201,f93])).
% 0.21/0.45  fof(f93,plain,(
% 0.21/0.45    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f92])).
% 0.21/0.45  fof(f201,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl3_6),
% 0.21/0.45    inference(superposition,[],[f142,f89])).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl3_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f88])).
% 0.21/0.45  fof(f142,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relat_1(X0),X1) | ~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.21/0.45    inference(resolution,[],[f45,f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(flattening,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,axiom,(
% 0.21/0.45    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.45  fof(f166,plain,(
% 0.21/0.45    ~spl3_16 | ~spl3_9 | spl3_1 | ~spl3_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f162,f123,f68,f100,f164])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    spl3_9 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    spl3_1 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f162,plain,(
% 0.21/0.45    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | (spl3_1 | ~spl3_11)),
% 0.21/0.45    inference(forward_demodulation,[],[f161,f124])).
% 0.21/0.45  fof(f161,plain,(
% 0.21/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | (spl3_1 | ~spl3_11)),
% 0.21/0.45    inference(forward_demodulation,[],[f160,f61])).
% 0.21/0.45  fof(f160,plain,(
% 0.21/0.45    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_1 | ~spl3_11)),
% 0.21/0.45    inference(forward_demodulation,[],[f158,f124])).
% 0.21/0.45  fof(f158,plain,(
% 0.21/0.45    k1_xboole_0 != k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_1),
% 0.21/0.45    inference(superposition,[],[f69,f59])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f68])).
% 0.21/0.45  fof(f141,plain,(
% 0.21/0.45    spl3_14 | ~spl3_4 | ~spl3_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f129,f123,f80,f139])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    spl3_4 <=> v1_funct_1(sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f129,plain,(
% 0.21/0.45    v1_funct_1(k1_xboole_0) | (~spl3_4 | ~spl3_11)),
% 0.21/0.45    inference(superposition,[],[f81,f124])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    v1_funct_1(sK2) | ~spl3_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f80])).
% 0.21/0.45  fof(f125,plain,(
% 0.21/0.45    spl3_11 | ~spl3_5 | ~spl3_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f120,f108,f84,f123])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    spl3_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.45  fof(f120,plain,(
% 0.21/0.45    k1_xboole_0 = sK2 | (~spl3_5 | ~spl3_10)),
% 0.21/0.45    inference(resolution,[],[f119,f109])).
% 0.21/0.45  fof(f119,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl3_5),
% 0.21/0.45    inference(forward_demodulation,[],[f117,f61])).
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = X0) ) | ~spl3_5),
% 0.21/0.45    inference(resolution,[],[f114,f85])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    v1_xboole_0(k1_xboole_0) | ~spl3_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f84])).
% 0.21/0.45  fof(f114,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X0) )),
% 0.21/0.45    inference(resolution,[],[f43,f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    spl3_9),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.45  fof(f112,plain,(
% 0.21/0.45    $false | spl3_9),
% 0.21/0.45    inference(resolution,[],[f101,f41])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl3_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f100])).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    spl3_10 | ~spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f106,f72,f108])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_2),
% 0.21/0.45    inference(forward_demodulation,[],[f73,f61])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f72])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f38,f92])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    spl3_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f39,f88])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    spl3_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f37,f84])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    v1_xboole_0(k1_xboole_0)),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    v1_xboole_0(k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    spl3_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f33,f80])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    v1_funct_1(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.21/0.45    inference(flattening,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.21/0.45    inference(ennf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.45    inference(negated_conjecture,[],[f14])).
% 0.21/0.45  fof(f14,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f35,f72])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    ~spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f36,f68])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (5495)------------------------------
% 0.21/0.45  % (5495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (5495)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (5495)Memory used [KB]: 10746
% 0.21/0.46  % (5495)Time elapsed: 0.032 s
% 0.21/0.46  % (5495)------------------------------
% 0.21/0.46  % (5495)------------------------------
% 0.21/0.46  % (5488)Success in time 0.1 s
%------------------------------------------------------------------------------
