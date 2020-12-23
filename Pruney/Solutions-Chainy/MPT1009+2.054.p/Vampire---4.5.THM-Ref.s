%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:33 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 190 expanded)
%              Number of leaves         :   22 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  300 ( 506 expanded)
%              Number of equality atoms :   63 ( 100 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f224,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f75,f85,f90,f104,f118,f123,f136,f178,f202,f219])).

fof(f219,plain,
    ( ~ spl4_6
    | ~ spl4_9
    | spl4_16 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_9
    | spl4_16 ),
    inference(subsumption_resolution,[],[f216,f55])).

fof(f55,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f216,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK3,sK0)))
    | ~ spl4_6
    | ~ spl4_9
    | spl4_16 ),
    inference(backward_demodulation,[],[f201,f211])).

fof(f211,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f205,f89])).

fof(f89,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f205,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9 ),
    inference(trivial_inequality_removal,[],[f204])).

fof(f204,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9 ),
    inference(superposition,[],[f38,f114])).

fof(f114,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_9
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f201,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl4_16
  <=> r1_tarski(k2_relat_1(sK3),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f202,plain,
    ( ~ spl4_16
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f190,f112,f87,f82,f199])).

fof(f82,plain,
    ( spl4_5
  <=> r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f190,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f84,f183])).

fof(f183,plain,
    ( ! [X0] : k9_relat_1(sK3,X0) = k2_relat_1(sK3)
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f180,f35])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f180,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | k9_relat_1(sK3,X0) = k2_relat_1(sK3) )
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f110,f114])).

fof(f110,plain,
    ( ! [X0] :
        ( k9_relat_1(sK3,X0) = k2_relat_1(sK3)
        | ~ r1_tarski(k1_relat_1(sK3),X0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f106,f92])).

fof(f92,plain,
    ( ! [X1] :
        ( v4_relat_1(sK3,X1)
        | ~ r1_tarski(k1_relat_1(sK3),X1) )
    | ~ spl4_6 ),
    inference(resolution,[],[f89,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f106,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | k9_relat_1(sK3,X0) = k2_relat_1(sK3) )
    | ~ spl4_6 ),
    inference(superposition,[],[f94,f91])).

fof(f91,plain,
    ( ! [X0] :
        ( sK3 = k7_relat_1(sK3,X0)
        | ~ v4_relat_1(sK3,X0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f89,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f94,plain,
    ( ! [X3] : k9_relat_1(sK3,X3) = k2_relat_1(k7_relat_1(sK3,X3))
    | ~ spl4_6 ),
    inference(resolution,[],[f89,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f84,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f178,plain,
    ( ~ spl4_1
    | spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl4_1
    | spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f176,f172])).

fof(f172,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f171,f122])).

fof(f122,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_11
  <=> k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f171,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,k1_tarski(sK0)))
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(resolution,[],[f148,f103])).

fof(f103,plain,
    ( v4_relat_1(sK3,k1_tarski(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_8
  <=> v4_relat_1(sK3,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(sK3,X0)
        | r1_tarski(k9_relat_1(sK3,X1),k9_relat_1(sK3,X0)) )
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f147,f89])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK3)
        | r1_tarski(k9_relat_1(sK3,X1),k9_relat_1(sK3,X0))
        | ~ v4_relat_1(sK3,X0) )
    | ~ spl4_6 ),
    inference(superposition,[],[f107,f91])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X0))
        | r1_tarski(k9_relat_1(k7_relat_1(sK3,X0),X1),k9_relat_1(sK3,X0)) )
    | ~ spl4_6 ),
    inference(superposition,[],[f40,f94])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f176,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_1
    | spl4_5
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f84,f175])).

fof(f175,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(equality_resolution,[],[f142])).

fof(f142,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK0)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) )
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f141,f89])).

fof(f141,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK0)
        | ~ v1_relat_1(sK3)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) )
    | ~ spl4_1
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f139,f59])).

fof(f59,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f139,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) )
    | ~ spl4_12 ),
    inference(superposition,[],[f44,f135])).

fof(f135,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl4_12
  <=> k1_tarski(sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f136,plain,
    ( spl4_12
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f124,f116,f101,f133])).

fof(f116,plain,
    ( spl4_10
  <=> ! [X0] :
        ( ~ v4_relat_1(sK3,k1_tarski(X0))
        | k1_tarski(X0) = k1_relat_1(sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f124,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(resolution,[],[f117,f103])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,k1_tarski(X0))
        | k1_tarski(X0) = k1_relat_1(sK3) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f123,plain,
    ( spl4_11
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f109,f101,f87,f120])).

fof(f109,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK0))
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(resolution,[],[f106,f103])).

fof(f118,plain,
    ( spl4_9
    | spl4_10
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f105,f87,f116,f112])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,k1_tarski(X0))
        | k1_tarski(X0) = k1_relat_1(sK3)
        | k1_xboole_0 = k1_relat_1(sK3) )
    | ~ spl4_6 ),
    inference(resolution,[],[f93,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f93,plain,
    ( ! [X2] :
        ( r1_tarski(k1_relat_1(sK3),X2)
        | ~ v4_relat_1(sK3,X2) )
    | ~ spl4_6 ),
    inference(resolution,[],[f89,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f104,plain,
    ( spl4_8
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f77,f72,f101])).

fof(f72,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f77,plain,
    ( v4_relat_1(sK3,k1_tarski(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f74,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f74,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f90,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f79,f72,f87])).

fof(f79,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f74,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f85,plain,
    ( ~ spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f80,f72,f82])).

fof(f80,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f34,f76])).

fof(f76,plain,
    ( ! [X0] : k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl4_4 ),
    inference(resolution,[],[f74,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f34,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f75,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f32,f72])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (2221)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (2203)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.24/0.51  % (2203)Refutation not found, incomplete strategy% (2203)------------------------------
% 1.24/0.51  % (2203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.51  % (2203)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.51  
% 1.24/0.51  % (2203)Memory used [KB]: 6268
% 1.24/0.51  % (2203)Time elapsed: 0.098 s
% 1.24/0.51  % (2203)------------------------------
% 1.24/0.51  % (2203)------------------------------
% 1.24/0.51  % (2209)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.24/0.52  % (2201)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.52  % (2222)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.24/0.52  % (2210)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.24/0.52  % (2214)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.24/0.52  % (2223)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.24/0.52  % (2222)Refutation found. Thanks to Tanya!
% 1.24/0.52  % SZS status Theorem for theBenchmark
% 1.24/0.52  % SZS output start Proof for theBenchmark
% 1.24/0.52  fof(f224,plain,(
% 1.24/0.52    $false),
% 1.24/0.52    inference(avatar_sat_refutation,[],[f60,f75,f85,f90,f104,f118,f123,f136,f178,f202,f219])).
% 1.24/0.52  fof(f219,plain,(
% 1.24/0.52    ~spl4_6 | ~spl4_9 | spl4_16),
% 1.24/0.52    inference(avatar_contradiction_clause,[],[f218])).
% 1.24/0.52  fof(f218,plain,(
% 1.24/0.52    $false | (~spl4_6 | ~spl4_9 | spl4_16)),
% 1.24/0.52    inference(subsumption_resolution,[],[f216,f55])).
% 1.24/0.52  fof(f55,plain,(
% 1.24/0.52    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 1.24/0.52    inference(equality_resolution,[],[f47])).
% 1.24/0.52  fof(f47,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 1.24/0.52    inference(cnf_transformation,[],[f5])).
% 1.24/0.52  fof(f5,axiom,(
% 1.24/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.24/0.52  fof(f216,plain,(
% 1.24/0.52    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK3,sK0))) | (~spl4_6 | ~spl4_9 | spl4_16)),
% 1.24/0.52    inference(backward_demodulation,[],[f201,f211])).
% 1.24/0.52  fof(f211,plain,(
% 1.24/0.52    k1_xboole_0 = k2_relat_1(sK3) | (~spl4_6 | ~spl4_9)),
% 1.24/0.52    inference(subsumption_resolution,[],[f205,f89])).
% 1.24/0.52  fof(f89,plain,(
% 1.24/0.52    v1_relat_1(sK3) | ~spl4_6),
% 1.24/0.52    inference(avatar_component_clause,[],[f87])).
% 1.24/0.52  fof(f87,plain,(
% 1.24/0.52    spl4_6 <=> v1_relat_1(sK3)),
% 1.24/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.24/0.52  fof(f205,plain,(
% 1.24/0.52    k1_xboole_0 = k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl4_9),
% 1.24/0.52    inference(trivial_inequality_removal,[],[f204])).
% 1.24/0.52  fof(f204,plain,(
% 1.24/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl4_9),
% 1.24/0.52    inference(superposition,[],[f38,f114])).
% 1.24/0.52  fof(f114,plain,(
% 1.24/0.52    k1_xboole_0 = k1_relat_1(sK3) | ~spl4_9),
% 1.24/0.52    inference(avatar_component_clause,[],[f112])).
% 1.24/0.52  fof(f112,plain,(
% 1.24/0.52    spl4_9 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.24/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.24/0.52  fof(f38,plain,(
% 1.24/0.52    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f19])).
% 1.24/0.52  fof(f19,plain,(
% 1.24/0.52    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.24/0.52    inference(ennf_transformation,[],[f10])).
% 1.24/0.52  fof(f10,axiom,(
% 1.24/0.52    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.24/0.52  fof(f201,plain,(
% 1.24/0.52    ~r1_tarski(k2_relat_1(sK3),k1_tarski(k1_funct_1(sK3,sK0))) | spl4_16),
% 1.24/0.52    inference(avatar_component_clause,[],[f199])).
% 1.24/0.52  fof(f199,plain,(
% 1.24/0.52    spl4_16 <=> r1_tarski(k2_relat_1(sK3),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.24/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.24/0.52  fof(f202,plain,(
% 1.24/0.52    ~spl4_16 | spl4_5 | ~spl4_6 | ~spl4_9),
% 1.24/0.52    inference(avatar_split_clause,[],[f190,f112,f87,f82,f199])).
% 1.24/0.52  fof(f82,plain,(
% 1.24/0.52    spl4_5 <=> r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.24/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.24/0.52  fof(f190,plain,(
% 1.24/0.52    ~r1_tarski(k2_relat_1(sK3),k1_tarski(k1_funct_1(sK3,sK0))) | (spl4_5 | ~spl4_6 | ~spl4_9)),
% 1.24/0.52    inference(backward_demodulation,[],[f84,f183])).
% 1.24/0.52  fof(f183,plain,(
% 1.24/0.52    ( ! [X0] : (k9_relat_1(sK3,X0) = k2_relat_1(sK3)) ) | (~spl4_6 | ~spl4_9)),
% 1.24/0.52    inference(subsumption_resolution,[],[f180,f35])).
% 1.24/0.52  fof(f35,plain,(
% 1.24/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f1])).
% 1.24/0.52  fof(f1,axiom,(
% 1.24/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.24/0.52  fof(f180,plain,(
% 1.24/0.52    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | k9_relat_1(sK3,X0) = k2_relat_1(sK3)) ) | (~spl4_6 | ~spl4_9)),
% 1.24/0.52    inference(backward_demodulation,[],[f110,f114])).
% 1.24/0.52  fof(f110,plain,(
% 1.24/0.52    ( ! [X0] : (k9_relat_1(sK3,X0) = k2_relat_1(sK3) | ~r1_tarski(k1_relat_1(sK3),X0)) ) | ~spl4_6),
% 1.24/0.52    inference(resolution,[],[f106,f92])).
% 1.24/0.52  fof(f92,plain,(
% 1.24/0.52    ( ! [X1] : (v4_relat_1(sK3,X1) | ~r1_tarski(k1_relat_1(sK3),X1)) ) | ~spl4_6),
% 1.24/0.52    inference(resolution,[],[f89,f42])).
% 1.24/0.52  fof(f42,plain,(
% 1.24/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f22])).
% 1.24/0.52  fof(f22,plain,(
% 1.24/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.24/0.52    inference(ennf_transformation,[],[f6])).
% 1.24/0.52  fof(f6,axiom,(
% 1.24/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.24/0.52  fof(f106,plain,(
% 1.24/0.52    ( ! [X0] : (~v4_relat_1(sK3,X0) | k9_relat_1(sK3,X0) = k2_relat_1(sK3)) ) | ~spl4_6),
% 1.24/0.52    inference(superposition,[],[f94,f91])).
% 1.24/0.52  fof(f91,plain,(
% 1.24/0.52    ( ! [X0] : (sK3 = k7_relat_1(sK3,X0) | ~v4_relat_1(sK3,X0)) ) | ~spl4_6),
% 1.24/0.52    inference(resolution,[],[f89,f45])).
% 1.24/0.52  fof(f45,plain,(
% 1.24/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.24/0.52    inference(cnf_transformation,[],[f26])).
% 1.24/0.52  fof(f26,plain,(
% 1.24/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.24/0.52    inference(flattening,[],[f25])).
% 1.24/0.52  fof(f25,plain,(
% 1.24/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.24/0.52    inference(ennf_transformation,[],[f9])).
% 1.24/0.52  fof(f9,axiom,(
% 1.24/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.24/0.52  fof(f94,plain,(
% 1.24/0.52    ( ! [X3] : (k9_relat_1(sK3,X3) = k2_relat_1(k7_relat_1(sK3,X3))) ) | ~spl4_6),
% 1.24/0.52    inference(resolution,[],[f89,f41])).
% 1.24/0.52  fof(f41,plain,(
% 1.24/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 1.24/0.52    inference(cnf_transformation,[],[f21])).
% 1.24/0.53  fof(f21,plain,(
% 1.24/0.53    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.24/0.53    inference(ennf_transformation,[],[f8])).
% 1.24/0.53  fof(f8,axiom,(
% 1.24/0.53    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.24/0.53  fof(f84,plain,(
% 1.24/0.53    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | spl4_5),
% 1.24/0.53    inference(avatar_component_clause,[],[f82])).
% 1.24/0.53  fof(f178,plain,(
% 1.24/0.53    ~spl4_1 | spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_12),
% 1.24/0.53    inference(avatar_contradiction_clause,[],[f177])).
% 1.24/0.53  fof(f177,plain,(
% 1.24/0.53    $false | (~spl4_1 | spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_12)),
% 1.24/0.53    inference(subsumption_resolution,[],[f176,f172])).
% 1.24/0.53  fof(f172,plain,(
% 1.24/0.53    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))) ) | (~spl4_6 | ~spl4_8 | ~spl4_11)),
% 1.24/0.53    inference(forward_demodulation,[],[f171,f122])).
% 1.24/0.53  fof(f122,plain,(
% 1.24/0.53    k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK0)) | ~spl4_11),
% 1.24/0.53    inference(avatar_component_clause,[],[f120])).
% 1.24/0.53  fof(f120,plain,(
% 1.24/0.53    spl4_11 <=> k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK0))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.24/0.53  fof(f171,plain,(
% 1.24/0.53    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,k1_tarski(sK0)))) ) | (~spl4_6 | ~spl4_8)),
% 1.24/0.53    inference(resolution,[],[f148,f103])).
% 1.24/0.53  fof(f103,plain,(
% 1.24/0.53    v4_relat_1(sK3,k1_tarski(sK0)) | ~spl4_8),
% 1.24/0.53    inference(avatar_component_clause,[],[f101])).
% 1.24/0.53  fof(f101,plain,(
% 1.24/0.53    spl4_8 <=> v4_relat_1(sK3,k1_tarski(sK0))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.24/0.53  fof(f148,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~v4_relat_1(sK3,X0) | r1_tarski(k9_relat_1(sK3,X1),k9_relat_1(sK3,X0))) ) | ~spl4_6),
% 1.24/0.53    inference(subsumption_resolution,[],[f147,f89])).
% 1.24/0.53  fof(f147,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~v1_relat_1(sK3) | r1_tarski(k9_relat_1(sK3,X1),k9_relat_1(sK3,X0)) | ~v4_relat_1(sK3,X0)) ) | ~spl4_6),
% 1.24/0.53    inference(superposition,[],[f107,f91])).
% 1.24/0.53  fof(f107,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(sK3,X0)) | r1_tarski(k9_relat_1(k7_relat_1(sK3,X0),X1),k9_relat_1(sK3,X0))) ) | ~spl4_6),
% 1.24/0.53    inference(superposition,[],[f40,f94])).
% 1.24/0.53  fof(f40,plain,(
% 1.24/0.53    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f20])).
% 1.24/0.53  fof(f20,plain,(
% 1.24/0.53    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.24/0.53    inference(ennf_transformation,[],[f7])).
% 1.24/0.53  fof(f7,axiom,(
% 1.24/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.24/0.53  fof(f176,plain,(
% 1.24/0.53    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | (~spl4_1 | spl4_5 | ~spl4_6 | ~spl4_12)),
% 1.24/0.53    inference(backward_demodulation,[],[f84,f175])).
% 1.24/0.53  fof(f175,plain,(
% 1.24/0.53    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | (~spl4_1 | ~spl4_6 | ~spl4_12)),
% 1.24/0.53    inference(equality_resolution,[],[f142])).
% 1.24/0.53  fof(f142,plain,(
% 1.24/0.53    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) ) | (~spl4_1 | ~spl4_6 | ~spl4_12)),
% 1.24/0.53    inference(subsumption_resolution,[],[f141,f89])).
% 1.24/0.53  fof(f141,plain,(
% 1.24/0.53    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | ~v1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) ) | (~spl4_1 | ~spl4_12)),
% 1.24/0.53    inference(subsumption_resolution,[],[f139,f59])).
% 1.24/0.53  fof(f59,plain,(
% 1.24/0.53    v1_funct_1(sK3) | ~spl4_1),
% 1.24/0.53    inference(avatar_component_clause,[],[f57])).
% 1.24/0.53  fof(f57,plain,(
% 1.24/0.53    spl4_1 <=> v1_funct_1(sK3)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.24/0.53  fof(f139,plain,(
% 1.24/0.53    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) ) | ~spl4_12),
% 1.24/0.53    inference(superposition,[],[f44,f135])).
% 1.24/0.53  fof(f135,plain,(
% 1.24/0.53    k1_tarski(sK0) = k1_relat_1(sK3) | ~spl4_12),
% 1.24/0.53    inference(avatar_component_clause,[],[f133])).
% 1.24/0.53  fof(f133,plain,(
% 1.24/0.53    spl4_12 <=> k1_tarski(sK0) = k1_relat_1(sK3)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.24/0.53  fof(f44,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f24])).
% 1.24/0.53  fof(f24,plain,(
% 1.24/0.53    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.24/0.53    inference(flattening,[],[f23])).
% 1.24/0.53  fof(f23,plain,(
% 1.24/0.53    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.24/0.53    inference(ennf_transformation,[],[f11])).
% 1.24/0.53  fof(f11,axiom,(
% 1.24/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.24/0.53  fof(f136,plain,(
% 1.24/0.53    spl4_12 | ~spl4_8 | ~spl4_10),
% 1.24/0.53    inference(avatar_split_clause,[],[f124,f116,f101,f133])).
% 1.24/0.53  fof(f116,plain,(
% 1.24/0.53    spl4_10 <=> ! [X0] : (~v4_relat_1(sK3,k1_tarski(X0)) | k1_tarski(X0) = k1_relat_1(sK3))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.24/0.53  fof(f124,plain,(
% 1.24/0.53    k1_tarski(sK0) = k1_relat_1(sK3) | (~spl4_8 | ~spl4_10)),
% 1.24/0.53    inference(resolution,[],[f117,f103])).
% 1.24/0.53  fof(f117,plain,(
% 1.24/0.53    ( ! [X0] : (~v4_relat_1(sK3,k1_tarski(X0)) | k1_tarski(X0) = k1_relat_1(sK3)) ) | ~spl4_10),
% 1.24/0.53    inference(avatar_component_clause,[],[f116])).
% 1.24/0.53  fof(f123,plain,(
% 1.24/0.53    spl4_11 | ~spl4_6 | ~spl4_8),
% 1.24/0.53    inference(avatar_split_clause,[],[f109,f101,f87,f120])).
% 1.24/0.53  fof(f109,plain,(
% 1.24/0.53    k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK0)) | (~spl4_6 | ~spl4_8)),
% 1.24/0.53    inference(resolution,[],[f106,f103])).
% 1.24/0.53  fof(f118,plain,(
% 1.24/0.53    spl4_9 | spl4_10 | ~spl4_6),
% 1.24/0.53    inference(avatar_split_clause,[],[f105,f87,f116,f112])).
% 1.24/0.53  fof(f105,plain,(
% 1.24/0.53    ( ! [X0] : (~v4_relat_1(sK3,k1_tarski(X0)) | k1_tarski(X0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)) ) | ~spl4_6),
% 1.24/0.53    inference(resolution,[],[f93,f46])).
% 1.24/0.53  fof(f46,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 1.24/0.53    inference(cnf_transformation,[],[f5])).
% 1.24/0.53  fof(f93,plain,(
% 1.24/0.53    ( ! [X2] : (r1_tarski(k1_relat_1(sK3),X2) | ~v4_relat_1(sK3,X2)) ) | ~spl4_6),
% 1.24/0.53    inference(resolution,[],[f89,f43])).
% 1.24/0.53  fof(f43,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f22])).
% 1.24/0.53  fof(f104,plain,(
% 1.24/0.53    spl4_8 | ~spl4_4),
% 1.24/0.53    inference(avatar_split_clause,[],[f77,f72,f101])).
% 1.24/0.53  fof(f72,plain,(
% 1.24/0.53    spl4_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.24/0.53  fof(f77,plain,(
% 1.24/0.53    v4_relat_1(sK3,k1_tarski(sK0)) | ~spl4_4),
% 1.24/0.53    inference(resolution,[],[f74,f51])).
% 1.24/0.53  fof(f51,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f28])).
% 1.24/0.53  fof(f28,plain,(
% 1.24/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.53    inference(ennf_transformation,[],[f13])).
% 1.24/0.53  fof(f13,axiom,(
% 1.24/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.24/0.53  fof(f74,plain,(
% 1.24/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~spl4_4),
% 1.24/0.53    inference(avatar_component_clause,[],[f72])).
% 1.24/0.53  fof(f90,plain,(
% 1.24/0.53    spl4_6 | ~spl4_4),
% 1.24/0.53    inference(avatar_split_clause,[],[f79,f72,f87])).
% 1.24/0.53  fof(f79,plain,(
% 1.24/0.53    v1_relat_1(sK3) | ~spl4_4),
% 1.24/0.53    inference(resolution,[],[f74,f50])).
% 1.24/0.53  fof(f50,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f27])).
% 1.24/0.53  fof(f27,plain,(
% 1.24/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.53    inference(ennf_transformation,[],[f12])).
% 1.24/0.53  fof(f12,axiom,(
% 1.24/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.24/0.53  fof(f85,plain,(
% 1.24/0.53    ~spl4_5 | ~spl4_4),
% 1.24/0.53    inference(avatar_split_clause,[],[f80,f72,f82])).
% 1.24/0.53  fof(f80,plain,(
% 1.24/0.53    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | ~spl4_4),
% 1.24/0.53    inference(backward_demodulation,[],[f34,f76])).
% 1.24/0.53  fof(f76,plain,(
% 1.24/0.53    ( ! [X0] : (k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl4_4),
% 1.24/0.53    inference(resolution,[],[f74,f53])).
% 1.24/0.53  fof(f53,plain,(
% 1.24/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f29])).
% 1.24/0.53  fof(f29,plain,(
% 1.24/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.53    inference(ennf_transformation,[],[f14])).
% 1.24/0.53  fof(f14,axiom,(
% 1.24/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.24/0.53  fof(f34,plain,(
% 1.24/0.53    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.24/0.53    inference(cnf_transformation,[],[f18])).
% 1.24/0.53  fof(f18,plain,(
% 1.24/0.53    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 1.24/0.53    inference(flattening,[],[f17])).
% 1.24/0.53  fof(f17,plain,(
% 1.24/0.53    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 1.24/0.53    inference(ennf_transformation,[],[f16])).
% 1.24/0.53  fof(f16,negated_conjecture,(
% 1.24/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.24/0.53    inference(negated_conjecture,[],[f15])).
% 1.24/0.53  fof(f15,conjecture,(
% 1.24/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.24/0.53  fof(f75,plain,(
% 1.24/0.53    spl4_4),
% 1.24/0.53    inference(avatar_split_clause,[],[f32,f72])).
% 1.24/0.53  fof(f32,plain,(
% 1.24/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.24/0.53    inference(cnf_transformation,[],[f18])).
% 1.24/0.53  fof(f60,plain,(
% 1.24/0.53    spl4_1),
% 1.24/0.53    inference(avatar_split_clause,[],[f30,f57])).
% 1.24/0.53  fof(f30,plain,(
% 1.24/0.53    v1_funct_1(sK3)),
% 1.24/0.53    inference(cnf_transformation,[],[f18])).
% 1.24/0.53  % SZS output end Proof for theBenchmark
% 1.24/0.53  % (2222)------------------------------
% 1.24/0.53  % (2222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (2222)Termination reason: Refutation
% 1.24/0.53  
% 1.24/0.53  % (2222)Memory used [KB]: 10874
% 1.24/0.53  % (2222)Time elapsed: 0.123 s
% 1.24/0.53  % (2222)------------------------------
% 1.24/0.53  % (2222)------------------------------
% 1.24/0.53  % (2205)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.37/0.53  % (2194)Success in time 0.173 s
%------------------------------------------------------------------------------
