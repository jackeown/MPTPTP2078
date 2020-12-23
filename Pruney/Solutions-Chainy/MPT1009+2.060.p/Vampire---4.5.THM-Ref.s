%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 163 expanded)
%              Number of leaves         :   23 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :  278 ( 456 expanded)
%              Number of equality atoms :   86 ( 143 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f531,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f84,f89,f127,f128,f145,f175,f189,f274,f387,f388,f530])).

fof(f530,plain,
    ( ~ spl4_10
    | spl4_14 ),
    inference(avatar_contradiction_clause,[],[f529])).

fof(f529,plain,
    ( $false
    | ~ spl4_10
    | spl4_14 ),
    inference(subsumption_resolution,[],[f528,f69])).

fof(f69,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f528,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_tarski(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl4_10
    | spl4_14 ),
    inference(forward_demodulation,[],[f527,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f527,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_tarski(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl4_10
    | spl4_14 ),
    inference(forward_demodulation,[],[f188,f144])).

fof(f144,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_10
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f188,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl4_14
  <=> r1_tarski(k9_relat_1(sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f388,plain,
    ( spl4_9
    | spl4_17
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f211,f172,f219,f138])).

% (14177)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f138,plain,
    ( spl4_9
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f219,plain,
    ( spl4_17
  <=> k2_tarski(sK0,sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f172,plain,
    ( spl4_13
  <=> r1_tarski(k1_relat_1(sK3),k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f211,plain,
    ( k2_tarski(sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_13 ),
    inference(duplicate_literal_removal,[],[f205])).

fof(f205,plain,
    ( k2_tarski(sK0,sK0) = k1_relat_1(sK3)
    | k2_tarski(sK0,sK0) = k1_relat_1(sK3)
    | k2_tarski(sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f174,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f54,f43,f43])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f174,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_tarski(sK0,sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f172])).

fof(f387,plain,
    ( ~ spl4_5
    | spl4_14
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | ~ spl4_5
    | spl4_14
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f367,f130])).

fof(f130,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f93,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f93,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f367,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | spl4_14
    | ~ spl4_22 ),
    inference(backward_demodulation,[],[f188,f273])).

fof(f273,plain,
    ( k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl4_22
  <=> k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f274,plain,
    ( spl4_22
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f234,f219,f92,f86,f271])).

fof(f86,plain,
    ( spl4_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f234,plain,
    ( k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f93,f88,f221,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k2_tarski(k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | k2_tarski(X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f49,f43,f43])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f221,plain,
    ( k2_tarski(sK0,sK0) = k1_relat_1(sK3)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f219])).

fof(f88,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f189,plain,
    ( ~ spl4_14
    | spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f181,f81,f71,f186])).

fof(f71,plain,
    ( spl4_1
  <=> r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f81,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f181,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | spl4_1
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f73,f105])).

fof(f105,plain,
    ( ! [X0] : k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f83,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f83,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f73,plain,
    ( ~ r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f175,plain,
    ( spl4_13
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f166,f123,f92,f172])).

fof(f123,plain,
    ( spl4_8
  <=> v4_relat_1(sK3,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f166,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_tarski(sK0,sK0))
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f93,f125,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f125,plain,
    ( v4_relat_1(sK3,k2_tarski(sK0,sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f145,plain,
    ( ~ spl4_9
    | spl4_10
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f135,f92,f142,f138])).

fof(f135,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 != k1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(resolution,[],[f93,f44])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f128,plain,
    ( spl4_5
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f111,f81,f92])).

fof(f111,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f83,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f127,plain,
    ( spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f110,f81,f123])).

fof(f110,plain,
    ( v4_relat_1(sK3,k2_tarski(sK0,sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f83,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f89,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f37,f86])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f84,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f61,f81])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f38,f43])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f60,f71])).

fof(f60,plain,(
    ~ r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f40,f43,f43])).

fof(f40,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:59:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (14184)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (14175)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (14158)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (14175)Refutation not found, incomplete strategy% (14175)------------------------------
% 0.22/0.54  % (14175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14175)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (14175)Memory used [KB]: 10618
% 0.22/0.54  % (14175)Time elapsed: 0.114 s
% 0.22/0.54  % (14175)------------------------------
% 0.22/0.54  % (14175)------------------------------
% 0.22/0.54  % (14159)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (14186)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (14167)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (14173)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (14157)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (14161)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (14157)Refutation not found, incomplete strategy% (14157)------------------------------
% 0.22/0.54  % (14157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14157)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (14157)Memory used [KB]: 1791
% 0.22/0.54  % (14157)Time elapsed: 0.118 s
% 0.22/0.54  % (14157)------------------------------
% 0.22/0.54  % (14157)------------------------------
% 0.22/0.54  % (14167)Refutation not found, incomplete strategy% (14167)------------------------------
% 0.22/0.54  % (14167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14167)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (14167)Memory used [KB]: 10746
% 0.22/0.54  % (14167)Time elapsed: 0.127 s
% 0.22/0.54  % (14167)------------------------------
% 0.22/0.54  % (14167)------------------------------
% 0.22/0.54  % (14182)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (14187)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (14163)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (14188)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (14184)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % (14162)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (14164)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f531,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f74,f84,f89,f127,f128,f145,f175,f189,f274,f387,f388,f530])).
% 0.22/0.55  fof(f530,plain,(
% 0.22/0.55    ~spl4_10 | spl4_14),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f529])).
% 0.22/0.55  fof(f529,plain,(
% 0.22/0.55    $false | (~spl4_10 | spl4_14)),
% 0.22/0.55    inference(subsumption_resolution,[],[f528,f69])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X2))) )),
% 0.22/0.55    inference(equality_resolution,[],[f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.22/0.55    inference(flattening,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.22/0.55    inference(nnf_transformation,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.22/0.55  fof(f528,plain,(
% 0.22/0.55    ~r1_tarski(k1_xboole_0,k2_tarski(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) | (~spl4_10 | spl4_14)),
% 0.22/0.55    inference(forward_demodulation,[],[f527,f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.22/0.55  fof(f527,plain,(
% 0.22/0.55    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_tarski(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) | (~spl4_10 | spl4_14)),
% 0.22/0.55    inference(forward_demodulation,[],[f188,f144])).
% 0.22/0.55  fof(f144,plain,(
% 0.22/0.55    k1_xboole_0 = sK3 | ~spl4_10),
% 0.22/0.55    inference(avatar_component_clause,[],[f142])).
% 0.22/0.55  fof(f142,plain,(
% 0.22/0.55    spl4_10 <=> k1_xboole_0 = sK3),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.55  fof(f188,plain,(
% 0.22/0.55    ~r1_tarski(k9_relat_1(sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | spl4_14),
% 0.22/0.55    inference(avatar_component_clause,[],[f186])).
% 0.22/0.55  fof(f186,plain,(
% 0.22/0.55    spl4_14 <=> r1_tarski(k9_relat_1(sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.55  fof(f388,plain,(
% 0.22/0.55    spl4_9 | spl4_17 | ~spl4_13),
% 0.22/0.55    inference(avatar_split_clause,[],[f211,f172,f219,f138])).
% 0.22/0.55  % (14177)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  fof(f138,plain,(
% 0.22/0.55    spl4_9 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.55  fof(f219,plain,(
% 0.22/0.55    spl4_17 <=> k2_tarski(sK0,sK0) = k1_relat_1(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.55  fof(f172,plain,(
% 0.22/0.55    spl4_13 <=> r1_tarski(k1_relat_1(sK3),k2_tarski(sK0,sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.55  fof(f211,plain,(
% 0.22/0.55    k2_tarski(sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3) | ~spl4_13),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f205])).
% 0.22/0.55  fof(f205,plain,(
% 0.22/0.55    k2_tarski(sK0,sK0) = k1_relat_1(sK3) | k2_tarski(sK0,sK0) = k1_relat_1(sK3) | k2_tarski(sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3) | ~spl4_13),
% 0.22/0.55    inference(resolution,[],[f174,f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k2_tarski(X2,X2) = X0 | k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f54,f43,f43])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f174,plain,(
% 0.22/0.55    r1_tarski(k1_relat_1(sK3),k2_tarski(sK0,sK0)) | ~spl4_13),
% 0.22/0.55    inference(avatar_component_clause,[],[f172])).
% 0.22/0.55  fof(f387,plain,(
% 0.22/0.55    ~spl4_5 | spl4_14 | ~spl4_22),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f386])).
% 0.22/0.55  fof(f386,plain,(
% 0.22/0.55    $false | (~spl4_5 | spl4_14 | ~spl4_22)),
% 0.22/0.55    inference(subsumption_resolution,[],[f367,f130])).
% 0.22/0.55  fof(f130,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))) ) | ~spl4_5),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f93,f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    v1_relat_1(sK3) | ~spl4_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f92])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    spl4_5 <=> v1_relat_1(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.55  fof(f367,plain,(
% 0.22/0.55    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | (spl4_14 | ~spl4_22)),
% 0.22/0.55    inference(backward_demodulation,[],[f188,f273])).
% 0.22/0.55  fof(f273,plain,(
% 0.22/0.55    k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_22),
% 0.22/0.55    inference(avatar_component_clause,[],[f271])).
% 0.22/0.55  fof(f271,plain,(
% 0.22/0.55    spl4_22 <=> k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.55  fof(f274,plain,(
% 0.22/0.55    spl4_22 | ~spl4_4 | ~spl4_5 | ~spl4_17),
% 0.22/0.55    inference(avatar_split_clause,[],[f234,f219,f92,f86,f271])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    spl4_4 <=> v1_funct_1(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.55  fof(f234,plain,(
% 0.22/0.55    k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | (~spl4_4 | ~spl4_5 | ~spl4_17)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f93,f88,f221,f62])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_relat_1(X1) = k2_tarski(k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | k2_tarski(X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f49,f43,f43])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.22/0.55  fof(f221,plain,(
% 0.22/0.55    k2_tarski(sK0,sK0) = k1_relat_1(sK3) | ~spl4_17),
% 0.22/0.55    inference(avatar_component_clause,[],[f219])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    v1_funct_1(sK3) | ~spl4_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f86])).
% 0.22/0.55  fof(f189,plain,(
% 0.22/0.55    ~spl4_14 | spl4_1 | ~spl4_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f181,f81,f71,f186])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    spl4_1 <=> r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.55  fof(f181,plain,(
% 0.22/0.55    ~r1_tarski(k9_relat_1(sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | (spl4_1 | ~spl4_3)),
% 0.22/0.55    inference(backward_demodulation,[],[f73,f105])).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    ( ! [X0] : (k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl4_3),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f83,f59])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1))) | ~spl4_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f81])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ~r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | spl4_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f71])).
% 0.22/0.55  fof(f175,plain,(
% 0.22/0.55    spl4_13 | ~spl4_5 | ~spl4_8),
% 0.22/0.55    inference(avatar_split_clause,[],[f166,f123,f92,f172])).
% 0.22/0.55  fof(f123,plain,(
% 0.22/0.55    spl4_8 <=> v4_relat_1(sK3,k2_tarski(sK0,sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.55  fof(f166,plain,(
% 0.22/0.55    r1_tarski(k1_relat_1(sK3),k2_tarski(sK0,sK0)) | (~spl4_5 | ~spl4_8)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f93,f125,f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.55  fof(f125,plain,(
% 0.22/0.55    v4_relat_1(sK3,k2_tarski(sK0,sK0)) | ~spl4_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f123])).
% 0.22/0.55  fof(f145,plain,(
% 0.22/0.55    ~spl4_9 | spl4_10 | ~spl4_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f135,f92,f142,f138])).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    k1_xboole_0 = sK3 | k1_xboole_0 != k1_relat_1(sK3) | ~spl4_5),
% 0.22/0.55    inference(resolution,[],[f93,f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    spl4_5 | ~spl4_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f111,f81,f92])).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    v1_relat_1(sK3) | ~spl4_3),
% 0.22/0.55    inference(resolution,[],[f83,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    spl4_8 | ~spl4_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f110,f81,f123])).
% 0.22/0.55  fof(f110,plain,(
% 0.22/0.55    v4_relat_1(sK3,k2_tarski(sK0,sK0)) | ~spl4_3),
% 0.22/0.55    inference(resolution,[],[f83,f53])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.55    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.55  fof(f89,plain,(
% 0.22/0.55    spl4_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f37,f86])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    v1_funct_1(sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 0.22/0.55    inference(flattening,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 0.22/0.55    inference(ennf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.22/0.55    inference(pure_predicate_removal,[],[f15])).
% 0.22/0.55  fof(f15,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.22/0.55    inference(negated_conjecture,[],[f14])).
% 0.22/0.55  fof(f14,conjecture,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    spl4_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f61,f81])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1)))),
% 0.22/0.55    inference(definition_unfolding,[],[f38,f43])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    ~spl4_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f60,f71])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ~r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.22/0.55    inference(definition_unfolding,[],[f40,f43,f43])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (14184)------------------------------
% 0.22/0.55  % (14184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (14184)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (14184)Memory used [KB]: 6524
% 0.22/0.55  % (14184)Time elapsed: 0.136 s
% 0.22/0.55  % (14184)------------------------------
% 0.22/0.55  % (14184)------------------------------
% 0.22/0.55  % (14180)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (14174)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (14156)Success in time 0.184 s
%------------------------------------------------------------------------------
