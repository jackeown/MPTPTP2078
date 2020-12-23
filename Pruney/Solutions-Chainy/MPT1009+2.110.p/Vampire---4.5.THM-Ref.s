%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:42 EST 2020

% Result     : Theorem 2.58s
% Output     : Refutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 396 expanded)
%              Number of leaves         :   44 ( 137 expanded)
%              Depth                    :   15
%              Number of atoms          :  686 (1180 expanded)
%              Number of equality atoms :  158 ( 262 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3671,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f125,f130,f136,f156,f376,f483,f893,f943,f983,f1072,f1086,f1139,f1172,f1179,f1183,f1370,f1530,f3627,f3665,f3669,f3670])).

fof(f3670,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k1_relat_1(sK3)
    | r1_tarski(k9_relat_1(sK3,sK2),k1_relat_1(k1_xboole_0))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3669,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK3
    | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(k1_xboole_0))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k1_relat_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3665,plain,
    ( ~ spl5_7
    | spl5_98 ),
    inference(avatar_contradiction_clause,[],[f3664])).

fof(f3664,plain,
    ( $false
    | ~ spl5_7
    | spl5_98 ),
    inference(subsumption_resolution,[],[f3654,f155])).

fof(f155,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl5_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f3654,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_98 ),
    inference(resolution,[],[f3626,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f3626,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | spl5_98 ),
    inference(avatar_component_clause,[],[f3624])).

fof(f3624,plain,
    ( spl5_98
  <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f3627,plain,
    ( ~ spl5_98
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_10
    | spl5_12
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f3611,f886,f226,f184,f153,f127,f3624])).

fof(f127,plain,
    ( spl5_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f184,plain,
    ( spl5_10
  <=> v4_relat_1(sK3,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f226,plain,
    ( spl5_12
  <=> r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f886,plain,
    ( spl5_31
  <=> r2_hidden(sK0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f3611,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_10
    | spl5_12
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f3610,f129])).

fof(f129,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f3610,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl5_7
    | ~ spl5_10
    | spl5_12
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f3609,f888])).

fof(f888,plain,
    ( r2_hidden(sK0,k1_relat_1(sK3))
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f886])).

fof(f3609,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl5_7
    | ~ spl5_10
    | spl5_12 ),
    inference(subsumption_resolution,[],[f3608,f186])).

fof(f186,plain,
    ( v4_relat_1(sK3,k1_tarski(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f184])).

fof(f3608,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v4_relat_1(sK3,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl5_7
    | spl5_12 ),
    inference(subsumption_resolution,[],[f3540,f155])).

fof(f3540,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v4_relat_1(sK3,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl5_12 ),
    inference(superposition,[],[f228,f458])).

fof(f458,plain,(
    ! [X8,X9] :
      ( k1_tarski(k1_funct_1(X8,X9)) = k2_relat_1(X8)
      | ~ v1_relat_1(X8)
      | ~ v4_relat_1(X8,k1_tarski(X9))
      | ~ r2_hidden(X9,k1_relat_1(X8))
      | ~ v1_funct_1(X8) ) ),
    inference(duplicate_literal_removal,[],[f453])).

fof(f453,plain,(
    ! [X8,X9] :
      ( k1_tarski(k1_funct_1(X8,X9)) = k2_relat_1(X8)
      | ~ v1_relat_1(X8)
      | ~ v4_relat_1(X8,k1_tarski(X9))
      | ~ r2_hidden(X9,k1_relat_1(X8))
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8) ) ),
    inference(superposition,[],[f206,f249])).

fof(f249,plain,(
    ! [X4,X3] :
      ( k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k1_tarski(X4))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(forward_demodulation,[],[f248,f87])).

fof(f87,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f248,plain,(
    ! [X4,X3] :
      ( k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,(
    ! [X4,X3] :
      ( k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f76,f87])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

fof(f206,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f97,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f97,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f228,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f226])).

fof(f1530,plain,
    ( ~ spl5_34
    | ~ spl5_7
    | spl5_28 ),
    inference(avatar_split_clause,[],[f1529,f828,f153,f980])).

fof(f980,plain,
    ( spl5_34
  <=> v5_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f828,plain,
    ( spl5_28
  <=> r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f1529,plain,
    ( ~ v5_relat_1(sK3,k1_xboole_0)
    | ~ spl5_7
    | spl5_28 ),
    inference(subsumption_resolution,[],[f1522,f155])).

fof(f1522,plain,
    ( ~ v5_relat_1(sK3,k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | spl5_28 ),
    inference(resolution,[],[f830,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f830,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | spl5_28 ),
    inference(avatar_component_clause,[],[f828])).

fof(f1370,plain,
    ( spl5_53
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f1369,f828,f1363])).

fof(f1363,plain,
    ( spl5_53
  <=> k1_xboole_0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f1369,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f1358,f141])).

fof(f141,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f63,f88])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1358,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK3))
    | ~ spl5_28 ),
    inference(resolution,[],[f829,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f829,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f828])).

fof(f1183,plain,
    ( ~ spl5_12
    | spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1182,f122,f112,f226])).

fof(f112,plain,
    ( spl5_1
  <=> r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f122,plain,
    ( spl5_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1182,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f1181,f124])).

fof(f124,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f1181,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | spl5_1 ),
    inference(superposition,[],[f114,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f114,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f1179,plain,
    ( spl5_10
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1174,f122,f184])).

fof(f1174,plain,
    ( v4_relat_1(sK3,k1_tarski(sK0))
    | ~ spl5_3 ),
    inference(resolution,[],[f124,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1172,plain,
    ( ~ spl5_5
    | spl5_12
    | ~ spl5_20
    | ~ spl5_41 ),
    inference(avatar_contradiction_clause,[],[f1171])).

fof(f1171,plain,
    ( $false
    | ~ spl5_5
    | spl5_12
    | ~ spl5_20
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f1170,f141])).

fof(f1170,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl5_5
    | spl5_12
    | ~ spl5_20
    | ~ spl5_41 ),
    inference(forward_demodulation,[],[f1155,f533])).

fof(f533,plain,
    ( ! [X3] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X3)
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f532,f135])).

fof(f135,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f532,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k9_relat_1(k1_xboole_0,X3)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f525,f141])).

fof(f525,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,X3))
        | k1_xboole_0 = k9_relat_1(k1_xboole_0,X3)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl5_20 ),
    inference(superposition,[],[f159,f482])).

fof(f482,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl5_20
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f159,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_relat_1(X2),k9_relat_1(X2,X3))
      | k9_relat_1(X2,X3) = k2_relat_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f70,f75])).

fof(f1155,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | spl5_12
    | ~ spl5_41 ),
    inference(backward_demodulation,[],[f228,f1084])).

fof(f1084,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f1082])).

fof(f1082,plain,
    ( spl5_41
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f1139,plain,
    ( spl5_34
    | ~ spl5_40 ),
    inference(avatar_contradiction_clause,[],[f1136])).

fof(f1136,plain,
    ( $false
    | spl5_34
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f982,f1074])).

fof(f1074,plain,
    ( ! [X0] : v5_relat_1(sK3,X0)
    | ~ spl5_40 ),
    inference(resolution,[],[f1071,f260])).

fof(f260,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | v5_relat_1(X1,X2) ) ),
    inference(resolution,[],[f192,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f192,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | v5_relat_1(X3,X2) ) ),
    inference(superposition,[],[f91,f110])).

fof(f110,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1071,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f1069])).

fof(f1069,plain,
    ( spl5_40
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f982,plain,
    ( ~ v5_relat_1(sK3,k1_xboole_0)
    | spl5_34 ),
    inference(avatar_component_clause,[],[f980])).

fof(f1086,plain,
    ( spl5_41
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f1076,f1069,f1082])).

fof(f1076,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_40 ),
    inference(resolution,[],[f1071,f158])).

fof(f158,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f70,f141])).

fof(f1072,plain,
    ( spl5_40
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f1067,f890,f153,f127,f1069])).

fof(f890,plain,
    ( spl5_32
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f1067,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f1066,f110])).

fof(f1066,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)))
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f1065,f129])).

fof(f1065,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ spl5_7
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f1062,f155])).

fof(f1062,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl5_32 ),
    inference(superposition,[],[f221,f892])).

fof(f892,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f890])).

fof(f221,plain,(
    ! [X5] :
      ( r1_tarski(X5,k2_zfmisc_1(k1_relat_1(X5),k2_relat_1(X5)))
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f93,f63])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f983,plain,
    ( ~ spl5_13
    | ~ spl5_34
    | ~ spl5_7
    | spl5_18 ),
    inference(avatar_split_clause,[],[f978,f443,f153,f980,f294])).

fof(f294,plain,
    ( spl5_13
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f443,plain,
    ( spl5_18
  <=> r1_tarski(k9_relat_1(sK3,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f978,plain,
    ( ~ v5_relat_1(sK3,k1_xboole_0)
    | ~ v4_relat_1(sK3,sK2)
    | ~ spl5_7
    | spl5_18 ),
    inference(subsumption_resolution,[],[f838,f155])).

fof(f838,plain,
    ( ~ v5_relat_1(sK3,k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | ~ v4_relat_1(sK3,sK2)
    | spl5_18 ),
    inference(resolution,[],[f430,f445])).

fof(f445,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_xboole_0)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f443])).

fof(f430,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),X2)
      | ~ v5_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f429])).

fof(f429,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X0,X2)
      | r1_tarski(k9_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f204,f96])).

fof(f204,plain,(
    ! [X6,X7,X5] :
      ( ~ v5_relat_1(k7_relat_1(X5,X6),X7)
      | r1_tarski(k9_relat_1(X5,X6),X7)
      | ~ v1_relat_1(k7_relat_1(X5,X6))
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f73,f97])).

fof(f943,plain,
    ( ~ spl5_7
    | spl5_13
    | ~ spl5_32 ),
    inference(avatar_contradiction_clause,[],[f940])).

fof(f940,plain,
    ( $false
    | ~ spl5_7
    | spl5_13
    | ~ spl5_32 ),
    inference(unit_resulting_resolution,[],[f296,f927])).

fof(f927,plain,
    ( ! [X0] : v4_relat_1(sK3,X0)
    | ~ spl5_7
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f926,f155])).

fof(f926,plain,
    ( ! [X0] :
        ( v4_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f924,f141])).

fof(f924,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v4_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_32 ),
    inference(superposition,[],[f72,f892])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f296,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f294])).

fof(f893,plain,
    ( spl5_31
    | spl5_32
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f884,f184,f153,f890,f886])).

fof(f884,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | r2_hidden(sK0,k1_relat_1(sK3))
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f880,f155])).

fof(f880,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl5_10 ),
    inference(resolution,[],[f354,f186])).

fof(f354,plain,(
    ! [X21,X20] :
      ( ~ v4_relat_1(X21,k1_tarski(X20))
      | k1_xboole_0 = k1_relat_1(X21)
      | r2_hidden(X20,k1_relat_1(X21))
      | ~ v1_relat_1(X21) ) ),
    inference(superposition,[],[f138,f209])).

fof(f209,plain,(
    ! [X2,X3] :
      ( k1_relat_1(X2) = k1_tarski(X3)
      | k1_xboole_0 = k1_relat_1(X2)
      | ~ v4_relat_1(X2,k1_tarski(X3))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f65,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f138,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f107,f87])).

fof(f107,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f54,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f483,plain,
    ( ~ spl5_19
    | spl5_20
    | ~ spl5_5
    | spl5_12 ),
    inference(avatar_split_clause,[],[f474,f226,f133,f480,f476])).

fof(f476,plain,
    ( spl5_19
  <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f474,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(k1_xboole_0))
    | ~ spl5_5
    | spl5_12 ),
    inference(subsumption_resolution,[],[f470,f135])).

fof(f470,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | spl5_12 ),
    inference(resolution,[],[f393,f189])).

fof(f189,plain,(
    ! [X0] : v5_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f91,f88])).

fof(f393,plain,
    ( ! [X9] :
        ( ~ v5_relat_1(X9,k1_tarski(k1_funct_1(sK3,sK0)))
        | k1_xboole_0 = k2_relat_1(X9)
        | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(X9))
        | ~ v1_relat_1(X9) )
    | spl5_12 ),
    inference(superposition,[],[f228,f210])).

fof(f210,plain,(
    ! [X4,X5] :
      ( k2_relat_1(X4) = k1_tarski(X5)
      | k1_xboole_0 = k2_relat_1(X4)
      | ~ v5_relat_1(X4,k1_tarski(X5))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f65,f73])).

fof(f376,plain,
    ( ~ spl5_15
    | spl5_16
    | ~ spl5_5
    | spl5_12 ),
    inference(avatar_split_clause,[],[f367,f226,f133,f373,f369])).

fof(f369,plain,
    ( spl5_15
  <=> r1_tarski(k9_relat_1(sK3,sK2),k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f373,plain,
    ( spl5_16
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f367,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k1_relat_1(k1_xboole_0))
    | ~ spl5_5
    | spl5_12 ),
    inference(subsumption_resolution,[],[f364,f135])).

fof(f364,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | spl5_12 ),
    inference(resolution,[],[f348,f179])).

fof(f179,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f90,f88])).

fof(f348,plain,
    ( ! [X7] :
        ( ~ v4_relat_1(X7,k1_tarski(k1_funct_1(sK3,sK0)))
        | k1_xboole_0 = k1_relat_1(X7)
        | ~ r1_tarski(k9_relat_1(sK3,sK2),k1_relat_1(X7))
        | ~ v1_relat_1(X7) )
    | spl5_12 ),
    inference(superposition,[],[f228,f209])).

fof(f156,plain,
    ( spl5_7
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f151,f122,f153])).

fof(f151,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f148,f95])).

fof(f95,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f148,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski(sK0),sK1))
    | ~ spl5_3 ),
    inference(resolution,[],[f94,f124])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f136,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f131,f133])).

fof(f131,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f95,f109])).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f130,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f59,f127])).

fof(f59,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f43])).

fof(f43,plain,
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

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f125,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f60,f122])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f115,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f62,f112])).

fof(f62,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (18828)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.48  % (18851)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.48  % (18843)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.49  % (18835)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.49  % (18831)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (18839)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.50  % (18836)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.50  % (18852)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.50  % (18825)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.50  % (18827)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.21/0.51  % (18844)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.21/0.51  % (18829)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.21/0.51  % (18826)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.21/0.51  % (18847)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.21/0.51  % (18826)Refutation not found, incomplete strategy% (18826)------------------------------
% 1.21/0.51  % (18826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.51  % (18826)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.51  
% 1.21/0.51  % (18826)Memory used [KB]: 1791
% 1.21/0.51  % (18826)Time elapsed: 0.116 s
% 1.21/0.51  % (18826)------------------------------
% 1.21/0.51  % (18826)------------------------------
% 1.21/0.52  % (18846)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.21/0.52  % (18854)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.21/0.52  % (18852)Refutation not found, incomplete strategy% (18852)------------------------------
% 1.21/0.52  % (18852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (18838)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.21/0.53  % (18849)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.38/0.53  % (18854)Refutation not found, incomplete strategy% (18854)------------------------------
% 1.38/0.53  % (18854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (18854)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (18854)Memory used [KB]: 1791
% 1.38/0.53  % (18854)Time elapsed: 0.093 s
% 1.38/0.53  % (18854)------------------------------
% 1.38/0.53  % (18854)------------------------------
% 1.38/0.53  % (18852)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (18852)Memory used [KB]: 6268
% 1.38/0.53  % (18852)Time elapsed: 0.123 s
% 1.38/0.53  % (18852)------------------------------
% 1.38/0.53  % (18852)------------------------------
% 1.38/0.53  % (18853)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.38/0.53  % (18830)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.38/0.53  % (18841)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.38/0.53  % (18841)Refutation not found, incomplete strategy% (18841)------------------------------
% 1.38/0.53  % (18841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (18841)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (18841)Memory used [KB]: 10746
% 1.38/0.53  % (18841)Time elapsed: 0.141 s
% 1.38/0.53  % (18841)------------------------------
% 1.38/0.53  % (18841)------------------------------
% 1.38/0.53  % (18850)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.38/0.53  % (18848)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.38/0.54  % (18833)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.38/0.54  % (18845)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.38/0.54  % (18842)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.38/0.54  % (18840)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.38/0.55  % (18834)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.38/0.55  % (18832)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.38/0.55  % (18837)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.38/0.62  % (18828)Refutation not found, incomplete strategy% (18828)------------------------------
% 1.38/0.62  % (18828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.62  % (18828)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.62  
% 1.38/0.62  % (18828)Memory used [KB]: 6268
% 1.38/0.62  % (18828)Time elapsed: 0.236 s
% 1.38/0.62  % (18828)------------------------------
% 1.38/0.62  % (18828)------------------------------
% 2.03/0.67  % (18856)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.03/0.67  % (18855)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.03/0.67  % (18857)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.03/0.67  % (18858)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.03/0.67  % (18857)Refutation not found, incomplete strategy% (18857)------------------------------
% 2.03/0.67  % (18857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.67  % (18857)Termination reason: Refutation not found, incomplete strategy
% 2.03/0.67  
% 2.03/0.67  % (18857)Memory used [KB]: 6268
% 2.03/0.67  % (18857)Time elapsed: 0.115 s
% 2.03/0.67  % (18857)------------------------------
% 2.03/0.67  % (18857)------------------------------
% 2.58/0.74  % (18859)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.58/0.74  % (18846)Refutation found. Thanks to Tanya!
% 2.58/0.74  % SZS status Theorem for theBenchmark
% 2.58/0.74  % SZS output start Proof for theBenchmark
% 2.58/0.74  fof(f3671,plain,(
% 2.58/0.74    $false),
% 2.58/0.74    inference(avatar_sat_refutation,[],[f115,f125,f130,f136,f156,f376,f483,f893,f943,f983,f1072,f1086,f1139,f1172,f1179,f1183,f1370,f1530,f3627,f3665,f3669,f3670])).
% 2.58/0.74  fof(f3670,plain,(
% 2.58/0.74    k1_xboole_0 != sK3 | k1_xboole_0 != k1_relat_1(sK3) | r1_tarski(k9_relat_1(sK3,sK2),k1_relat_1(k1_xboole_0)) | ~r1_tarski(k9_relat_1(sK3,sK2),k1_xboole_0)),
% 2.58/0.74    introduced(theory_tautology_sat_conflict,[])).
% 2.58/0.74  fof(f3669,plain,(
% 2.58/0.74    k1_xboole_0 != k2_relat_1(sK3) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != sK3 | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(k1_xboole_0)) | ~r1_tarski(k9_relat_1(sK3,sK2),k1_relat_1(k1_xboole_0))),
% 2.58/0.74    introduced(theory_tautology_sat_conflict,[])).
% 2.58/0.74  fof(f3665,plain,(
% 2.58/0.74    ~spl5_7 | spl5_98),
% 2.58/0.74    inference(avatar_contradiction_clause,[],[f3664])).
% 2.58/0.74  fof(f3664,plain,(
% 2.58/0.74    $false | (~spl5_7 | spl5_98)),
% 2.58/0.74    inference(subsumption_resolution,[],[f3654,f155])).
% 2.58/0.74  fof(f155,plain,(
% 2.58/0.74    v1_relat_1(sK3) | ~spl5_7),
% 2.58/0.74    inference(avatar_component_clause,[],[f153])).
% 2.58/0.74  fof(f153,plain,(
% 2.58/0.74    spl5_7 <=> v1_relat_1(sK3)),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.58/0.74  fof(f3654,plain,(
% 2.58/0.74    ~v1_relat_1(sK3) | spl5_98),
% 2.58/0.74    inference(resolution,[],[f3626,f75])).
% 2.58/0.74  fof(f75,plain,(
% 2.58/0.74    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.58/0.74    inference(cnf_transformation,[],[f30])).
% 2.58/0.74  fof(f30,plain,(
% 2.58/0.74    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.58/0.74    inference(ennf_transformation,[],[f15])).
% 2.58/0.74  fof(f15,axiom,(
% 2.58/0.74    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 2.58/0.74  fof(f3626,plain,(
% 2.58/0.74    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | spl5_98),
% 2.58/0.74    inference(avatar_component_clause,[],[f3624])).
% 2.58/0.74  fof(f3624,plain,(
% 2.58/0.74    spl5_98 <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).
% 2.58/0.74  fof(f3627,plain,(
% 2.58/0.74    ~spl5_98 | ~spl5_4 | ~spl5_7 | ~spl5_10 | spl5_12 | ~spl5_31),
% 2.58/0.74    inference(avatar_split_clause,[],[f3611,f886,f226,f184,f153,f127,f3624])).
% 2.58/0.74  fof(f127,plain,(
% 2.58/0.74    spl5_4 <=> v1_funct_1(sK3)),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.58/0.74  fof(f184,plain,(
% 2.58/0.74    spl5_10 <=> v4_relat_1(sK3,k1_tarski(sK0))),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.58/0.74  fof(f226,plain,(
% 2.58/0.74    spl5_12 <=> r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.58/0.74  fof(f886,plain,(
% 2.58/0.74    spl5_31 <=> r2_hidden(sK0,k1_relat_1(sK3))),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 2.58/0.74  fof(f3611,plain,(
% 2.58/0.74    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | (~spl5_4 | ~spl5_7 | ~spl5_10 | spl5_12 | ~spl5_31)),
% 2.58/0.74    inference(subsumption_resolution,[],[f3610,f129])).
% 2.58/0.74  fof(f129,plain,(
% 2.58/0.74    v1_funct_1(sK3) | ~spl5_4),
% 2.58/0.74    inference(avatar_component_clause,[],[f127])).
% 2.58/0.74  fof(f3610,plain,(
% 2.58/0.74    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~v1_funct_1(sK3) | (~spl5_7 | ~spl5_10 | spl5_12 | ~spl5_31)),
% 2.58/0.74    inference(subsumption_resolution,[],[f3609,f888])).
% 2.58/0.74  fof(f888,plain,(
% 2.58/0.74    r2_hidden(sK0,k1_relat_1(sK3)) | ~spl5_31),
% 2.58/0.74    inference(avatar_component_clause,[],[f886])).
% 2.58/0.74  fof(f3609,plain,(
% 2.58/0.74    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | (~spl5_7 | ~spl5_10 | spl5_12)),
% 2.58/0.74    inference(subsumption_resolution,[],[f3608,f186])).
% 2.58/0.74  fof(f186,plain,(
% 2.58/0.74    v4_relat_1(sK3,k1_tarski(sK0)) | ~spl5_10),
% 2.58/0.74    inference(avatar_component_clause,[],[f184])).
% 2.58/0.74  fof(f3608,plain,(
% 2.58/0.74    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~v4_relat_1(sK3,k1_tarski(sK0)) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | (~spl5_7 | spl5_12)),
% 2.58/0.74    inference(subsumption_resolution,[],[f3540,f155])).
% 2.58/0.74  fof(f3540,plain,(
% 2.58/0.74    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v4_relat_1(sK3,k1_tarski(sK0)) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | spl5_12),
% 2.58/0.74    inference(superposition,[],[f228,f458])).
% 2.58/0.74  fof(f458,plain,(
% 2.58/0.74    ( ! [X8,X9] : (k1_tarski(k1_funct_1(X8,X9)) = k2_relat_1(X8) | ~v1_relat_1(X8) | ~v4_relat_1(X8,k1_tarski(X9)) | ~r2_hidden(X9,k1_relat_1(X8)) | ~v1_funct_1(X8)) )),
% 2.58/0.74    inference(duplicate_literal_removal,[],[f453])).
% 2.58/0.74  fof(f453,plain,(
% 2.58/0.74    ( ! [X8,X9] : (k1_tarski(k1_funct_1(X8,X9)) = k2_relat_1(X8) | ~v1_relat_1(X8) | ~v4_relat_1(X8,k1_tarski(X9)) | ~r2_hidden(X9,k1_relat_1(X8)) | ~v1_funct_1(X8) | ~v1_relat_1(X8)) )),
% 2.58/0.74    inference(superposition,[],[f206,f249])).
% 2.58/0.74  fof(f249,plain,(
% 2.58/0.74    ( ! [X4,X3] : (k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k1_tarski(X4)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 2.58/0.74    inference(forward_demodulation,[],[f248,f87])).
% 2.58/0.74  fof(f87,plain,(
% 2.58/0.74    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.58/0.74    inference(cnf_transformation,[],[f3])).
% 2.58/0.74  fof(f3,axiom,(
% 2.58/0.74    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.58/0.74  fof(f248,plain,(
% 2.58/0.74    ( ! [X4,X3] : (k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 2.58/0.74    inference(duplicate_literal_removal,[],[f242])).
% 2.58/0.74  fof(f242,plain,(
% 2.58/0.74    ( ! [X4,X3] : (k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 2.58/0.74    inference(superposition,[],[f76,f87])).
% 2.58/0.74  fof(f76,plain,(
% 2.58/0.74    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.58/0.74    inference(cnf_transformation,[],[f32])).
% 2.58/0.74  fof(f32,plain,(
% 2.58/0.74    ! [X0,X1,X2] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.58/0.74    inference(flattening,[],[f31])).
% 2.58/0.74  fof(f31,plain,(
% 2.58/0.74    ! [X0,X1,X2] : ((k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.58/0.74    inference(ennf_transformation,[],[f18])).
% 2.58/0.74  fof(f18,axiom,(
% 2.58/0.74    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))))),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).
% 2.58/0.74  fof(f206,plain,(
% 2.58/0.74    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 2.58/0.74    inference(duplicate_literal_removal,[],[f201])).
% 2.58/0.74  fof(f201,plain,(
% 2.58/0.74    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 2.58/0.74    inference(superposition,[],[f97,f96])).
% 2.58/0.74  fof(f96,plain,(
% 2.58/0.74    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.58/0.74    inference(cnf_transformation,[],[f41])).
% 2.58/0.74  fof(f41,plain,(
% 2.58/0.74    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.58/0.74    inference(flattening,[],[f40])).
% 2.58/0.74  fof(f40,plain,(
% 2.58/0.74    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.58/0.74    inference(ennf_transformation,[],[f17])).
% 2.58/0.74  fof(f17,axiom,(
% 2.58/0.74    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 2.58/0.74  fof(f97,plain,(
% 2.58/0.74    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.58/0.74    inference(cnf_transformation,[],[f42])).
% 2.58/0.74  fof(f42,plain,(
% 2.58/0.74    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.58/0.74    inference(ennf_transformation,[],[f16])).
% 2.58/0.74  fof(f16,axiom,(
% 2.58/0.74    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 2.58/0.74  fof(f228,plain,(
% 2.58/0.74    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | spl5_12),
% 2.58/0.74    inference(avatar_component_clause,[],[f226])).
% 2.58/0.74  fof(f1530,plain,(
% 2.58/0.74    ~spl5_34 | ~spl5_7 | spl5_28),
% 2.58/0.74    inference(avatar_split_clause,[],[f1529,f828,f153,f980])).
% 2.58/0.74  fof(f980,plain,(
% 2.58/0.74    spl5_34 <=> v5_relat_1(sK3,k1_xboole_0)),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 2.58/0.74  fof(f828,plain,(
% 2.58/0.74    spl5_28 <=> r1_tarski(k2_relat_1(sK3),k1_xboole_0)),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 2.58/0.74  fof(f1529,plain,(
% 2.58/0.74    ~v5_relat_1(sK3,k1_xboole_0) | (~spl5_7 | spl5_28)),
% 2.58/0.74    inference(subsumption_resolution,[],[f1522,f155])).
% 2.58/0.74  fof(f1522,plain,(
% 2.58/0.74    ~v5_relat_1(sK3,k1_xboole_0) | ~v1_relat_1(sK3) | spl5_28),
% 2.58/0.74    inference(resolution,[],[f830,f73])).
% 2.58/0.74  fof(f73,plain,(
% 2.58/0.74    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.58/0.74    inference(cnf_transformation,[],[f51])).
% 2.58/0.74  fof(f51,plain,(
% 2.58/0.74    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.58/0.74    inference(nnf_transformation,[],[f29])).
% 2.58/0.74  fof(f29,plain,(
% 2.58/0.74    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.58/0.74    inference(ennf_transformation,[],[f13])).
% 2.58/0.74  fof(f13,axiom,(
% 2.58/0.74    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 2.58/0.74  fof(f830,plain,(
% 2.58/0.74    ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | spl5_28),
% 2.58/0.74    inference(avatar_component_clause,[],[f828])).
% 2.58/0.74  fof(f1370,plain,(
% 2.58/0.74    spl5_53 | ~spl5_28),
% 2.58/0.74    inference(avatar_split_clause,[],[f1369,f828,f1363])).
% 2.58/0.74  fof(f1363,plain,(
% 2.58/0.74    spl5_53 <=> k1_xboole_0 = k2_relat_1(sK3)),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 2.58/0.74  fof(f1369,plain,(
% 2.58/0.74    k1_xboole_0 = k2_relat_1(sK3) | ~spl5_28),
% 2.58/0.74    inference(subsumption_resolution,[],[f1358,f141])).
% 2.58/0.74  fof(f141,plain,(
% 2.58/0.74    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.58/0.74    inference(resolution,[],[f63,f88])).
% 2.58/0.74  fof(f88,plain,(
% 2.58/0.74    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.58/0.74    inference(cnf_transformation,[],[f8])).
% 2.58/0.74  fof(f8,axiom,(
% 2.58/0.74    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.58/0.74  fof(f63,plain,(
% 2.58/0.74    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.58/0.74    inference(cnf_transformation,[],[f45])).
% 2.58/0.74  fof(f45,plain,(
% 2.58/0.74    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.58/0.74    inference(nnf_transformation,[],[f9])).
% 2.58/0.74  fof(f9,axiom,(
% 2.58/0.74    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.58/0.74  fof(f1358,plain,(
% 2.58/0.74    k1_xboole_0 = k2_relat_1(sK3) | ~r1_tarski(k1_xboole_0,k2_relat_1(sK3)) | ~spl5_28),
% 2.58/0.74    inference(resolution,[],[f829,f70])).
% 2.58/0.74  fof(f70,plain,(
% 2.58/0.74    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.58/0.74    inference(cnf_transformation,[],[f49])).
% 2.58/0.74  fof(f49,plain,(
% 2.58/0.74    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.58/0.74    inference(flattening,[],[f48])).
% 2.58/0.74  fof(f48,plain,(
% 2.58/0.74    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.58/0.74    inference(nnf_transformation,[],[f1])).
% 2.58/0.74  fof(f1,axiom,(
% 2.58/0.74    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.58/0.74  fof(f829,plain,(
% 2.58/0.74    r1_tarski(k2_relat_1(sK3),k1_xboole_0) | ~spl5_28),
% 2.58/0.74    inference(avatar_component_clause,[],[f828])).
% 2.58/0.74  fof(f1183,plain,(
% 2.58/0.74    ~spl5_12 | spl5_1 | ~spl5_3),
% 2.58/0.74    inference(avatar_split_clause,[],[f1182,f122,f112,f226])).
% 2.58/0.74  fof(f112,plain,(
% 2.58/0.74    spl5_1 <=> r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.58/0.74  fof(f122,plain,(
% 2.58/0.74    spl5_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.58/0.74  fof(f1182,plain,(
% 2.58/0.74    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | (spl5_1 | ~spl5_3)),
% 2.58/0.74    inference(subsumption_resolution,[],[f1181,f124])).
% 2.58/0.74  fof(f124,plain,(
% 2.58/0.74    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~spl5_3),
% 2.58/0.74    inference(avatar_component_clause,[],[f122])).
% 2.58/0.74  fof(f1181,plain,(
% 2.58/0.74    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | spl5_1),
% 2.58/0.74    inference(superposition,[],[f114,f77])).
% 2.58/0.74  fof(f77,plain,(
% 2.58/0.74    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/0.74    inference(cnf_transformation,[],[f33])).
% 2.58/0.74  fof(f33,plain,(
% 2.58/0.74    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/0.74    inference(ennf_transformation,[],[f20])).
% 2.58/0.74  fof(f20,axiom,(
% 2.58/0.74    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 2.58/0.74  fof(f114,plain,(
% 2.58/0.74    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | spl5_1),
% 2.58/0.74    inference(avatar_component_clause,[],[f112])).
% 2.58/0.74  fof(f1179,plain,(
% 2.58/0.74    spl5_10 | ~spl5_3),
% 2.58/0.74    inference(avatar_split_clause,[],[f1174,f122,f184])).
% 2.58/0.74  fof(f1174,plain,(
% 2.58/0.74    v4_relat_1(sK3,k1_tarski(sK0)) | ~spl5_3),
% 2.58/0.74    inference(resolution,[],[f124,f90])).
% 2.58/0.74  fof(f90,plain,(
% 2.58/0.74    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.58/0.74    inference(cnf_transformation,[],[f36])).
% 2.58/0.74  fof(f36,plain,(
% 2.58/0.74    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/0.74    inference(ennf_transformation,[],[f19])).
% 2.58/0.74  fof(f19,axiom,(
% 2.58/0.74    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.58/0.74  fof(f1172,plain,(
% 2.58/0.74    ~spl5_5 | spl5_12 | ~spl5_20 | ~spl5_41),
% 2.58/0.74    inference(avatar_contradiction_clause,[],[f1171])).
% 2.58/0.74  fof(f1171,plain,(
% 2.58/0.74    $false | (~spl5_5 | spl5_12 | ~spl5_20 | ~spl5_41)),
% 2.58/0.74    inference(subsumption_resolution,[],[f1170,f141])).
% 2.58/0.74  fof(f1170,plain,(
% 2.58/0.74    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | (~spl5_5 | spl5_12 | ~spl5_20 | ~spl5_41)),
% 2.58/0.74    inference(forward_demodulation,[],[f1155,f533])).
% 2.58/0.74  fof(f533,plain,(
% 2.58/0.74    ( ! [X3] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X3)) ) | (~spl5_5 | ~spl5_20)),
% 2.58/0.74    inference(subsumption_resolution,[],[f532,f135])).
% 2.58/0.74  fof(f135,plain,(
% 2.58/0.74    v1_relat_1(k1_xboole_0) | ~spl5_5),
% 2.58/0.74    inference(avatar_component_clause,[],[f133])).
% 2.58/0.74  fof(f133,plain,(
% 2.58/0.74    spl5_5 <=> v1_relat_1(k1_xboole_0)),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.58/0.74  fof(f532,plain,(
% 2.58/0.74    ( ! [X3] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X3) | ~v1_relat_1(k1_xboole_0)) ) | ~spl5_20),
% 2.58/0.74    inference(subsumption_resolution,[],[f525,f141])).
% 2.58/0.74  fof(f525,plain,(
% 2.58/0.74    ( ! [X3] : (~r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,X3)) | k1_xboole_0 = k9_relat_1(k1_xboole_0,X3) | ~v1_relat_1(k1_xboole_0)) ) | ~spl5_20),
% 2.58/0.74    inference(superposition,[],[f159,f482])).
% 2.58/0.74  fof(f482,plain,(
% 2.58/0.74    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl5_20),
% 2.58/0.74    inference(avatar_component_clause,[],[f480])).
% 2.58/0.74  fof(f480,plain,(
% 2.58/0.74    spl5_20 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 2.58/0.74  fof(f159,plain,(
% 2.58/0.74    ( ! [X2,X3] : (~r1_tarski(k2_relat_1(X2),k9_relat_1(X2,X3)) | k9_relat_1(X2,X3) = k2_relat_1(X2) | ~v1_relat_1(X2)) )),
% 2.58/0.74    inference(resolution,[],[f70,f75])).
% 2.58/0.74  fof(f1155,plain,(
% 2.58/0.74    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | (spl5_12 | ~spl5_41)),
% 2.58/0.74    inference(backward_demodulation,[],[f228,f1084])).
% 2.58/0.74  fof(f1084,plain,(
% 2.58/0.74    k1_xboole_0 = sK3 | ~spl5_41),
% 2.58/0.74    inference(avatar_component_clause,[],[f1082])).
% 2.58/0.74  fof(f1082,plain,(
% 2.58/0.74    spl5_41 <=> k1_xboole_0 = sK3),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 2.58/0.74  fof(f1139,plain,(
% 2.58/0.74    spl5_34 | ~spl5_40),
% 2.58/0.74    inference(avatar_contradiction_clause,[],[f1136])).
% 2.58/0.74  fof(f1136,plain,(
% 2.58/0.74    $false | (spl5_34 | ~spl5_40)),
% 2.58/0.74    inference(unit_resulting_resolution,[],[f982,f1074])).
% 2.58/0.74  fof(f1074,plain,(
% 2.58/0.74    ( ! [X0] : (v5_relat_1(sK3,X0)) ) | ~spl5_40),
% 2.58/0.74    inference(resolution,[],[f1071,f260])).
% 2.58/0.74  fof(f260,plain,(
% 2.58/0.74    ( ! [X2,X1] : (~r1_tarski(X1,k1_xboole_0) | v5_relat_1(X1,X2)) )),
% 2.58/0.74    inference(resolution,[],[f192,f64])).
% 2.58/0.74  fof(f64,plain,(
% 2.58/0.74    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.58/0.74    inference(cnf_transformation,[],[f45])).
% 2.58/0.74  fof(f192,plain,(
% 2.58/0.74    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | v5_relat_1(X3,X2)) )),
% 2.58/0.74    inference(superposition,[],[f91,f110])).
% 2.58/0.74  fof(f110,plain,(
% 2.58/0.74    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.58/0.74    inference(equality_resolution,[],[f85])).
% 2.58/0.74  fof(f85,plain,(
% 2.58/0.74    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.58/0.74    inference(cnf_transformation,[],[f58])).
% 2.58/0.74  fof(f58,plain,(
% 2.58/0.74    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.58/0.74    inference(flattening,[],[f57])).
% 2.58/0.74  fof(f57,plain,(
% 2.58/0.74    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.58/0.74    inference(nnf_transformation,[],[f7])).
% 2.58/0.74  fof(f7,axiom,(
% 2.58/0.74    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.58/0.74  fof(f91,plain,(
% 2.58/0.74    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.58/0.74    inference(cnf_transformation,[],[f36])).
% 2.58/0.74  fof(f1071,plain,(
% 2.58/0.74    r1_tarski(sK3,k1_xboole_0) | ~spl5_40),
% 2.58/0.74    inference(avatar_component_clause,[],[f1069])).
% 2.58/0.74  fof(f1069,plain,(
% 2.58/0.74    spl5_40 <=> r1_tarski(sK3,k1_xboole_0)),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 2.58/0.74  fof(f982,plain,(
% 2.58/0.74    ~v5_relat_1(sK3,k1_xboole_0) | spl5_34),
% 2.58/0.74    inference(avatar_component_clause,[],[f980])).
% 2.58/0.74  fof(f1086,plain,(
% 2.58/0.74    spl5_41 | ~spl5_40),
% 2.58/0.74    inference(avatar_split_clause,[],[f1076,f1069,f1082])).
% 2.58/0.74  fof(f1076,plain,(
% 2.58/0.74    k1_xboole_0 = sK3 | ~spl5_40),
% 2.58/0.74    inference(resolution,[],[f1071,f158])).
% 2.58/0.74  fof(f158,plain,(
% 2.58/0.74    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 2.58/0.74    inference(resolution,[],[f70,f141])).
% 2.58/0.74  fof(f1072,plain,(
% 2.58/0.74    spl5_40 | ~spl5_4 | ~spl5_7 | ~spl5_32),
% 2.58/0.74    inference(avatar_split_clause,[],[f1067,f890,f153,f127,f1069])).
% 2.58/0.74  fof(f890,plain,(
% 2.58/0.74    spl5_32 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 2.58/0.74  fof(f1067,plain,(
% 2.58/0.74    r1_tarski(sK3,k1_xboole_0) | (~spl5_4 | ~spl5_7 | ~spl5_32)),
% 2.58/0.74    inference(forward_demodulation,[],[f1066,f110])).
% 2.58/0.74  fof(f1066,plain,(
% 2.58/0.74    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))) | (~spl5_4 | ~spl5_7 | ~spl5_32)),
% 2.58/0.74    inference(subsumption_resolution,[],[f1065,f129])).
% 2.58/0.74  fof(f1065,plain,(
% 2.58/0.74    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))) | ~v1_funct_1(sK3) | (~spl5_7 | ~spl5_32)),
% 2.58/0.74    inference(subsumption_resolution,[],[f1062,f155])).
% 2.58/0.74  fof(f1062,plain,(
% 2.58/0.74    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~spl5_32),
% 2.58/0.74    inference(superposition,[],[f221,f892])).
% 2.58/0.74  fof(f892,plain,(
% 2.58/0.74    k1_xboole_0 = k1_relat_1(sK3) | ~spl5_32),
% 2.58/0.74    inference(avatar_component_clause,[],[f890])).
% 2.58/0.74  fof(f221,plain,(
% 2.58/0.74    ( ! [X5] : (r1_tarski(X5,k2_zfmisc_1(k1_relat_1(X5),k2_relat_1(X5))) | ~v1_relat_1(X5) | ~v1_funct_1(X5)) )),
% 2.58/0.74    inference(resolution,[],[f93,f63])).
% 2.58/0.74  fof(f93,plain,(
% 2.58/0.74    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.58/0.74    inference(cnf_transformation,[],[f38])).
% 2.58/0.74  fof(f38,plain,(
% 2.58/0.74    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.58/0.74    inference(flattening,[],[f37])).
% 2.58/0.74  fof(f37,plain,(
% 2.58/0.74    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.58/0.74    inference(ennf_transformation,[],[f25])).
% 2.58/0.74  fof(f25,plain,(
% 2.58/0.74    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)))),
% 2.58/0.74    inference(pure_predicate_removal,[],[f21])).
% 2.58/0.74  fof(f21,axiom,(
% 2.58/0.74    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 2.58/0.74  fof(f983,plain,(
% 2.58/0.74    ~spl5_13 | ~spl5_34 | ~spl5_7 | spl5_18),
% 2.58/0.74    inference(avatar_split_clause,[],[f978,f443,f153,f980,f294])).
% 2.58/0.74  fof(f294,plain,(
% 2.58/0.74    spl5_13 <=> v4_relat_1(sK3,sK2)),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.58/0.74  fof(f443,plain,(
% 2.58/0.74    spl5_18 <=> r1_tarski(k9_relat_1(sK3,sK2),k1_xboole_0)),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 2.58/0.74  fof(f978,plain,(
% 2.58/0.74    ~v5_relat_1(sK3,k1_xboole_0) | ~v4_relat_1(sK3,sK2) | (~spl5_7 | spl5_18)),
% 2.58/0.74    inference(subsumption_resolution,[],[f838,f155])).
% 2.58/0.74  fof(f838,plain,(
% 2.58/0.74    ~v5_relat_1(sK3,k1_xboole_0) | ~v1_relat_1(sK3) | ~v4_relat_1(sK3,sK2) | spl5_18),
% 2.58/0.74    inference(resolution,[],[f430,f445])).
% 2.58/0.74  fof(f445,plain,(
% 2.58/0.74    ~r1_tarski(k9_relat_1(sK3,sK2),k1_xboole_0) | spl5_18),
% 2.58/0.74    inference(avatar_component_clause,[],[f443])).
% 2.58/0.74  fof(f430,plain,(
% 2.58/0.74    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X0,X1),X2) | ~v5_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 2.58/0.74    inference(duplicate_literal_removal,[],[f429])).
% 2.58/0.74  fof(f429,plain,(
% 2.58/0.74    ( ! [X2,X0,X1] : (~v5_relat_1(X0,X2) | r1_tarski(k9_relat_1(X0,X1),X2) | ~v1_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 2.58/0.74    inference(superposition,[],[f204,f96])).
% 2.58/0.74  fof(f204,plain,(
% 2.58/0.74    ( ! [X6,X7,X5] : (~v5_relat_1(k7_relat_1(X5,X6),X7) | r1_tarski(k9_relat_1(X5,X6),X7) | ~v1_relat_1(k7_relat_1(X5,X6)) | ~v1_relat_1(X5)) )),
% 2.58/0.74    inference(superposition,[],[f73,f97])).
% 2.58/0.74  fof(f943,plain,(
% 2.58/0.74    ~spl5_7 | spl5_13 | ~spl5_32),
% 2.58/0.74    inference(avatar_contradiction_clause,[],[f940])).
% 2.58/0.74  fof(f940,plain,(
% 2.58/0.74    $false | (~spl5_7 | spl5_13 | ~spl5_32)),
% 2.58/0.74    inference(unit_resulting_resolution,[],[f296,f927])).
% 2.58/0.74  fof(f927,plain,(
% 2.58/0.74    ( ! [X0] : (v4_relat_1(sK3,X0)) ) | (~spl5_7 | ~spl5_32)),
% 2.58/0.74    inference(subsumption_resolution,[],[f926,f155])).
% 2.58/0.74  fof(f926,plain,(
% 2.58/0.74    ( ! [X0] : (v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | ~spl5_32),
% 2.58/0.74    inference(subsumption_resolution,[],[f924,f141])).
% 2.58/0.74  fof(f924,plain,(
% 2.58/0.74    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | ~spl5_32),
% 2.58/0.74    inference(superposition,[],[f72,f892])).
% 2.58/0.74  fof(f72,plain,(
% 2.58/0.74    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.58/0.74    inference(cnf_transformation,[],[f50])).
% 2.58/0.74  fof(f50,plain,(
% 2.58/0.74    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.58/0.74    inference(nnf_transformation,[],[f28])).
% 2.58/0.74  fof(f28,plain,(
% 2.58/0.74    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.58/0.74    inference(ennf_transformation,[],[f12])).
% 2.58/0.74  fof(f12,axiom,(
% 2.58/0.74    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.58/0.74  fof(f296,plain,(
% 2.58/0.74    ~v4_relat_1(sK3,sK2) | spl5_13),
% 2.58/0.74    inference(avatar_component_clause,[],[f294])).
% 2.58/0.74  fof(f893,plain,(
% 2.58/0.74    spl5_31 | spl5_32 | ~spl5_7 | ~spl5_10),
% 2.58/0.74    inference(avatar_split_clause,[],[f884,f184,f153,f890,f886])).
% 2.58/0.74  fof(f884,plain,(
% 2.58/0.74    k1_xboole_0 = k1_relat_1(sK3) | r2_hidden(sK0,k1_relat_1(sK3)) | (~spl5_7 | ~spl5_10)),
% 2.58/0.74    inference(subsumption_resolution,[],[f880,f155])).
% 2.58/0.74  fof(f880,plain,(
% 2.58/0.74    k1_xboole_0 = k1_relat_1(sK3) | r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl5_10),
% 2.58/0.74    inference(resolution,[],[f354,f186])).
% 2.58/0.74  fof(f354,plain,(
% 2.58/0.74    ( ! [X21,X20] : (~v4_relat_1(X21,k1_tarski(X20)) | k1_xboole_0 = k1_relat_1(X21) | r2_hidden(X20,k1_relat_1(X21)) | ~v1_relat_1(X21)) )),
% 2.58/0.74    inference(superposition,[],[f138,f209])).
% 2.58/0.74  fof(f209,plain,(
% 2.58/0.74    ( ! [X2,X3] : (k1_relat_1(X2) = k1_tarski(X3) | k1_xboole_0 = k1_relat_1(X2) | ~v4_relat_1(X2,k1_tarski(X3)) | ~v1_relat_1(X2)) )),
% 2.58/0.74    inference(resolution,[],[f65,f71])).
% 2.58/0.74  fof(f71,plain,(
% 2.58/0.74    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.58/0.74    inference(cnf_transformation,[],[f50])).
% 2.58/0.74  fof(f65,plain,(
% 2.58/0.74    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.58/0.74    inference(cnf_transformation,[],[f47])).
% 2.58/0.74  fof(f47,plain,(
% 2.58/0.74    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.58/0.74    inference(flattening,[],[f46])).
% 2.58/0.74  fof(f46,plain,(
% 2.58/0.74    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.58/0.74    inference(nnf_transformation,[],[f6])).
% 2.58/0.74  fof(f6,axiom,(
% 2.58/0.74    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.58/0.74  fof(f138,plain,(
% 2.58/0.74    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 2.58/0.74    inference(superposition,[],[f107,f87])).
% 2.58/0.74  fof(f107,plain,(
% 2.58/0.74    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 2.58/0.74    inference(equality_resolution,[],[f106])).
% 2.58/0.74  fof(f106,plain,(
% 2.58/0.74    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 2.58/0.74    inference(equality_resolution,[],[f79])).
% 2.58/0.74  fof(f79,plain,(
% 2.58/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.58/0.74    inference(cnf_transformation,[],[f56])).
% 2.58/0.74  fof(f56,plain,(
% 2.58/0.74    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.58/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f54,f55])).
% 2.58/0.74  fof(f55,plain,(
% 2.58/0.74    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.58/0.74    introduced(choice_axiom,[])).
% 2.58/0.74  fof(f54,plain,(
% 2.58/0.74    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.58/0.74    inference(rectify,[],[f53])).
% 2.58/0.74  fof(f53,plain,(
% 2.58/0.74    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.58/0.74    inference(flattening,[],[f52])).
% 2.58/0.74  fof(f52,plain,(
% 2.58/0.74    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.58/0.74    inference(nnf_transformation,[],[f2])).
% 2.58/0.74  fof(f2,axiom,(
% 2.58/0.74    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.58/0.74  fof(f483,plain,(
% 2.58/0.74    ~spl5_19 | spl5_20 | ~spl5_5 | spl5_12),
% 2.58/0.74    inference(avatar_split_clause,[],[f474,f226,f133,f480,f476])).
% 2.58/0.74  fof(f476,plain,(
% 2.58/0.74    spl5_19 <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(k1_xboole_0))),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 2.58/0.74  fof(f474,plain,(
% 2.58/0.74    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(k1_xboole_0)) | (~spl5_5 | spl5_12)),
% 2.58/0.74    inference(subsumption_resolution,[],[f470,f135])).
% 2.58/0.74  fof(f470,plain,(
% 2.58/0.74    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | spl5_12),
% 2.58/0.74    inference(resolution,[],[f393,f189])).
% 2.58/0.74  fof(f189,plain,(
% 2.58/0.74    ( ! [X0] : (v5_relat_1(k1_xboole_0,X0)) )),
% 2.58/0.74    inference(resolution,[],[f91,f88])).
% 2.58/0.74  fof(f393,plain,(
% 2.58/0.74    ( ! [X9] : (~v5_relat_1(X9,k1_tarski(k1_funct_1(sK3,sK0))) | k1_xboole_0 = k2_relat_1(X9) | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(X9)) | ~v1_relat_1(X9)) ) | spl5_12),
% 2.58/0.74    inference(superposition,[],[f228,f210])).
% 2.58/0.74  fof(f210,plain,(
% 2.58/0.74    ( ! [X4,X5] : (k2_relat_1(X4) = k1_tarski(X5) | k1_xboole_0 = k2_relat_1(X4) | ~v5_relat_1(X4,k1_tarski(X5)) | ~v1_relat_1(X4)) )),
% 2.58/0.74    inference(resolution,[],[f65,f73])).
% 2.58/0.74  fof(f376,plain,(
% 2.58/0.74    ~spl5_15 | spl5_16 | ~spl5_5 | spl5_12),
% 2.58/0.74    inference(avatar_split_clause,[],[f367,f226,f133,f373,f369])).
% 2.58/0.74  fof(f369,plain,(
% 2.58/0.74    spl5_15 <=> r1_tarski(k9_relat_1(sK3,sK2),k1_relat_1(k1_xboole_0))),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.58/0.74  fof(f373,plain,(
% 2.58/0.74    spl5_16 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.58/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 2.58/0.74  fof(f367,plain,(
% 2.58/0.74    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~r1_tarski(k9_relat_1(sK3,sK2),k1_relat_1(k1_xboole_0)) | (~spl5_5 | spl5_12)),
% 2.58/0.74    inference(subsumption_resolution,[],[f364,f135])).
% 2.58/0.74  fof(f364,plain,(
% 2.58/0.74    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~r1_tarski(k9_relat_1(sK3,sK2),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | spl5_12),
% 2.58/0.74    inference(resolution,[],[f348,f179])).
% 2.58/0.74  fof(f179,plain,(
% 2.58/0.74    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 2.58/0.74    inference(resolution,[],[f90,f88])).
% 2.58/0.74  fof(f348,plain,(
% 2.58/0.74    ( ! [X7] : (~v4_relat_1(X7,k1_tarski(k1_funct_1(sK3,sK0))) | k1_xboole_0 = k1_relat_1(X7) | ~r1_tarski(k9_relat_1(sK3,sK2),k1_relat_1(X7)) | ~v1_relat_1(X7)) ) | spl5_12),
% 2.58/0.74    inference(superposition,[],[f228,f209])).
% 2.58/0.74  fof(f156,plain,(
% 2.58/0.74    spl5_7 | ~spl5_3),
% 2.58/0.74    inference(avatar_split_clause,[],[f151,f122,f153])).
% 2.58/0.74  fof(f151,plain,(
% 2.58/0.74    v1_relat_1(sK3) | ~spl5_3),
% 2.58/0.74    inference(subsumption_resolution,[],[f148,f95])).
% 2.58/0.74  fof(f95,plain,(
% 2.58/0.74    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.58/0.74    inference(cnf_transformation,[],[f14])).
% 2.58/0.74  fof(f14,axiom,(
% 2.58/0.74    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.58/0.74  fof(f148,plain,(
% 2.58/0.74    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) | ~spl5_3),
% 2.58/0.74    inference(resolution,[],[f94,f124])).
% 2.58/0.74  fof(f94,plain,(
% 2.58/0.74    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.58/0.74    inference(cnf_transformation,[],[f39])).
% 2.58/0.74  fof(f39,plain,(
% 2.58/0.74    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.58/0.74    inference(ennf_transformation,[],[f11])).
% 2.58/0.74  fof(f11,axiom,(
% 2.58/0.74    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.58/0.74  fof(f136,plain,(
% 2.58/0.74    spl5_5),
% 2.58/0.74    inference(avatar_split_clause,[],[f131,f133])).
% 2.58/0.74  fof(f131,plain,(
% 2.58/0.74    v1_relat_1(k1_xboole_0)),
% 2.58/0.74    inference(superposition,[],[f95,f109])).
% 2.58/0.74  fof(f109,plain,(
% 2.58/0.74    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.58/0.74    inference(equality_resolution,[],[f86])).
% 2.58/0.74  fof(f86,plain,(
% 2.58/0.74    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.58/0.74    inference(cnf_transformation,[],[f58])).
% 2.58/0.74  fof(f130,plain,(
% 2.58/0.74    spl5_4),
% 2.58/0.74    inference(avatar_split_clause,[],[f59,f127])).
% 2.58/0.74  fof(f59,plain,(
% 2.58/0.74    v1_funct_1(sK3)),
% 2.58/0.74    inference(cnf_transformation,[],[f44])).
% 2.58/0.74  fof(f44,plain,(
% 2.58/0.74    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.58/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f43])).
% 2.58/0.74  fof(f43,plain,(
% 2.58/0.74    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.58/0.74    introduced(choice_axiom,[])).
% 2.58/0.74  fof(f27,plain,(
% 2.58/0.74    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.58/0.74    inference(flattening,[],[f26])).
% 2.58/0.74  fof(f26,plain,(
% 2.58/0.74    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.58/0.74    inference(ennf_transformation,[],[f24])).
% 2.58/0.74  fof(f24,plain,(
% 2.58/0.74    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.58/0.74    inference(pure_predicate_removal,[],[f23])).
% 2.58/0.74  fof(f23,negated_conjecture,(
% 2.58/0.74    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.58/0.74    inference(negated_conjecture,[],[f22])).
% 2.58/0.74  fof(f22,conjecture,(
% 2.58/0.74    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.58/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 2.58/0.77  fof(f125,plain,(
% 2.58/0.77    spl5_3),
% 2.58/0.77    inference(avatar_split_clause,[],[f60,f122])).
% 2.58/0.77  fof(f60,plain,(
% 2.58/0.77    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.58/0.77    inference(cnf_transformation,[],[f44])).
% 2.58/0.77  fof(f115,plain,(
% 2.58/0.77    ~spl5_1),
% 2.58/0.77    inference(avatar_split_clause,[],[f62,f112])).
% 2.58/0.77  fof(f62,plain,(
% 2.58/0.77    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.58/0.77    inference(cnf_transformation,[],[f44])).
% 2.58/0.77  % SZS output end Proof for theBenchmark
% 2.58/0.77  % (18846)------------------------------
% 2.58/0.77  % (18846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.58/0.77  % (18846)Termination reason: Refutation
% 2.58/0.77  
% 2.58/0.77  % (18846)Memory used [KB]: 8059
% 2.58/0.77  % (18846)Time elapsed: 0.297 s
% 2.58/0.77  % (18846)------------------------------
% 2.58/0.77  % (18846)------------------------------
% 2.58/0.77  % (18824)Success in time 0.411 s
%------------------------------------------------------------------------------
