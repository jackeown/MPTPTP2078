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
% DateTime   : Thu Dec  3 13:02:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 466 expanded)
%              Number of leaves         :   38 ( 178 expanded)
%              Depth                    :   13
%              Number of atoms          :  603 (1421 expanded)
%              Number of equality atoms :  112 ( 274 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f656,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f102,f114,f121,f125,f129,f151,f158,f166,f182,f202,f254,f260,f272,f287,f296,f355,f387,f399,f411,f415,f416,f418,f484,f655])).

fof(f655,plain,
    ( ~ spl3_1
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_26
    | ~ spl3_33
    | spl3_45 ),
    inference(avatar_contradiction_clause,[],[f654])).

fof(f654,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_26
    | ~ spl3_33
    | spl3_45 ),
    inference(subsumption_resolution,[],[f483,f653])).

fof(f653,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_26
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f652,f65])).

fof(f65,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f652,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_26
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f651,f366])).

fof(f366,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f365])).

fof(f365,plain,
    ( spl3_33
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f651,plain,
    ( ! [X0] : v1_funct_2(sK2,k1_relat_1(sK2),X0)
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f650,f82])).

fof(f82,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f650,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(sK2,k1_relat_1(sK2),X0) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_26 ),
    inference(superposition,[],[f188,f286])).

fof(f286,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl3_26
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f188,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK1,X1)
        | v1_funct_2(sK2,k1_relat_1(sK2),X1) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f187,f150])).

fof(f150,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f187,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK1,X1)
        | ~ v1_relat_1(sK2)
        | v1_funct_2(sK2,k1_relat_1(sK2),X1) )
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f184,f97])).

fof(f97,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f184,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK1,X1)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | v1_funct_2(sK2,k1_relat_1(sK2),X1) )
    | ~ spl3_11 ),
    inference(superposition,[],[f77,f181])).

fof(f181,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl3_11
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f483,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl3_45 ),
    inference(avatar_component_clause,[],[f482])).

fof(f482,plain,
    ( spl3_45
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f484,plain,
    ( ~ spl3_45
    | ~ spl3_4
    | spl3_9
    | ~ spl3_26
    | ~ spl3_30
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f454,f365,f301,f285,f156,f116,f482])).

fof(f116,plain,
    ( spl3_4
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f156,plain,
    ( spl3_9
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f301,plain,
    ( spl3_30
  <=> k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f454,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ spl3_4
    | spl3_9
    | ~ spl3_26
    | ~ spl3_30
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f453,f437])).

fof(f437,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_30
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f346,f366])).

fof(f346,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_4
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f161,f302])).

fof(f302,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f301])).

fof(f161,plain,
    ( k1_xboole_0 != k1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f117,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f117,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f453,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl3_9
    | ~ spl3_26
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f452,f366])).

fof(f452,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_9
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f157,f286])).

fof(f157,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f156])).

fof(f418,plain,
    ( k1_xboole_0 != sK1
    | sK1 != k1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f416,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f415,plain,
    ( spl3_38
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f176,f164,f127,f123,f116,f100,f96,f413])).

fof(f413,plain,
    ( spl3_38
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f100,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f123,plain,
    ( spl3_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f127,plain,
    ( spl3_7
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f164,plain,
    ( spl3_10
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f176,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f175,f143])).

fof(f143,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f142,f140])).

fof(f140,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f134,f128])).

fof(f128,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f134,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f124,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f124,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f142,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f109,f133])).

fof(f133,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f124,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f109,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f107,f97])).

fof(f107,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f101,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f101,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f175,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f174,f141])).

fof(f141,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f110,f133])).

fof(f110,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f108,f97])).

fof(f108,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f101,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f174,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f168,f117])).

fof(f168,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_10 ),
    inference(resolution,[],[f165,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f165,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f164])).

fof(f411,plain,
    ( ~ spl3_26
    | ~ spl3_11
    | spl3_29 ),
    inference(avatar_split_clause,[],[f404,f298,f180,f285])).

fof(f298,plain,
    ( spl3_29
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f404,plain,
    ( k1_xboole_0 != sK1
    | ~ spl3_11
    | spl3_29 ),
    inference(superposition,[],[f398,f181])).

fof(f398,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl3_29 ),
    inference(avatar_component_clause,[],[f298])).

fof(f399,plain,
    ( spl3_33
    | ~ spl3_29
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f160,f119,f298,f365])).

fof(f160,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_5 ),
    inference(resolution,[],[f150,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f387,plain,
    ( spl3_9
    | ~ spl3_24
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f343,f289,f270,f156])).

fof(f270,plain,
    ( spl3_24
  <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f289,plain,
    ( spl3_27
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f343,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl3_24
    | ~ spl3_27 ),
    inference(superposition,[],[f271,f290])).

fof(f290,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f289])).

fof(f271,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f270])).

fof(f355,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | spl3_8
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_29
    | ~ spl3_30 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | spl3_8
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_29
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f353,f348])).

fof(f348,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f326,f347])).

fof(f347,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_5
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f160,f299])).

fof(f299,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f298])).

fof(f326,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_23
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f318,f88])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f318,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl3_23
    | ~ spl3_26 ),
    inference(superposition,[],[f259,f286])).

fof(f259,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl3_23
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f353,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_4
    | spl3_8
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f320,f346])).

fof(f320,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl3_8
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f312,f89])).

fof(f89,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f312,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_8
    | ~ spl3_26 ),
    inference(superposition,[],[f154,f286])).

fof(f154,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl3_8
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f296,plain,
    ( spl3_27
    | ~ spl3_22
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f294,f282,f252,f289])).

fof(f252,plain,
    ( spl3_22
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f282,plain,
    ( spl3_25
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f294,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_22
    | ~ spl3_25 ),
    inference(superposition,[],[f283,f253])).

fof(f253,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f252])).

fof(f283,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f282])).

fof(f287,plain,
    ( spl3_25
    | spl3_26
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f137,f123,f112,f285,f282])).

fof(f112,plain,
    ( spl3_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f137,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f132,f113])).

fof(f113,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f132,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_6 ),
    inference(resolution,[],[f124,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f272,plain,
    ( spl3_24
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f173,f164,f127,f123,f116,f100,f96,f270])).

fof(f173,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f172,f143])).

fof(f172,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f171,f141])).

fof(f171,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f167,f117])).

fof(f167,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_10 ),
    inference(resolution,[],[f165,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f260,plain,
    ( spl3_23
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f147,f127,f123,f96,f258])).

fof(f147,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f146,f140])).

fof(f146,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f104,f133])).

fof(f104,plain,
    ( ~ v1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_1 ),
    inference(resolution,[],[f97,f80])).

fof(f254,plain,
    ( spl3_22
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f130,f123,f252])).

fof(f130,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f124,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f202,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f143,f127,f123,f100,f96,f200])).

fof(f200,plain,
    ( spl3_14
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f182,plain,
    ( spl3_11
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f140,f127,f123,f180])).

fof(f166,plain,
    ( spl3_10
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f144,f123,f96,f164])).

fof(f144,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f106,f133])).

fof(f106,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f97,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f158,plain,
    ( ~ spl3_8
    | ~ spl3_9
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f145,f123,f96,f156,f153])).

fof(f145,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f48,f144])).

fof(f48,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
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

fof(f151,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f133,f123,f119])).

fof(f129,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f53,f127])).

fof(f53,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f125,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f51,f123])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f121,plain,
    ( spl3_4
    | ~ spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f105,f96,f119,f116])).

fof(f105,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f97,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f114,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f50,f112])).

fof(f50,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f102,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f52,f100])).

fof(f52,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f98,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f49,f96])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:17:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (9117)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (9105)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (9117)Refutation not found, incomplete strategy% (9117)------------------------------
% 0.21/0.48  % (9117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9117)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9117)Memory used [KB]: 1791
% 0.21/0.48  % (9117)Time elapsed: 0.014 s
% 0.21/0.48  % (9117)------------------------------
% 0.21/0.48  % (9117)------------------------------
% 0.21/0.49  % (9112)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (9104)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (9105)Refutation not found, incomplete strategy% (9105)------------------------------
% 0.21/0.49  % (9105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9105)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (9105)Memory used [KB]: 10746
% 0.21/0.49  % (9105)Time elapsed: 0.071 s
% 0.21/0.49  % (9105)------------------------------
% 0.21/0.49  % (9105)------------------------------
% 0.21/0.50  % (9118)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (9116)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (9104)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f656,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f98,f102,f114,f121,f125,f129,f151,f158,f166,f182,f202,f254,f260,f272,f287,f296,f355,f387,f399,f411,f415,f416,f418,f484,f655])).
% 0.21/0.50  fof(f655,plain,(
% 0.21/0.50    ~spl3_1 | ~spl3_5 | ~spl3_11 | ~spl3_26 | ~spl3_33 | spl3_45),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f654])).
% 0.21/0.50  fof(f654,plain,(
% 0.21/0.50    $false | (~spl3_1 | ~spl3_5 | ~spl3_11 | ~spl3_26 | ~spl3_33 | spl3_45)),
% 0.21/0.50    inference(subsumption_resolution,[],[f483,f653])).
% 0.21/0.50  fof(f653,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl3_1 | ~spl3_5 | ~spl3_11 | ~spl3_26 | ~spl3_33)),
% 0.21/0.50    inference(forward_demodulation,[],[f652,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.50  fof(f652,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)) ) | (~spl3_1 | ~spl3_5 | ~spl3_11 | ~spl3_26 | ~spl3_33)),
% 0.21/0.50    inference(forward_demodulation,[],[f651,f366])).
% 0.21/0.50  fof(f366,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | ~spl3_33),
% 0.21/0.50    inference(avatar_component_clause,[],[f365])).
% 0.21/0.50  fof(f365,plain,(
% 0.21/0.50    spl3_33 <=> k1_xboole_0 = sK2),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.50  fof(f651,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(sK2,k1_relat_1(sK2),X0)) ) | (~spl3_1 | ~spl3_5 | ~spl3_11 | ~spl3_26)),
% 0.21/0.50    inference(subsumption_resolution,[],[f650,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.50  fof(f650,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) ) | (~spl3_1 | ~spl3_5 | ~spl3_11 | ~spl3_26)),
% 0.21/0.50    inference(superposition,[],[f188,f286])).
% 0.21/0.50  fof(f286,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~spl3_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f285])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    spl3_26 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_tarski(sK1,X1) | v1_funct_2(sK2,k1_relat_1(sK2),X1)) ) | (~spl3_1 | ~spl3_5 | ~spl3_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f187,f150])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    v1_relat_1(sK2) | ~spl3_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f119])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl3_5 <=> v1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_tarski(sK1,X1) | ~v1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),X1)) ) | (~spl3_1 | ~spl3_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f184,f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    v1_funct_1(sK2) | ~spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl3_1 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_tarski(sK1,X1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),X1)) ) | ~spl3_11),
% 0.21/0.50    inference(superposition,[],[f77,f181])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    sK1 = k2_relat_1(sK2) | ~spl3_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f180])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    spl3_11 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.50  fof(f483,plain,(
% 0.21/0.50    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | spl3_45),
% 0.21/0.50    inference(avatar_component_clause,[],[f482])).
% 0.21/0.50  fof(f482,plain,(
% 0.21/0.50    spl3_45 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.50  fof(f484,plain,(
% 0.21/0.50    ~spl3_45 | ~spl3_4 | spl3_9 | ~spl3_26 | ~spl3_30 | ~spl3_33),
% 0.21/0.50    inference(avatar_split_clause,[],[f454,f365,f301,f285,f156,f116,f482])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    spl3_4 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    spl3_9 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.50  fof(f301,plain,(
% 0.21/0.50    spl3_30 <=> k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.50  fof(f454,plain,(
% 0.21/0.50    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (~spl3_4 | spl3_9 | ~spl3_26 | ~spl3_30 | ~spl3_33)),
% 0.21/0.50    inference(forward_demodulation,[],[f453,f437])).
% 0.21/0.50  fof(f437,plain,(
% 0.21/0.50    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_4 | ~spl3_30 | ~spl3_33)),
% 0.21/0.50    inference(forward_demodulation,[],[f346,f366])).
% 0.21/0.50  fof(f346,plain,(
% 0.21/0.50    k1_xboole_0 = k2_funct_1(sK2) | (~spl3_4 | ~spl3_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f161,f302])).
% 0.21/0.50  fof(f302,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f301])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_funct_1(sK2) | ~spl3_4),
% 0.21/0.50    inference(resolution,[],[f117,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    v1_relat_1(k2_funct_1(sK2)) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f116])).
% 0.21/0.50  fof(f453,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl3_9 | ~spl3_26 | ~spl3_33)),
% 0.21/0.50    inference(forward_demodulation,[],[f452,f366])).
% 0.21/0.50  fof(f452,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl3_9 | ~spl3_26)),
% 0.21/0.50    inference(forward_demodulation,[],[f157,f286])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f156])).
% 0.21/0.50  fof(f418,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | sK1 != k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f416,plain,(
% 0.21/0.50    sK0 != k1_relset_1(sK0,sK1,sK2) | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f415,plain,(
% 0.21/0.50    spl3_38 | ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f176,f164,f127,f123,f116,f100,f96,f413])).
% 0.21/0.50  fof(f413,plain,(
% 0.21/0.50    spl3_38 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl3_2 <=> v2_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    spl3_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl3_7 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    spl3_10 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_10)),
% 0.21/0.50    inference(forward_demodulation,[],[f175,f143])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7)),
% 0.21/0.50    inference(forward_demodulation,[],[f142,f140])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    sK1 = k2_relat_1(sK2) | (~spl3_6 | ~spl3_7)),
% 0.21/0.50    inference(forward_demodulation,[],[f134,f128])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl3_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f127])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_6),
% 0.21/0.50    inference(resolution,[],[f124,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f123])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f109,f133])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    v1_relat_1(sK2) | ~spl3_6),
% 0.21/0.50    inference(resolution,[],[f124,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f107,f97])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.21/0.50    inference(resolution,[],[f101,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    v2_funct_1(sK2) | ~spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f100])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_10)),
% 0.21/0.50    inference(forward_demodulation,[],[f174,f141])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f110,f133])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f108,f97])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.21/0.50    inference(resolution,[],[f101,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | (~spl3_4 | ~spl3_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f168,f117])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl3_10),
% 0.21/0.50    inference(resolution,[],[f165,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    v1_funct_1(k2_funct_1(sK2)) | ~spl3_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f164])).
% 0.21/0.50  fof(f411,plain,(
% 0.21/0.50    ~spl3_26 | ~spl3_11 | spl3_29),
% 0.21/0.50    inference(avatar_split_clause,[],[f404,f298,f180,f285])).
% 0.21/0.50  fof(f298,plain,(
% 0.21/0.50    spl3_29 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.50  fof(f404,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | (~spl3_11 | spl3_29)),
% 0.21/0.50    inference(superposition,[],[f398,f181])).
% 0.21/0.50  fof(f398,plain,(
% 0.21/0.50    k1_xboole_0 != k2_relat_1(sK2) | spl3_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f298])).
% 0.21/0.50  fof(f399,plain,(
% 0.21/0.50    spl3_33 | ~spl3_29 | ~spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f160,f119,f298,f365])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl3_5),
% 0.21/0.50    inference(resolution,[],[f150,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f387,plain,(
% 0.21/0.50    spl3_9 | ~spl3_24 | ~spl3_27),
% 0.21/0.50    inference(avatar_split_clause,[],[f343,f289,f270,f156])).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    spl3_24 <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.50  fof(f289,plain,(
% 0.21/0.50    spl3_27 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.50  fof(f343,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl3_24 | ~spl3_27)),
% 0.21/0.50    inference(superposition,[],[f271,f290])).
% 0.21/0.50  fof(f290,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK2) | ~spl3_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f289])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~spl3_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f270])).
% 0.21/0.50  fof(f355,plain,(
% 0.21/0.50    ~spl3_4 | ~spl3_5 | spl3_8 | ~spl3_23 | ~spl3_26 | ~spl3_29 | ~spl3_30),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f354])).
% 0.21/0.50  fof(f354,plain,(
% 0.21/0.50    $false | (~spl3_4 | ~spl3_5 | spl3_8 | ~spl3_23 | ~spl3_26 | ~spl3_29 | ~spl3_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f353,f348])).
% 0.21/0.50  fof(f348,plain,(
% 0.21/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_5 | ~spl3_23 | ~spl3_26 | ~spl3_29)),
% 0.21/0.50    inference(forward_demodulation,[],[f326,f347])).
% 0.21/0.50  fof(f347,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | (~spl3_5 | ~spl3_29)),
% 0.21/0.50    inference(subsumption_resolution,[],[f160,f299])).
% 0.21/0.50  fof(f299,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(sK2) | ~spl3_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f298])).
% 0.21/0.50  fof(f326,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl3_23 | ~spl3_26)),
% 0.21/0.50    inference(forward_demodulation,[],[f318,f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.50  fof(f318,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | (~spl3_23 | ~spl3_26)),
% 0.21/0.50    inference(superposition,[],[f259,f286])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~spl3_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f258])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    spl3_23 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.50  fof(f353,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_4 | spl3_8 | ~spl3_26 | ~spl3_30)),
% 0.21/0.50    inference(forward_demodulation,[],[f320,f346])).
% 0.21/0.50  fof(f320,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl3_8 | ~spl3_26)),
% 0.21/0.50    inference(forward_demodulation,[],[f312,f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f312,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_8 | ~spl3_26)),
% 0.21/0.50    inference(superposition,[],[f154,f286])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f153])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    spl3_8 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    spl3_27 | ~spl3_22 | ~spl3_25),
% 0.21/0.50    inference(avatar_split_clause,[],[f294,f282,f252,f289])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    spl3_22 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    spl3_25 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK2) | (~spl3_22 | ~spl3_25)),
% 0.21/0.50    inference(superposition,[],[f283,f253])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl3_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f252])).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f282])).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    spl3_25 | spl3_26 | ~spl3_3 | ~spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f137,f123,f112,f285,f282])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    spl3_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl3_3 | ~spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f132,f113])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,sK1) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f112])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl3_6),
% 0.21/0.50    inference(resolution,[],[f124,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    spl3_24 | ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f173,f164,f127,f123,f116,f100,f96,f270])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_10)),
% 0.21/0.50    inference(forward_demodulation,[],[f172,f143])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_10)),
% 0.21/0.50    inference(forward_demodulation,[],[f171,f141])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | (~spl3_4 | ~spl3_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f167,f117])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl3_10),
% 0.21/0.50    inference(resolution,[],[f165,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    spl3_23 | ~spl3_1 | ~spl3_6 | ~spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f147,f127,f123,f96,f258])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | (~spl3_1 | ~spl3_6 | ~spl3_7)),
% 0.21/0.50    inference(forward_demodulation,[],[f146,f140])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_1 | ~spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f104,f133])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_1),
% 0.21/0.50    inference(resolution,[],[f97,f80])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    spl3_22 | ~spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f130,f123,f252])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl3_6),
% 0.21/0.50    inference(resolution,[],[f124,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    spl3_14 | ~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f143,f127,f123,f100,f96,f200])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    spl3_14 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    spl3_11 | ~spl3_6 | ~spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f140,f127,f123,f180])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    spl3_10 | ~spl3_1 | ~spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f144,f123,f96,f164])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f106,f133])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.21/0.50    inference(resolution,[],[f97,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ~spl3_8 | ~spl3_9 | ~spl3_1 | ~spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f145,f123,f96,f156,f153])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_1 | ~spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f48,f144])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f24])).
% 0.21/0.50  fof(f24,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    spl3_5 | ~spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f133,f123,f119])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f127])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f51,f123])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    spl3_4 | ~spl3_5 | ~spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f105,f96,f119,f116])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.21/0.50    inference(resolution,[],[f97,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f112])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f100])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    v2_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f96])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (9104)------------------------------
% 0.21/0.50  % (9104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (9104)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (9104)Memory used [KB]: 6524
% 0.21/0.50  % (9104)Time elapsed: 0.076 s
% 0.21/0.50  % (9104)------------------------------
% 0.21/0.50  % (9104)------------------------------
% 0.21/0.50  % (9103)Success in time 0.135 s
%------------------------------------------------------------------------------
