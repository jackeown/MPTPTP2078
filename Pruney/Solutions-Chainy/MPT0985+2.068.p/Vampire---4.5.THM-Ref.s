%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 322 expanded)
%              Number of leaves         :   39 ( 132 expanded)
%              Depth                    :   13
%              Number of atoms          :  574 (1035 expanded)
%              Number of equality atoms :  109 ( 214 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f524,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f105,f120,f126,f131,f144,f157,f165,f170,f179,f235,f246,f287,f314,f325,f334,f394,f411,f438,f439,f440,f442,f513,f518,f523])).

fof(f523,plain,
    ( spl7_8
    | ~ spl7_25
    | ~ spl7_31 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | spl7_8
    | ~ spl7_25
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f521,f393])).

fof(f393,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl7_31
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f521,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl7_8
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f520,f90])).

fof(f90,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f520,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl7_8
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f148,f323])).

fof(f323,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl7_25
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f148,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl7_8
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f518,plain,
    ( ~ spl7_28
    | ~ spl7_31
    | spl7_38 ),
    inference(avatar_contradiction_clause,[],[f517])).

fof(f517,plain,
    ( $false
    | ~ spl7_28
    | ~ spl7_31
    | spl7_38 ),
    inference(subsumption_resolution,[],[f516,f393])).

fof(f516,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_28
    | spl7_38 ),
    inference(forward_demodulation,[],[f515,f90])).

fof(f515,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl7_28
    | spl7_38 ),
    inference(subsumption_resolution,[],[f514,f342])).

fof(f342,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl7_28
  <=> k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f514,plain,
    ( k1_xboole_0 != k1_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl7_38 ),
    inference(superposition,[],[f512,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f512,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | spl7_38 ),
    inference(avatar_component_clause,[],[f510])).

fof(f510,plain,
    ( spl7_38
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f513,plain,
    ( ~ spl7_38
    | spl7_9
    | ~ spl7_25
    | ~ spl7_31
    | spl7_32 ),
    inference(avatar_split_clause,[],[f504,f406,f391,f322,f150,f510])).

fof(f150,plain,
    ( spl7_9
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f406,plain,
    ( spl7_32
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f504,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | spl7_9
    | ~ spl7_25
    | ~ spl7_31
    | spl7_32 ),
    inference(subsumption_resolution,[],[f503,f393])).

fof(f503,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | spl7_9
    | ~ spl7_25
    | spl7_32 ),
    inference(forward_demodulation,[],[f502,f90])).

fof(f502,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | spl7_9
    | ~ spl7_25
    | spl7_32 ),
    inference(forward_demodulation,[],[f501,f323])).

fof(f501,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl7_9
    | ~ spl7_25
    | spl7_32 ),
    inference(forward_demodulation,[],[f445,f323])).

fof(f445,plain,
    ( sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl7_9
    | spl7_32 ),
    inference(subsumption_resolution,[],[f444,f407])).

fof(f407,plain,
    ( k1_xboole_0 != sK0
    | spl7_32 ),
    inference(avatar_component_clause,[],[f406])).

fof(f444,plain,
    ( k1_xboole_0 = sK0
    | sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl7_9 ),
    inference(resolution,[],[f152,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f152,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f150])).

fof(f442,plain,
    ( k1_xboole_0 != sK1
    | sK1 != k1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f440,plain,
    ( sK0 != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f439,plain,
    ( sK0 != k1_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f438,plain,
    ( spl7_35
    | ~ spl7_4
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f401,f331,f123,f435])).

fof(f435,plain,
    ( spl7_35
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f123,plain,
    ( spl7_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f331,plain,
    ( spl7_26
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f401,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_4
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f399,f125])).

fof(f125,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f399,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_26 ),
    inference(superposition,[],[f333,f79])).

fof(f333,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f331])).

fof(f411,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f394,plain,
    ( spl7_31
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_24
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f388,f322,f318,f243,f232,f154,f137,f391])).

fof(f137,plain,
    ( spl7_6
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f154,plain,
    ( spl7_10
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f232,plain,
    ( spl7_15
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f243,plain,
    ( spl7_17
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f318,plain,
    ( spl7_24
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f388,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_24
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f387,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f387,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_24
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f375,f320])).

fof(f320,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f318])).

fof(f375,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
        | ~ r1_tarski(k1_relat_1(sK2),X1) )
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f374,f90])).

fof(f374,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ r1_tarski(k1_relat_1(sK2),X1) )
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f373,f323])).

fof(f373,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_15
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f372,f234])).

fof(f234,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f232])).

fof(f372,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1))) )
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f188,f245])).

fof(f245,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f243])).

fof(f188,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1))) )
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f182,f139])).

fof(f139,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f137])).

fof(f182,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(k2_funct_1(sK2))
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1))) )
    | ~ spl7_10 ),
    inference(resolution,[],[f155,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f155,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f334,plain,
    ( spl7_26
    | ~ spl7_3
    | ~ spl7_4
    | spl7_25 ),
    inference(avatar_split_clause,[],[f329,f322,f123,f117,f331])).

fof(f117,plain,
    ( spl7_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f329,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_3
    | ~ spl7_4
    | spl7_25 ),
    inference(subsumption_resolution,[],[f328,f125])).

fof(f328,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_3
    | spl7_25 ),
    inference(subsumption_resolution,[],[f121,f324])).

fof(f324,plain,
    ( k1_xboole_0 != sK1
    | spl7_25 ),
    inference(avatar_component_clause,[],[f322])).

fof(f121,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_3 ),
    inference(resolution,[],[f119,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f119,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f325,plain,
    ( spl7_24
    | ~ spl7_25
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f174,f162,f141,f322,f318])).

fof(f141,plain,
    ( spl7_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f162,plain,
    ( spl7_11
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f174,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f172,f164])).

fof(f164,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f162])).

fof(f172,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_7 ),
    inference(resolution,[],[f142,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f142,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f141])).

fof(f314,plain,
    ( spl7_23
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_15
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f297,f243,f232,f154,f137,f311])).

% (30823)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f311,plain,
    ( spl7_23
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f297,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_15
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f296,f234])).

fof(f296,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f192,f245])).

fof(f192,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f186,f139])).

fof(f186,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl7_10 ),
    inference(resolution,[],[f155,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f287,plain,
    ( spl7_21
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_15
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f280,f243,f232,f154,f137,f284])).

fof(f284,plain,
    ( spl7_21
  <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f280,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_15
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f279,f234])).

fof(f279,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f191,f245])).

fof(f191,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f185,f139])).

fof(f185,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl7_10 ),
    inference(resolution,[],[f155,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f246,plain,
    ( spl7_17
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f236,f141,f102,f97,f243])).

fof(f97,plain,
    ( spl7_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f102,plain,
    ( spl7_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f236,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f115,f142])).

fof(f115,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f113,f99])).

fof(f99,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f113,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl7_2 ),
    inference(resolution,[],[f104,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f104,plain,
    ( v2_funct_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f235,plain,
    ( spl7_15
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f230,f162,f141,f102,f97,f232])).

fof(f230,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f229,f164])).

fof(f229,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f114,f142])).

fof(f114,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f112,f99])).

fof(f112,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl7_2 ),
    inference(resolution,[],[f104,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f179,plain,
    ( ~ spl7_1
    | ~ spl7_7
    | spl7_10 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_7
    | spl7_10 ),
    inference(subsumption_resolution,[],[f171,f142])).

fof(f171,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl7_1
    | spl7_10 ),
    inference(subsumption_resolution,[],[f109,f156])).

fof(f156,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f109,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl7_1 ),
    inference(resolution,[],[f99,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f170,plain,
    ( ~ spl7_4
    | spl7_7 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl7_4
    | spl7_7 ),
    inference(resolution,[],[f158,f125])).

fof(f158,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_7 ),
    inference(resolution,[],[f143,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f143,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f141])).

fof(f165,plain,
    ( spl7_11
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f134,f128,f123,f162])).

fof(f128,plain,
    ( spl7_5
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f134,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f132,f125])).

fof(f132,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_5 ),
    inference(superposition,[],[f130,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f130,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f157,plain,
    ( ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f40,f154,f150,f146])).

fof(f40,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f144,plain,
    ( spl7_6
    | ~ spl7_7
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f108,f97,f141,f137])).

fof(f108,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ spl7_1 ),
    inference(resolution,[],[f99,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f131,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f45,f128])).

fof(f45,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f126,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f43,f123])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f120,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f42,f117])).

fof(f42,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f105,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f44,f102])).

fof(f44,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f100,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f41,f97])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:23:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (30810)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (30809)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (30819)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (30806)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (30809)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (30807)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (30819)Refutation not found, incomplete strategy% (30819)------------------------------
% 0.21/0.48  % (30819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30819)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (30819)Memory used [KB]: 1663
% 0.21/0.48  % (30819)Time elapsed: 0.069 s
% 0.21/0.48  % (30819)------------------------------
% 0.21/0.48  % (30819)------------------------------
% 0.21/0.49  % (30816)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (30822)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (30818)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (30812)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f524,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f100,f105,f120,f126,f131,f144,f157,f165,f170,f179,f235,f246,f287,f314,f325,f334,f394,f411,f438,f439,f440,f442,f513,f518,f523])).
% 0.21/0.49  fof(f523,plain,(
% 0.21/0.49    spl7_8 | ~spl7_25 | ~spl7_31),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f522])).
% 0.21/0.49  fof(f522,plain,(
% 0.21/0.49    $false | (spl7_8 | ~spl7_25 | ~spl7_31)),
% 0.21/0.49    inference(subsumption_resolution,[],[f521,f393])).
% 0.21/0.49  fof(f393,plain,(
% 0.21/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~spl7_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f391])).
% 0.21/0.49  fof(f391,plain,(
% 0.21/0.49    spl7_31 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.21/0.49  fof(f521,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl7_8 | ~spl7_25)),
% 0.21/0.49    inference(forward_demodulation,[],[f520,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.49  fof(f520,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl7_8 | ~spl7_25)),
% 0.21/0.49    inference(forward_demodulation,[],[f148,f323])).
% 0.21/0.49  fof(f323,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl7_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f322])).
% 0.21/0.49  fof(f322,plain,(
% 0.21/0.49    spl7_25 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl7_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f146])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    spl7_8 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.49  fof(f518,plain,(
% 0.21/0.49    ~spl7_28 | ~spl7_31 | spl7_38),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f517])).
% 0.21/0.49  fof(f517,plain,(
% 0.21/0.49    $false | (~spl7_28 | ~spl7_31 | spl7_38)),
% 0.21/0.49    inference(subsumption_resolution,[],[f516,f393])).
% 0.21/0.49  fof(f516,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (~spl7_28 | spl7_38)),
% 0.21/0.49    inference(forward_demodulation,[],[f515,f90])).
% 0.21/0.49  fof(f515,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl7_28 | spl7_38)),
% 0.21/0.49    inference(subsumption_resolution,[],[f514,f342])).
% 0.21/0.49  fof(f342,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | ~spl7_28),
% 0.21/0.49    inference(avatar_component_clause,[],[f340])).
% 0.21/0.49  fof(f340,plain,(
% 0.21/0.49    spl7_28 <=> k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.49  fof(f514,plain,(
% 0.21/0.49    k1_xboole_0 != k1_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl7_38),
% 0.21/0.49    inference(superposition,[],[f512,f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f512,plain,(
% 0.21/0.49    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | spl7_38),
% 0.21/0.49    inference(avatar_component_clause,[],[f510])).
% 0.21/0.49  fof(f510,plain,(
% 0.21/0.49    spl7_38 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 0.21/0.49  fof(f513,plain,(
% 0.21/0.49    ~spl7_38 | spl7_9 | ~spl7_25 | ~spl7_31 | spl7_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f504,f406,f391,f322,f150,f510])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    spl7_9 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.49  fof(f406,plain,(
% 0.21/0.49    spl7_32 <=> k1_xboole_0 = sK0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.21/0.49  fof(f504,plain,(
% 0.21/0.49    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | (spl7_9 | ~spl7_25 | ~spl7_31 | spl7_32)),
% 0.21/0.49    inference(subsumption_resolution,[],[f503,f393])).
% 0.21/0.49  fof(f503,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | (spl7_9 | ~spl7_25 | spl7_32)),
% 0.21/0.49    inference(forward_demodulation,[],[f502,f90])).
% 0.21/0.49  fof(f502,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | (spl7_9 | ~spl7_25 | spl7_32)),
% 0.21/0.49    inference(forward_demodulation,[],[f501,f323])).
% 0.21/0.49  fof(f501,plain,(
% 0.21/0.49    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl7_9 | ~spl7_25 | spl7_32)),
% 0.21/0.49    inference(forward_demodulation,[],[f445,f323])).
% 0.21/0.49  fof(f445,plain,(
% 0.21/0.49    sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl7_9 | spl7_32)),
% 0.21/0.49    inference(subsumption_resolution,[],[f444,f407])).
% 0.21/0.49  fof(f407,plain,(
% 0.21/0.49    k1_xboole_0 != sK0 | spl7_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f406])).
% 0.21/0.49  fof(f444,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl7_9),
% 0.21/0.49    inference(resolution,[],[f152,f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl7_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f150])).
% 0.21/0.49  fof(f442,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | sK1 != k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f440,plain,(
% 0.21/0.49    sK0 != k1_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f439,plain,(
% 0.21/0.49    sK0 != k1_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f438,plain,(
% 0.21/0.49    spl7_35 | ~spl7_4 | ~spl7_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f401,f331,f123,f435])).
% 0.21/0.49  fof(f435,plain,(
% 0.21/0.49    spl7_35 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl7_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.49  fof(f331,plain,(
% 0.21/0.49    spl7_26 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.21/0.49  fof(f401,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK2) | (~spl7_4 | ~spl7_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f399,f125])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f123])).
% 0.21/0.50  fof(f399,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_26),
% 0.21/0.50    inference(superposition,[],[f333,f79])).
% 0.21/0.50  fof(f333,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f331])).
% 0.21/0.50  fof(f411,plain,(
% 0.21/0.50    k1_xboole_0 != sK0 | k1_xboole_0 != k1_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f394,plain,(
% 0.21/0.50    spl7_31 | ~spl7_6 | ~spl7_10 | ~spl7_15 | ~spl7_17 | ~spl7_24 | ~spl7_25),
% 0.21/0.50    inference(avatar_split_clause,[],[f388,f322,f318,f243,f232,f154,f137,f391])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    spl7_6 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    spl7_10 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    spl7_15 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    spl7_17 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.50  fof(f318,plain,(
% 0.21/0.50    spl7_24 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.50  fof(f388,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (~spl7_6 | ~spl7_10 | ~spl7_15 | ~spl7_17 | ~spl7_24 | ~spl7_25)),
% 0.21/0.50    inference(subsumption_resolution,[],[f387,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.50  fof(f387,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))) ) | (~spl7_6 | ~spl7_10 | ~spl7_15 | ~spl7_17 | ~spl7_24 | ~spl7_25)),
% 0.21/0.50    inference(forward_demodulation,[],[f375,f320])).
% 0.21/0.50  fof(f320,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(sK2) | ~spl7_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f318])).
% 0.21/0.50  fof(f375,plain,(
% 0.21/0.50    ( ! [X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(sK2),X1)) ) | (~spl7_6 | ~spl7_10 | ~spl7_15 | ~spl7_17 | ~spl7_25)),
% 0.21/0.50    inference(forward_demodulation,[],[f374,f90])).
% 0.21/0.50  fof(f374,plain,(
% 0.21/0.50    ( ! [X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r1_tarski(k1_relat_1(sK2),X1)) ) | (~spl7_6 | ~spl7_10 | ~spl7_15 | ~spl7_17 | ~spl7_25)),
% 0.21/0.50    inference(forward_demodulation,[],[f373,f323])).
% 0.21/0.50  fof(f373,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | (~spl7_6 | ~spl7_10 | ~spl7_15 | ~spl7_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f372,f234])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl7_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f232])).
% 0.21/0.50  fof(f372,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1)))) ) | (~spl7_6 | ~spl7_10 | ~spl7_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f188,f245])).
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl7_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f243])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1)))) ) | (~spl7_6 | ~spl7_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f182,f139])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    v1_relat_1(k2_funct_1(sK2)) | ~spl7_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f137])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    ( ! [X1] : (~v1_relat_1(k2_funct_1(sK2)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1)))) ) | ~spl7_10),
% 0.21/0.50    inference(resolution,[],[f155,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    v1_funct_1(k2_funct_1(sK2)) | ~spl7_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f154])).
% 0.21/0.50  fof(f334,plain,(
% 0.21/0.50    spl7_26 | ~spl7_3 | ~spl7_4 | spl7_25),
% 0.21/0.50    inference(avatar_split_clause,[],[f329,f322,f123,f117,f331])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    spl7_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.50  fof(f329,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl7_3 | ~spl7_4 | spl7_25)),
% 0.21/0.50    inference(subsumption_resolution,[],[f328,f125])).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl7_3 | spl7_25)),
% 0.21/0.50    inference(subsumption_resolution,[],[f121,f324])).
% 0.21/0.50  fof(f324,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | spl7_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f322])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_3),
% 0.21/0.50    inference(resolution,[],[f119,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,sK1) | ~spl7_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f117])).
% 0.21/0.50  fof(f325,plain,(
% 0.21/0.50    spl7_24 | ~spl7_25 | ~spl7_7 | ~spl7_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f174,f162,f141,f322,f318])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    spl7_7 <=> v1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl7_11 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | k1_xboole_0 = k1_relat_1(sK2) | (~spl7_7 | ~spl7_11)),
% 0.21/0.50    inference(forward_demodulation,[],[f172,f164])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    sK1 = k2_relat_1(sK2) | ~spl7_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f162])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2) | ~spl7_7),
% 0.21/0.50    inference(resolution,[],[f142,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    v1_relat_1(sK2) | ~spl7_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f141])).
% 0.21/0.50  fof(f314,plain,(
% 0.21/0.50    spl7_23 | ~spl7_6 | ~spl7_10 | ~spl7_15 | ~spl7_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f297,f243,f232,f154,f137,f311])).
% 0.21/0.50  % (30823)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  fof(f311,plain,(
% 0.21/0.50    spl7_23 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.21/0.50  fof(f297,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl7_6 | ~spl7_10 | ~spl7_15 | ~spl7_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f296,f234])).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | (~spl7_6 | ~spl7_10 | ~spl7_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f192,f245])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | (~spl7_6 | ~spl7_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f186,f139])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl7_10),
% 0.21/0.50    inference(resolution,[],[f155,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    spl7_21 | ~spl7_6 | ~spl7_10 | ~spl7_15 | ~spl7_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f280,f243,f232,f154,f137,f284])).
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    spl7_21 <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.50  fof(f280,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | (~spl7_6 | ~spl7_10 | ~spl7_15 | ~spl7_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f279,f234])).
% 0.21/0.50  fof(f279,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | (~spl7_6 | ~spl7_10 | ~spl7_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f191,f245])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | (~spl7_6 | ~spl7_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f185,f139])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl7_10),
% 0.21/0.50    inference(resolution,[],[f155,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    spl7_17 | ~spl7_1 | ~spl7_2 | ~spl7_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f236,f141,f102,f97,f243])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl7_1 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl7_2 <=> v2_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f115,f142])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl7_1 | ~spl7_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f113,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    v1_funct_1(sK2) | ~spl7_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl7_2),
% 0.21/0.50    inference(resolution,[],[f104,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    v2_funct_1(sK2) | ~spl7_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f102])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    spl7_15 | ~spl7_1 | ~spl7_2 | ~spl7_7 | ~spl7_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f230,f162,f141,f102,f97,f232])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_7 | ~spl7_11)),
% 0.21/0.50    inference(forward_demodulation,[],[f229,f164])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f114,f142])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl7_1 | ~spl7_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f112,f99])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl7_2),
% 0.21/0.50    inference(resolution,[],[f104,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    ~spl7_1 | ~spl7_7 | spl7_10),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f178])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    $false | (~spl7_1 | ~spl7_7 | spl7_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f171,f142])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | (~spl7_1 | spl7_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f109,f156])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    ~v1_funct_1(k2_funct_1(sK2)) | spl7_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f154])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl7_1),
% 0.21/0.50    inference(resolution,[],[f99,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    ~spl7_4 | spl7_7),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f167])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    $false | (~spl7_4 | spl7_7)),
% 0.21/0.50    inference(resolution,[],[f158,f125])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_7),
% 0.21/0.50    inference(resolution,[],[f143,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | spl7_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f141])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    spl7_11 | ~spl7_4 | ~spl7_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f134,f128,f123,f162])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    spl7_5 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    sK1 = k2_relat_1(sK2) | (~spl7_4 | ~spl7_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f132,f125])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_5),
% 0.21/0.50    inference(superposition,[],[f130,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl7_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f128])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    ~spl7_8 | ~spl7_9 | ~spl7_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f40,f154,f150,f146])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f20])).
% 0.21/0.50  fof(f20,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    spl7_6 | ~spl7_7 | ~spl7_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f108,f97,f141,f137])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~spl7_1),
% 0.21/0.50    inference(resolution,[],[f99,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl7_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f128])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl7_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f123])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl7_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f117])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl7_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f44,f102])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    v2_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl7_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f41,f97])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (30809)------------------------------
% 0.21/0.50  % (30809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30809)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (30809)Memory used [KB]: 10874
% 0.21/0.50  % (30809)Time elapsed: 0.055 s
% 0.21/0.50  % (30809)------------------------------
% 0.21/0.50  % (30809)------------------------------
% 0.21/0.50  % (30811)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (30805)Success in time 0.135 s
%------------------------------------------------------------------------------
