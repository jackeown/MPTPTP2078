%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 225 expanded)
%              Number of leaves         :   26 (  78 expanded)
%              Depth                    :   13
%              Number of atoms          :  331 ( 660 expanded)
%              Number of equality atoms :   87 ( 165 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f368,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f79,f83,f105,f132,f237,f243,f323,f329,f334,f336,f337,f343,f365,f367])).

fof(f367,plain,
    ( spl1_16
    | ~ spl1_18 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | spl1_16
    | ~ spl1_18 ),
    inference(subsumption_resolution,[],[f342,f364])).

fof(f364,plain,
    ( ! [X8] : v1_funct_2(sK0,k1_xboole_0,X8)
    | ~ spl1_18 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl1_18
  <=> ! [X8] : v1_funct_2(sK0,k1_xboole_0,X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f342,plain,
    ( ~ v1_funct_2(sK0,k1_xboole_0,k1_xboole_0)
    | spl1_16 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl1_16
  <=> v1_funct_2(sK0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f365,plain,
    ( spl1_18
    | ~ spl1_12
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f352,f127,f235,f363])).

fof(f235,plain,
    ( spl1_12
  <=> m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f127,plain,
    ( spl1_9
  <=> k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f352,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(sK0,k1_xboole_0,X8) )
    | ~ spl1_9 ),
    inference(trivial_inequality_removal,[],[f349])).

fof(f349,plain,
    ( ! [X8] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(sK0,k1_xboole_0,X8) )
    | ~ spl1_9 ),
    inference(superposition,[],[f189,f128])).

fof(f128,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f189,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X1,k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f187,f62])).

fof(f62,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f187,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f98,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f98,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f66,f62])).

fof(f66,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f343,plain,
    ( ~ spl1_16
    | spl1_2
    | ~ spl1_9
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f339,f130,f127,f72,f341])).

fof(f72,plain,
    ( spl1_2
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f130,plain,
    ( spl1_10
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f339,plain,
    ( ~ v1_funct_2(sK0,k1_xboole_0,k1_xboole_0)
    | spl1_2
    | ~ spl1_9
    | ~ spl1_10 ),
    inference(forward_demodulation,[],[f338,f128])).

fof(f338,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl1_2
    | ~ spl1_10 ),
    inference(forward_demodulation,[],[f73,f322])).

fof(f322,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f73,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f337,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f336,plain,(
    spl1_15 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | spl1_15 ),
    inference(resolution,[],[f333,f88])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f43,f41])).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f333,plain,
    ( ~ m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(k2_relat_1(sK0)))
    | spl1_15 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl1_15
  <=> m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f334,plain,
    ( ~ spl1_15
    | spl1_14 ),
    inference(avatar_split_clause,[],[f330,f327,f332])).

fof(f327,plain,
    ( spl1_14
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f330,plain,
    ( ~ m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(k2_relat_1(sK0)))
    | spl1_14 ),
    inference(resolution,[],[f328,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f328,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | spl1_14 ),
    inference(avatar_component_clause,[],[f327])).

fof(f329,plain,
    ( ~ spl1_14
    | spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f325,f81,f75,f327])).

fof(f75,plain,
    ( spl1_3
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f81,plain,
    ( spl1_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f325,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | spl1_3
    | ~ spl1_4 ),
    inference(resolution,[],[f76,f229])).

fof(f229,plain,
    ( ! [X0] :
        ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),X0)))
        | ~ r1_tarski(k2_relat_1(sK0),X0) )
    | ~ spl1_4 ),
    inference(resolution,[],[f228,f88])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_relat_1(sK0),k1_zfmisc_1(X1))
        | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r1_tarski(k2_relat_1(sK0),X0) )
    | ~ spl1_4 ),
    inference(resolution,[],[f227,f49])).

fof(f227,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(sK0),X1)
        | ~ r1_tarski(k2_relat_1(sK0),X0)
        | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl1_4 ),
    inference(resolution,[],[f53,f82])).

fof(f82,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f76,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f323,plain,
    ( spl1_2
    | spl1_10
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f320,f81,f130,f72])).

fof(f320,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_4 ),
    inference(resolution,[],[f319,f88])).

fof(f319,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(X0))
        | k1_xboole_0 = X0
        | v1_funct_2(sK0,k1_relat_1(sK0),X0) )
    | ~ spl1_4 ),
    inference(resolution,[],[f316,f49])).

fof(f316,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK0),X0)
        | v1_funct_2(sK0,k1_relat_1(sK0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_4 ),
    inference(resolution,[],[f315,f229])).

fof(f315,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
      | k1_xboole_0 = X1
      | v1_funct_2(X0,k1_relat_1(X0),X1) ) ),
    inference(equality_resolution,[],[f314])).

fof(f314,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f57,f54])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f243,plain,
    ( ~ spl1_13
    | spl1_11 ),
    inference(avatar_split_clause,[],[f239,f232,f241])).

fof(f241,plain,
    ( spl1_13
  <=> m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f232,plain,
    ( spl1_11
  <=> r1_tarski(k2_relat_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f239,plain,
    ( ~ m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | spl1_11 ),
    inference(resolution,[],[f233,f49])).

fof(f233,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_xboole_0)
    | spl1_11 ),
    inference(avatar_component_clause,[],[f232])).

fof(f237,plain,
    ( ~ spl1_11
    | spl1_12
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f230,f81,f235,f232])).

fof(f230,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(sK0),k1_xboole_0)
    | ~ spl1_4 ),
    inference(superposition,[],[f229,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f132,plain,
    ( spl1_9
    | ~ spl1_10
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f125,f81,f130,f127])).

fof(f125,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(resolution,[],[f45,f82])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f105,plain,(
    spl1_7 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl1_7 ),
    inference(resolution,[],[f95,f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f95,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl1_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl1_7
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f83,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f37,f81])).

fof(f37,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
        | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
        | ~ v1_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f79,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f69,plain,
    ( spl1_1
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f38,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f39,f75,f72,f69])).

fof(f39,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:11:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (13554)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (13561)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (13566)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.48  % (13553)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (13566)Refutation not found, incomplete strategy% (13566)------------------------------
% 0.20/0.48  % (13566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (13560)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (13547)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (13547)Refutation not found, incomplete strategy% (13547)------------------------------
% 0.20/0.49  % (13547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (13547)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (13547)Memory used [KB]: 6140
% 0.20/0.49  % (13547)Time elapsed: 0.071 s
% 0.20/0.49  % (13547)------------------------------
% 0.20/0.49  % (13547)------------------------------
% 0.20/0.49  % (13560)Refutation not found, incomplete strategy% (13560)------------------------------
% 0.20/0.49  % (13560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (13560)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (13560)Memory used [KB]: 1663
% 0.20/0.49  % (13560)Time elapsed: 0.072 s
% 0.20/0.49  % (13560)------------------------------
% 0.20/0.49  % (13560)------------------------------
% 0.20/0.49  % (13548)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (13566)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (13566)Memory used [KB]: 6140
% 0.20/0.49  % (13566)Time elapsed: 0.073 s
% 0.20/0.49  % (13566)------------------------------
% 0.20/0.49  % (13566)------------------------------
% 0.20/0.49  % (13548)Refutation not found, incomplete strategy% (13548)------------------------------
% 0.20/0.49  % (13548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (13548)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (13548)Memory used [KB]: 10618
% 0.20/0.49  % (13548)Time elapsed: 0.083 s
% 0.20/0.49  % (13548)------------------------------
% 0.20/0.49  % (13548)------------------------------
% 0.20/0.49  % (13562)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (13562)Refutation not found, incomplete strategy% (13562)------------------------------
% 0.20/0.50  % (13562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13562)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (13562)Memory used [KB]: 6140
% 0.20/0.50  % (13562)Time elapsed: 0.087 s
% 0.20/0.50  % (13562)------------------------------
% 0.20/0.50  % (13562)------------------------------
% 0.20/0.50  % (13549)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (13563)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  % (13551)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (13550)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (13552)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (13550)Refutation not found, incomplete strategy% (13550)------------------------------
% 0.20/0.50  % (13550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13550)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (13550)Memory used [KB]: 10618
% 0.20/0.50  % (13550)Time elapsed: 0.094 s
% 0.20/0.50  % (13550)------------------------------
% 0.20/0.50  % (13550)------------------------------
% 0.20/0.50  % (13553)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f368,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f77,f79,f83,f105,f132,f237,f243,f323,f329,f334,f336,f337,f343,f365,f367])).
% 0.20/0.50  fof(f367,plain,(
% 0.20/0.50    spl1_16 | ~spl1_18),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f366])).
% 0.20/0.50  fof(f366,plain,(
% 0.20/0.50    $false | (spl1_16 | ~spl1_18)),
% 0.20/0.50    inference(subsumption_resolution,[],[f342,f364])).
% 0.20/0.50  fof(f364,plain,(
% 0.20/0.50    ( ! [X8] : (v1_funct_2(sK0,k1_xboole_0,X8)) ) | ~spl1_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f363])).
% 0.20/0.50  fof(f363,plain,(
% 0.20/0.50    spl1_18 <=> ! [X8] : v1_funct_2(sK0,k1_xboole_0,X8)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.20/0.50  fof(f342,plain,(
% 0.20/0.50    ~v1_funct_2(sK0,k1_xboole_0,k1_xboole_0) | spl1_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f341])).
% 0.20/0.50  fof(f341,plain,(
% 0.20/0.50    spl1_16 <=> v1_funct_2(sK0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.20/0.50  fof(f365,plain,(
% 0.20/0.50    spl1_18 | ~spl1_12 | ~spl1_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f352,f127,f235,f363])).
% 0.20/0.50  fof(f235,plain,(
% 0.20/0.50    spl1_12 <=> m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    spl1_9 <=> k1_xboole_0 = k1_relat_1(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.20/0.50  fof(f352,plain,(
% 0.20/0.50    ( ! [X8] : (~m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(sK0,k1_xboole_0,X8)) ) | ~spl1_9),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f349])).
% 0.20/0.50  fof(f349,plain,(
% 0.20/0.50    ( ! [X8] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(sK0,k1_xboole_0,X8)) ) | ~spl1_9),
% 0.20/0.50    inference(superposition,[],[f189,f128])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(sK0) | ~spl1_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f127])).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f188])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f187,f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.50    inference(flattening,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.20/0.50    inference(superposition,[],[f98,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f66,f62])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.50  fof(f343,plain,(
% 0.20/0.50    ~spl1_16 | spl1_2 | ~spl1_9 | ~spl1_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f339,f130,f127,f72,f341])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    spl1_2 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    spl1_10 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.20/0.50  fof(f339,plain,(
% 0.20/0.50    ~v1_funct_2(sK0,k1_xboole_0,k1_xboole_0) | (spl1_2 | ~spl1_9 | ~spl1_10)),
% 0.20/0.50    inference(forward_demodulation,[],[f338,f128])).
% 0.20/0.50  fof(f338,plain,(
% 0.20/0.50    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | (spl1_2 | ~spl1_10)),
% 0.20/0.50    inference(forward_demodulation,[],[f73,f322])).
% 0.20/0.50  fof(f322,plain,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(sK0) | ~spl1_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f130])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl1_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f72])).
% 0.20/0.50  fof(f337,plain,(
% 0.20/0.50    k1_xboole_0 != k2_relat_1(sK0) | m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f336,plain,(
% 0.20/0.50    spl1_15),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f335])).
% 0.20/0.50  fof(f335,plain,(
% 0.20/0.50    $false | spl1_15),
% 0.20/0.50    inference(resolution,[],[f333,f88])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f43,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.50  fof(f333,plain,(
% 0.20/0.50    ~m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(k2_relat_1(sK0))) | spl1_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f332])).
% 0.20/0.50  fof(f332,plain,(
% 0.20/0.50    spl1_15 <=> m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(k2_relat_1(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.20/0.50  fof(f334,plain,(
% 0.20/0.50    ~spl1_15 | spl1_14),
% 0.20/0.50    inference(avatar_split_clause,[],[f330,f327,f332])).
% 0.20/0.50  fof(f327,plain,(
% 0.20/0.50    spl1_14 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.20/0.50  fof(f330,plain,(
% 0.20/0.50    ~m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(k2_relat_1(sK0))) | spl1_14),
% 0.20/0.50    inference(resolution,[],[f328,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.20/0.50    inference(unused_predicate_definition_removal,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.50  fof(f328,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | spl1_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f327])).
% 0.20/0.50  fof(f329,plain,(
% 0.20/0.50    ~spl1_14 | spl1_3 | ~spl1_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f325,f81,f75,f327])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    spl1_3 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    spl1_4 <=> v1_relat_1(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.50  fof(f325,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | (spl1_3 | ~spl1_4)),
% 0.20/0.50    inference(resolution,[],[f76,f229])).
% 0.20/0.50  fof(f229,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),X0))) | ~r1_tarski(k2_relat_1(sK0),X0)) ) | ~spl1_4),
% 0.20/0.50    inference(resolution,[],[f228,f88])).
% 0.20/0.50  fof(f228,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(k1_relat_1(sK0),k1_zfmisc_1(X1)) | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(k2_relat_1(sK0),X0)) ) | ~spl1_4),
% 0.20/0.50    inference(resolution,[],[f227,f49])).
% 0.20/0.50  fof(f227,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK0),X1) | ~r1_tarski(k2_relat_1(sK0),X0) | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl1_4),
% 0.20/0.50    inference(resolution,[],[f53,f82])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    v1_relat_1(sK0) | ~spl1_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f81])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl1_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f75])).
% 0.20/0.50  fof(f323,plain,(
% 0.20/0.50    spl1_2 | spl1_10 | ~spl1_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f320,f81,f130,f72])).
% 0.20/0.50  fof(f320,plain,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(sK0) | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl1_4),
% 0.20/0.50    inference(resolution,[],[f319,f88])).
% 0.20/0.50  fof(f319,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | v1_funct_2(sK0,k1_relat_1(sK0),X0)) ) | ~spl1_4),
% 0.20/0.50    inference(resolution,[],[f316,f49])).
% 0.20/0.50  fof(f316,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | v1_funct_2(sK0,k1_relat_1(sK0),X0) | k1_xboole_0 = X0) ) | ~spl1_4),
% 0.20/0.50    inference(resolution,[],[f315,f229])).
% 0.20/0.50  fof(f315,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) | k1_xboole_0 = X1 | v1_funct_2(X0,k1_relat_1(X0),X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f314])).
% 0.20/0.50  fof(f314,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f313])).
% 0.20/0.50  fof(f313,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(superposition,[],[f57,f54])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f243,plain,(
% 0.20/0.50    ~spl1_13 | spl1_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f239,f232,f241])).
% 0.20/0.50  fof(f241,plain,(
% 0.20/0.50    spl1_13 <=> m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.20/0.50  fof(f232,plain,(
% 0.20/0.50    spl1_11 <=> r1_tarski(k2_relat_1(sK0),k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.20/0.50  fof(f239,plain,(
% 0.20/0.50    ~m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | spl1_11),
% 0.20/0.50    inference(resolution,[],[f233,f49])).
% 0.20/0.50  fof(f233,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(sK0),k1_xboole_0) | spl1_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f232])).
% 0.20/0.50  fof(f237,plain,(
% 0.20/0.50    ~spl1_11 | spl1_12 | ~spl1_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f230,f81,f235,f232])).
% 0.20/0.50  fof(f230,plain,(
% 0.20/0.50    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(sK0),k1_xboole_0) | ~spl1_4),
% 0.20/0.50    inference(superposition,[],[f229,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    spl1_9 | ~spl1_10 | ~spl1_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f125,f81,f130,f127])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0) | ~spl1_4),
% 0.20/0.50    inference(resolution,[],[f45,f82])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    spl1_7),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f102])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    $false | spl1_7),
% 0.20/0.50    inference(resolution,[],[f95,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl1_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f94])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    spl1_7 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    spl1_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f37,f81])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    v1_relat_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.50    inference(negated_conjecture,[],[f15])).
% 0.20/0.50  fof(f15,conjecture,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    spl1_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f38,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    spl1_1 <=> v1_funct_1(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    v1_funct_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ~spl1_1 | ~spl1_2 | ~spl1_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f39,f75,f72,f69])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (13553)------------------------------
% 0.20/0.50  % (13553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13553)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (13553)Memory used [KB]: 10746
% 0.20/0.50  % (13553)Time elapsed: 0.039 s
% 0.20/0.50  % (13553)------------------------------
% 0.20/0.50  % (13553)------------------------------
% 0.20/0.50  % (13544)Success in time 0.145 s
%------------------------------------------------------------------------------
