%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:22 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 698 expanded)
%              Number of leaves         :   28 ( 199 expanded)
%              Depth                    :   19
%              Number of atoms          :  752 (3261 expanded)
%              Number of equality atoms :  115 ( 586 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f979,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f141,f156,f162,f168,f185,f188,f196,f328,f340,f373,f455,f645,f769,f973])).

fof(f973,plain,
    ( spl4_2
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f972])).

fof(f972,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f971,f867])).

fof(f867,plain,
    ( m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_3
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f866,f469])).

fof(f469,plain,
    ( k2_funct_1(k1_xboole_0) = k4_relat_1(k1_xboole_0)
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f167,f368])).

fof(f368,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl4_19
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f167,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl4_9
  <=> k2_funct_1(sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f866,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f652,f368])).

fof(f652,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f129,f184])).

fof(f184,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl4_11
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f129,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl4_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f971,plain,
    ( ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f970,f812])).

fof(f812,plain,
    ( ~ v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f653,f368])).

fof(f653,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f225,f184])).

fof(f225,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | spl4_2
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f126,f167])).

fof(f126,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f970,plain,
    ( v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_19 ),
    inference(trivial_inequality_removal,[],[f966])).

fof(f966,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_19 ),
    inference(superposition,[],[f117,f876])).

fof(f876,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f872,f475])).

fof(f475,plain,
    ( k1_xboole_0 = k1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f349,f368])).

fof(f349,plain,
    ( k1_xboole_0 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f311,f184])).

fof(f311,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f263,f309])).

fof(f309,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f173,f69])).

fof(f69,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f56])).

fof(f56,plain,
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

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f173,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f67,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f263,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f155,f167])).

fof(f155,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl4_7
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f872,plain,
    ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_19 ),
    inference(resolution,[],[f867,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f117,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f769,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f768])).

fof(f768,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f767,f696])).

fof(f696,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f653,f372])).

fof(f372,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl4_20
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f767,plain,
    ( v1_funct_2(k4_relat_1(sK2),k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f766,f349])).

fof(f766,plain,
    ( v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f765,f227])).

fof(f227,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f140,f167])).

fof(f140,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_5
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f765,plain,
    ( v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f763,f228])).

fof(f228,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f121,f167])).

fof(f121,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f763,plain,
    ( v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_xboole_0)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_20 ),
    inference(superposition,[],[f79,f450])).

fof(f450,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(sK2))
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f264,f385])).

fof(f385,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f384,f71])).

fof(f71,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f384,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK2))
    | ~ spl4_4
    | ~ spl4_20 ),
    inference(resolution,[],[f379,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
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

fof(f379,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f378,f135])).

fof(f135,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f378,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | ~ spl4_20 ),
    inference(resolution,[],[f375,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
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

fof(f375,plain,
    ( v4_relat_1(sK2,k1_xboole_0)
    | ~ spl4_20 ),
    inference(backward_demodulation,[],[f171,f372])).

fof(f171,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f67,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f264,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f161,f167])).

fof(f161,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl4_8
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f79,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f645,plain,
    ( spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f644])).

fof(f644,plain,
    ( $false
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f641,f532])).

fof(f532,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK0)
    | ~ spl4_4
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f531,f468])).

fof(f468,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f135,f368])).

fof(f531,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_19 ),
    inference(resolution,[],[f470,f87])).

fof(f470,plain,
    ( v4_relat_1(k1_xboole_0,sK0)
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f171,f368])).

fof(f641,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK0)
    | spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f602,f629])).

fof(f629,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f264,f368])).

fof(f602,plain,
    ( ~ r1_tarski(k2_relat_1(k4_relat_1(k1_xboole_0)),sK0)
    | spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f342,f368])).

fof(f342,plain,
    ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f341,f113])).

fof(f113,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f341,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f335,f311])).

fof(f335,plain,
    ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
    | spl4_3
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f333,f227])).

fof(f333,plain,
    ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
    | ~ v1_relat_1(k4_relat_1(sK2))
    | spl4_3
    | ~ spl4_9 ),
    inference(resolution,[],[f332,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f332,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_3
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f130,f167])).

fof(f130,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f455,plain,
    ( spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f451,f71])).

fof(f451,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_20 ),
    inference(backward_demodulation,[],[f412,f450])).

fof(f412,plain,
    ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),k1_xboole_0)
    | spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f342,f372])).

fof(f373,plain,
    ( spl4_19
    | spl4_20
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f364,f182,f370,f366])).

fof(f364,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f357,f343])).

fof(f343,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f66,f184])).

fof(f66,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f357,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl4_11 ),
    inference(resolution,[],[f344,f116])).

fof(f116,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f344,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f67,f184])).

fof(f340,plain,
    ( spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f338,f113])).

fof(f338,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f337,f311])).

fof(f337,plain,
    ( ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
    | spl4_3
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f336,f113])).

fof(f336,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
    | spl4_3
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f335,f288])).

fof(f288,plain,
    ( sK0 = k2_relat_1(k4_relat_1(sK2))
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f264,f287])).

fof(f287,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f172,f180])).

fof(f180,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl4_10
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f172,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f67,f102])).

fof(f328,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f326,f225])).

fof(f326,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f325,f288])).

fof(f325,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,k2_relat_1(k4_relat_1(sK2)))
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f324,f227])).

fof(f324,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,k2_relat_1(k4_relat_1(sK2)))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f321,f228])).

fof(f321,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,k2_relat_1(k4_relat_1(sK2)))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(superposition,[],[f79,f311])).

fof(f196,plain,
    ( spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f190,f135])).

fof(f190,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f169,f65])).

fof(f65,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f169,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(resolution,[],[f122,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f122,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f188,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f186,f86])).

fof(f86,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f186,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(subsumption_resolution,[],[f175,f136])).

fof(f136,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f175,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f67,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f185,plain,
    ( spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f176,f182,f178])).

fof(f176,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f170,f66])).

fof(f170,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f67,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f168,plain,
    ( ~ spl4_4
    | spl4_9 ),
    inference(avatar_split_clause,[],[f163,f165,f134])).

fof(f163,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f145,f65])).

fof(f145,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f68,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f68,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f162,plain,
    ( ~ spl4_4
    | spl4_8 ),
    inference(avatar_split_clause,[],[f157,f159,f134])).

fof(f157,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f144,f65])).

fof(f144,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f68,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f156,plain,
    ( ~ spl4_4
    | spl4_7 ),
    inference(avatar_split_clause,[],[f151,f153,f134])).

fof(f151,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f143,f65])).

fof(f143,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f68,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f141,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f132,f138,f134])).

fof(f132,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f65,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f131,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f70,f128,f124,f120])).

fof(f70,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 14:12:56 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.50  % (14290)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (14301)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.50  % (14295)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (14303)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (14293)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (14302)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (14294)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.18/0.52  % (14292)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.18/0.52  % (14310)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.18/0.52  % (14305)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.18/0.53  % (14311)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.18/0.53  % (14308)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.18/0.53  % (14297)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.18/0.53  % (14291)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.18/0.53  % (14309)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.18/0.54  % (14298)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.18/0.54  % (14313)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.18/0.54  % (14306)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.18/0.54  % (14300)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.18/0.54  % (14299)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.18/0.54  % (14296)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.18/0.54  % (14314)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.18/0.54  % (14307)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.36/0.54  % (14296)Refutation not found, incomplete strategy% (14296)------------------------------
% 1.36/0.54  % (14296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (14296)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (14296)Memory used [KB]: 10618
% 1.36/0.54  % (14296)Time elapsed: 0.116 s
% 1.36/0.54  % (14296)------------------------------
% 1.36/0.54  % (14296)------------------------------
% 1.36/0.54  % (14315)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.36/0.55  % (14312)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.36/0.56  % (14304)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.36/0.56  % (14291)Refutation found. Thanks to Tanya!
% 1.36/0.56  % SZS status Theorem for theBenchmark
% 1.36/0.56  % SZS output start Proof for theBenchmark
% 1.36/0.56  fof(f979,plain,(
% 1.36/0.56    $false),
% 1.36/0.56    inference(avatar_sat_refutation,[],[f131,f141,f156,f162,f168,f185,f188,f196,f328,f340,f373,f455,f645,f769,f973])).
% 1.36/0.56  fof(f973,plain,(
% 1.36/0.56    spl4_2 | ~spl4_3 | ~spl4_7 | ~spl4_9 | ~spl4_11 | ~spl4_19),
% 1.36/0.56    inference(avatar_contradiction_clause,[],[f972])).
% 1.36/0.56  fof(f972,plain,(
% 1.36/0.56    $false | (spl4_2 | ~spl4_3 | ~spl4_7 | ~spl4_9 | ~spl4_11 | ~spl4_19)),
% 1.36/0.56    inference(subsumption_resolution,[],[f971,f867])).
% 1.36/0.56  fof(f867,plain,(
% 1.36/0.56    m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl4_3 | ~spl4_9 | ~spl4_11 | ~spl4_19)),
% 1.36/0.56    inference(forward_demodulation,[],[f866,f469])).
% 1.36/0.56  fof(f469,plain,(
% 1.36/0.56    k2_funct_1(k1_xboole_0) = k4_relat_1(k1_xboole_0) | (~spl4_9 | ~spl4_19)),
% 1.36/0.56    inference(backward_demodulation,[],[f167,f368])).
% 1.36/0.56  fof(f368,plain,(
% 1.36/0.56    k1_xboole_0 = sK2 | ~spl4_19),
% 1.36/0.56    inference(avatar_component_clause,[],[f366])).
% 1.36/0.56  fof(f366,plain,(
% 1.36/0.56    spl4_19 <=> k1_xboole_0 = sK2),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.36/0.56  fof(f167,plain,(
% 1.36/0.56    k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl4_9),
% 1.36/0.56    inference(avatar_component_clause,[],[f165])).
% 1.36/0.56  fof(f165,plain,(
% 1.36/0.56    spl4_9 <=> k2_funct_1(sK2) = k4_relat_1(sK2)),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.36/0.56  fof(f866,plain,(
% 1.36/0.56    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl4_3 | ~spl4_11 | ~spl4_19)),
% 1.36/0.56    inference(forward_demodulation,[],[f652,f368])).
% 1.36/0.56  fof(f652,plain,(
% 1.36/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl4_3 | ~spl4_11)),
% 1.36/0.56    inference(forward_demodulation,[],[f129,f184])).
% 1.36/0.56  fof(f184,plain,(
% 1.36/0.56    k1_xboole_0 = sK1 | ~spl4_11),
% 1.36/0.56    inference(avatar_component_clause,[],[f182])).
% 1.36/0.56  fof(f182,plain,(
% 1.36/0.56    spl4_11 <=> k1_xboole_0 = sK1),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.36/0.56  fof(f129,plain,(
% 1.36/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_3),
% 1.36/0.56    inference(avatar_component_clause,[],[f128])).
% 1.36/0.56  fof(f128,plain,(
% 1.36/0.56    spl4_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.36/0.56  fof(f971,plain,(
% 1.36/0.56    ~m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_2 | ~spl4_3 | ~spl4_7 | ~spl4_9 | ~spl4_11 | ~spl4_19)),
% 1.36/0.56    inference(subsumption_resolution,[],[f970,f812])).
% 1.36/0.56  fof(f812,plain,(
% 1.36/0.56    ~v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | (spl4_2 | ~spl4_9 | ~spl4_11 | ~spl4_19)),
% 1.36/0.56    inference(forward_demodulation,[],[f653,f368])).
% 1.36/0.56  fof(f653,plain,(
% 1.36/0.56    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) | (spl4_2 | ~spl4_9 | ~spl4_11)),
% 1.36/0.56    inference(forward_demodulation,[],[f225,f184])).
% 1.36/0.56  fof(f225,plain,(
% 1.36/0.56    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | (spl4_2 | ~spl4_9)),
% 1.36/0.56    inference(backward_demodulation,[],[f126,f167])).
% 1.36/0.56  fof(f126,plain,(
% 1.36/0.56    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl4_2),
% 1.36/0.56    inference(avatar_component_clause,[],[f124])).
% 1.36/0.56  fof(f124,plain,(
% 1.36/0.56    spl4_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.36/0.56  fof(f970,plain,(
% 1.36/0.56    v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | ~m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl4_3 | ~spl4_7 | ~spl4_9 | ~spl4_11 | ~spl4_19)),
% 1.36/0.56    inference(trivial_inequality_removal,[],[f966])).
% 1.36/0.56  fof(f966,plain,(
% 1.36/0.56    k1_xboole_0 != k1_xboole_0 | v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | ~m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl4_3 | ~spl4_7 | ~spl4_9 | ~spl4_11 | ~spl4_19)),
% 1.36/0.56    inference(superposition,[],[f117,f876])).
% 1.36/0.56  fof(f876,plain,(
% 1.36/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0)) | (~spl4_3 | ~spl4_7 | ~spl4_9 | ~spl4_11 | ~spl4_19)),
% 1.36/0.56    inference(forward_demodulation,[],[f872,f475])).
% 1.36/0.56  fof(f475,plain,(
% 1.36/0.56    k1_xboole_0 = k1_relat_1(k4_relat_1(k1_xboole_0)) | (~spl4_7 | ~spl4_9 | ~spl4_11 | ~spl4_19)),
% 1.36/0.56    inference(backward_demodulation,[],[f349,f368])).
% 1.36/0.56  fof(f349,plain,(
% 1.36/0.56    k1_xboole_0 = k1_relat_1(k4_relat_1(sK2)) | (~spl4_7 | ~spl4_9 | ~spl4_11)),
% 1.36/0.56    inference(backward_demodulation,[],[f311,f184])).
% 1.36/0.56  fof(f311,plain,(
% 1.36/0.56    sK1 = k1_relat_1(k4_relat_1(sK2)) | (~spl4_7 | ~spl4_9)),
% 1.36/0.56    inference(backward_demodulation,[],[f263,f309])).
% 1.36/0.56  fof(f309,plain,(
% 1.36/0.56    sK1 = k2_relat_1(sK2)),
% 1.36/0.56    inference(forward_demodulation,[],[f173,f69])).
% 1.36/0.56  fof(f69,plain,(
% 1.36/0.56    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.36/0.56    inference(cnf_transformation,[],[f57])).
% 1.36/0.56  fof(f57,plain,(
% 1.36/0.56    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.36/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f56])).
% 1.36/0.56  fof(f56,plain,(
% 1.36/0.56    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.36/0.56    introduced(choice_axiom,[])).
% 1.36/0.56  fof(f29,plain,(
% 1.36/0.56    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.36/0.56    inference(flattening,[],[f28])).
% 1.36/0.56  fof(f28,plain,(
% 1.36/0.56    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.36/0.56    inference(ennf_transformation,[],[f25])).
% 1.36/0.56  fof(f25,negated_conjecture,(
% 1.36/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.36/0.56    inference(negated_conjecture,[],[f24])).
% 1.36/0.56  fof(f24,conjecture,(
% 1.36/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.36/0.56  fof(f173,plain,(
% 1.36/0.56    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.36/0.56    inference(resolution,[],[f67,f101])).
% 1.36/0.56  fof(f101,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f48])).
% 1.36/0.56  fof(f48,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.56    inference(ennf_transformation,[],[f19])).
% 1.36/0.56  fof(f19,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.36/0.56  fof(f67,plain,(
% 1.36/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.36/0.56    inference(cnf_transformation,[],[f57])).
% 1.36/0.56  fof(f263,plain,(
% 1.36/0.56    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) | (~spl4_7 | ~spl4_9)),
% 1.36/0.56    inference(forward_demodulation,[],[f155,f167])).
% 1.36/0.56  fof(f155,plain,(
% 1.36/0.56    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl4_7),
% 1.36/0.56    inference(avatar_component_clause,[],[f153])).
% 1.36/0.56  fof(f153,plain,(
% 1.36/0.56    spl4_7 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.36/0.56  fof(f872,plain,(
% 1.36/0.56    k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0)) | (~spl4_3 | ~spl4_9 | ~spl4_11 | ~spl4_19)),
% 1.36/0.56    inference(resolution,[],[f867,f102])).
% 1.36/0.56  fof(f102,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f49])).
% 1.36/0.56  fof(f49,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.56    inference(ennf_transformation,[],[f18])).
% 1.36/0.56  fof(f18,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.36/0.56  fof(f117,plain,(
% 1.36/0.56    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.36/0.56    inference(equality_resolution,[],[f108])).
% 1.36/0.56  fof(f108,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f64])).
% 1.36/0.56  fof(f64,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.56    inference(nnf_transformation,[],[f53])).
% 1.36/0.57  fof(f53,plain,(
% 1.36/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.57    inference(flattening,[],[f52])).
% 1.36/0.57  fof(f52,plain,(
% 1.36/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.57    inference(ennf_transformation,[],[f21])).
% 1.36/0.57  fof(f21,axiom,(
% 1.36/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.36/0.57  fof(f769,plain,(
% 1.36/0.57    ~spl4_1 | spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_11 | ~spl4_20),
% 1.36/0.57    inference(avatar_contradiction_clause,[],[f768])).
% 1.36/0.57  fof(f768,plain,(
% 1.36/0.57    $false | (~spl4_1 | spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_11 | ~spl4_20)),
% 1.36/0.57    inference(subsumption_resolution,[],[f767,f696])).
% 1.36/0.57  fof(f696,plain,(
% 1.36/0.57    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_9 | ~spl4_11 | ~spl4_20)),
% 1.36/0.57    inference(forward_demodulation,[],[f653,f372])).
% 1.36/0.57  fof(f372,plain,(
% 1.36/0.57    k1_xboole_0 = sK0 | ~spl4_20),
% 1.36/0.57    inference(avatar_component_clause,[],[f370])).
% 1.36/0.57  fof(f370,plain,(
% 1.36/0.57    spl4_20 <=> k1_xboole_0 = sK0),
% 1.36/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.36/0.57  fof(f767,plain,(
% 1.36/0.57    v1_funct_2(k4_relat_1(sK2),k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_11 | ~spl4_20)),
% 1.36/0.57    inference(forward_demodulation,[],[f766,f349])).
% 1.36/0.57  fof(f766,plain,(
% 1.36/0.57    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_xboole_0) | (~spl4_1 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | ~spl4_20)),
% 1.36/0.57    inference(subsumption_resolution,[],[f765,f227])).
% 1.36/0.57  fof(f227,plain,(
% 1.36/0.57    v1_relat_1(k4_relat_1(sK2)) | (~spl4_5 | ~spl4_9)),
% 1.36/0.57    inference(backward_demodulation,[],[f140,f167])).
% 1.36/0.57  fof(f140,plain,(
% 1.36/0.57    v1_relat_1(k2_funct_1(sK2)) | ~spl4_5),
% 1.36/0.57    inference(avatar_component_clause,[],[f138])).
% 1.36/0.57  fof(f138,plain,(
% 1.36/0.57    spl4_5 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.36/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.36/0.57  fof(f765,plain,(
% 1.36/0.57    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_xboole_0) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_4 | ~spl4_8 | ~spl4_9 | ~spl4_20)),
% 1.36/0.57    inference(subsumption_resolution,[],[f763,f228])).
% 1.36/0.57  fof(f228,plain,(
% 1.36/0.57    v1_funct_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_9)),
% 1.36/0.57    inference(backward_demodulation,[],[f121,f167])).
% 1.36/0.57  fof(f121,plain,(
% 1.36/0.57    v1_funct_1(k2_funct_1(sK2)) | ~spl4_1),
% 1.36/0.57    inference(avatar_component_clause,[],[f120])).
% 1.36/0.57  fof(f120,plain,(
% 1.36/0.57    spl4_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.36/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.36/0.57  fof(f763,plain,(
% 1.36/0.57    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_xboole_0) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_4 | ~spl4_8 | ~spl4_9 | ~spl4_20)),
% 1.36/0.57    inference(superposition,[],[f79,f450])).
% 1.36/0.57  fof(f450,plain,(
% 1.36/0.57    k1_xboole_0 = k2_relat_1(k4_relat_1(sK2)) | (~spl4_4 | ~spl4_8 | ~spl4_9 | ~spl4_20)),
% 1.36/0.57    inference(forward_demodulation,[],[f264,f385])).
% 1.36/0.57  fof(f385,plain,(
% 1.36/0.57    k1_xboole_0 = k1_relat_1(sK2) | (~spl4_4 | ~spl4_20)),
% 1.36/0.57    inference(subsumption_resolution,[],[f384,f71])).
% 1.36/0.57  fof(f71,plain,(
% 1.36/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f3])).
% 1.36/0.57  fof(f3,axiom,(
% 1.36/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.36/0.57  fof(f384,plain,(
% 1.36/0.57    k1_xboole_0 = k1_relat_1(sK2) | ~r1_tarski(k1_xboole_0,k1_relat_1(sK2)) | (~spl4_4 | ~spl4_20)),
% 1.36/0.57    inference(resolution,[],[f379,f92])).
% 1.36/0.57  fof(f92,plain,(
% 1.36/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f60])).
% 1.36/0.57  fof(f60,plain,(
% 1.36/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.57    inference(flattening,[],[f59])).
% 1.36/0.57  fof(f59,plain,(
% 1.36/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.57    inference(nnf_transformation,[],[f1])).
% 1.36/0.57  fof(f1,axiom,(
% 1.36/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.57  fof(f379,plain,(
% 1.36/0.57    r1_tarski(k1_relat_1(sK2),k1_xboole_0) | (~spl4_4 | ~spl4_20)),
% 1.36/0.57    inference(subsumption_resolution,[],[f378,f135])).
% 1.36/0.57  fof(f135,plain,(
% 1.36/0.57    v1_relat_1(sK2) | ~spl4_4),
% 1.36/0.57    inference(avatar_component_clause,[],[f134])).
% 1.36/0.57  fof(f134,plain,(
% 1.36/0.57    spl4_4 <=> v1_relat_1(sK2)),
% 1.36/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.36/0.57  fof(f378,plain,(
% 1.36/0.57    r1_tarski(k1_relat_1(sK2),k1_xboole_0) | ~v1_relat_1(sK2) | ~spl4_20),
% 1.36/0.57    inference(resolution,[],[f375,f87])).
% 1.36/0.57  fof(f87,plain,(
% 1.36/0.57    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f58])).
% 1.36/0.57  fof(f58,plain,(
% 1.36/0.57    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.36/0.57    inference(nnf_transformation,[],[f43])).
% 1.36/0.57  fof(f43,plain,(
% 1.36/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.36/0.57    inference(ennf_transformation,[],[f6])).
% 1.36/0.57  fof(f6,axiom,(
% 1.36/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.36/0.57  fof(f375,plain,(
% 1.36/0.57    v4_relat_1(sK2,k1_xboole_0) | ~spl4_20),
% 1.36/0.57    inference(backward_demodulation,[],[f171,f372])).
% 1.36/0.57  fof(f171,plain,(
% 1.36/0.57    v4_relat_1(sK2,sK0)),
% 1.36/0.57    inference(resolution,[],[f67,f104])).
% 1.36/0.57  fof(f104,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f51])).
% 1.36/0.57  fof(f51,plain,(
% 1.36/0.57    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.57    inference(ennf_transformation,[],[f27])).
% 1.36/0.57  fof(f27,plain,(
% 1.36/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.36/0.57    inference(pure_predicate_removal,[],[f16])).
% 1.36/0.57  fof(f16,axiom,(
% 1.36/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.36/0.57  fof(f264,plain,(
% 1.36/0.57    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | (~spl4_8 | ~spl4_9)),
% 1.36/0.57    inference(forward_demodulation,[],[f161,f167])).
% 1.36/0.57  fof(f161,plain,(
% 1.36/0.57    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl4_8),
% 1.36/0.57    inference(avatar_component_clause,[],[f159])).
% 1.36/0.57  fof(f159,plain,(
% 1.36/0.57    spl4_8 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.36/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.36/0.57  fof(f79,plain,(
% 1.36/0.57    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f36])).
% 1.36/0.57  fof(f36,plain,(
% 1.36/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.57    inference(flattening,[],[f35])).
% 1.36/0.57  fof(f35,plain,(
% 1.36/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.57    inference(ennf_transformation,[],[f23])).
% 1.36/0.57  fof(f23,axiom,(
% 1.36/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.36/0.57  fof(f645,plain,(
% 1.36/0.57    spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_19),
% 1.36/0.57    inference(avatar_contradiction_clause,[],[f644])).
% 1.36/0.57  fof(f644,plain,(
% 1.36/0.57    $false | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_19)),
% 1.36/0.57    inference(subsumption_resolution,[],[f641,f532])).
% 1.36/0.57  fof(f532,plain,(
% 1.36/0.57    r1_tarski(k1_relat_1(k1_xboole_0),sK0) | (~spl4_4 | ~spl4_19)),
% 1.36/0.57    inference(subsumption_resolution,[],[f531,f468])).
% 1.36/0.57  fof(f468,plain,(
% 1.36/0.57    v1_relat_1(k1_xboole_0) | (~spl4_4 | ~spl4_19)),
% 1.36/0.57    inference(backward_demodulation,[],[f135,f368])).
% 1.36/0.57  fof(f531,plain,(
% 1.36/0.57    r1_tarski(k1_relat_1(k1_xboole_0),sK0) | ~v1_relat_1(k1_xboole_0) | ~spl4_19),
% 1.36/0.57    inference(resolution,[],[f470,f87])).
% 1.36/0.57  fof(f470,plain,(
% 1.36/0.57    v4_relat_1(k1_xboole_0,sK0) | ~spl4_19),
% 1.36/0.57    inference(backward_demodulation,[],[f171,f368])).
% 1.36/0.57  fof(f641,plain,(
% 1.36/0.57    ~r1_tarski(k1_relat_1(k1_xboole_0),sK0) | (spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_19)),
% 1.36/0.57    inference(backward_demodulation,[],[f602,f629])).
% 1.36/0.57  fof(f629,plain,(
% 1.36/0.57    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0)) | (~spl4_8 | ~spl4_9 | ~spl4_19)),
% 1.36/0.57    inference(forward_demodulation,[],[f264,f368])).
% 1.36/0.57  fof(f602,plain,(
% 1.36/0.57    ~r1_tarski(k2_relat_1(k4_relat_1(k1_xboole_0)),sK0) | (spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_9 | ~spl4_19)),
% 1.36/0.57    inference(forward_demodulation,[],[f342,f368])).
% 1.36/0.57  fof(f342,plain,(
% 1.36/0.57    ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | (spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_9)),
% 1.36/0.57    inference(subsumption_resolution,[],[f341,f113])).
% 1.36/0.57  fof(f113,plain,(
% 1.36/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.36/0.57    inference(equality_resolution,[],[f90])).
% 1.36/0.57  fof(f90,plain,(
% 1.36/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.36/0.57    inference(cnf_transformation,[],[f60])).
% 1.36/0.57  fof(f341,plain,(
% 1.36/0.57    ~r1_tarski(sK1,sK1) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | (spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_9)),
% 1.36/0.57    inference(forward_demodulation,[],[f335,f311])).
% 1.36/0.57  fof(f335,plain,(
% 1.36/0.57    ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1) | (spl4_3 | ~spl4_5 | ~spl4_9)),
% 1.36/0.57    inference(subsumption_resolution,[],[f333,f227])).
% 1.36/0.57  fof(f333,plain,(
% 1.36/0.57    ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1) | ~v1_relat_1(k4_relat_1(sK2)) | (spl4_3 | ~spl4_9)),
% 1.36/0.57    inference(resolution,[],[f332,f100])).
% 1.36/0.57  fof(f100,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f47])).
% 1.36/0.57  fof(f47,plain,(
% 1.36/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.36/0.57    inference(flattening,[],[f46])).
% 1.36/0.57  fof(f46,plain,(
% 1.36/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.36/0.57    inference(ennf_transformation,[],[f20])).
% 1.36/0.57  fof(f20,axiom,(
% 1.36/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.36/0.57  fof(f332,plain,(
% 1.36/0.57    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl4_3 | ~spl4_9)),
% 1.36/0.57    inference(forward_demodulation,[],[f130,f167])).
% 1.36/0.57  fof(f130,plain,(
% 1.36/0.57    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_3),
% 1.36/0.57    inference(avatar_component_clause,[],[f128])).
% 1.36/0.57  fof(f455,plain,(
% 1.36/0.57    spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_20),
% 1.36/0.57    inference(avatar_contradiction_clause,[],[f454])).
% 1.36/0.57  fof(f454,plain,(
% 1.36/0.57    $false | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_20)),
% 1.36/0.57    inference(subsumption_resolution,[],[f451,f71])).
% 1.36/0.57  fof(f451,plain,(
% 1.36/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_20)),
% 1.36/0.57    inference(backward_demodulation,[],[f412,f450])).
% 1.36/0.57  fof(f412,plain,(
% 1.36/0.57    ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),k1_xboole_0) | (spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_9 | ~spl4_20)),
% 1.36/0.57    inference(forward_demodulation,[],[f342,f372])).
% 1.36/0.57  fof(f373,plain,(
% 1.36/0.57    spl4_19 | spl4_20 | ~spl4_11),
% 1.36/0.57    inference(avatar_split_clause,[],[f364,f182,f370,f366])).
% 1.36/0.57  fof(f364,plain,(
% 1.36/0.57    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl4_11),
% 1.36/0.57    inference(subsumption_resolution,[],[f357,f343])).
% 1.36/0.57  fof(f343,plain,(
% 1.36/0.57    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl4_11),
% 1.36/0.57    inference(backward_demodulation,[],[f66,f184])).
% 1.36/0.57  fof(f66,plain,(
% 1.36/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.36/0.57    inference(cnf_transformation,[],[f57])).
% 1.36/0.57  fof(f357,plain,(
% 1.36/0.57    ~v1_funct_2(sK2,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl4_11),
% 1.36/0.57    inference(resolution,[],[f344,f116])).
% 1.36/0.57  fof(f116,plain,(
% 1.36/0.57    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 1.36/0.57    inference(equality_resolution,[],[f109])).
% 1.36/0.57  fof(f109,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.57    inference(cnf_transformation,[],[f64])).
% 1.36/0.57  fof(f344,plain,(
% 1.36/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl4_11),
% 1.36/0.57    inference(backward_demodulation,[],[f67,f184])).
% 1.36/0.57  fof(f340,plain,(
% 1.36/0.57    spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10),
% 1.36/0.57    inference(avatar_contradiction_clause,[],[f339])).
% 1.36/0.57  fof(f339,plain,(
% 1.36/0.57    $false | (spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10)),
% 1.36/0.57    inference(subsumption_resolution,[],[f338,f113])).
% 1.36/0.57  fof(f338,plain,(
% 1.36/0.57    ~r1_tarski(sK1,sK1) | (spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10)),
% 1.36/0.57    inference(forward_demodulation,[],[f337,f311])).
% 1.36/0.57  fof(f337,plain,(
% 1.36/0.57    ~r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1) | (spl4_3 | ~spl4_5 | ~spl4_8 | ~spl4_9 | ~spl4_10)),
% 1.36/0.57    inference(subsumption_resolution,[],[f336,f113])).
% 1.36/0.57  fof(f336,plain,(
% 1.36/0.57    ~r1_tarski(sK0,sK0) | ~r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1) | (spl4_3 | ~spl4_5 | ~spl4_8 | ~spl4_9 | ~spl4_10)),
% 1.36/0.57    inference(forward_demodulation,[],[f335,f288])).
% 1.36/0.57  fof(f288,plain,(
% 1.36/0.57    sK0 = k2_relat_1(k4_relat_1(sK2)) | (~spl4_8 | ~spl4_9 | ~spl4_10)),
% 1.36/0.57    inference(backward_demodulation,[],[f264,f287])).
% 1.36/0.57  fof(f287,plain,(
% 1.36/0.57    sK0 = k1_relat_1(sK2) | ~spl4_10),
% 1.36/0.57    inference(forward_demodulation,[],[f172,f180])).
% 1.36/0.57  fof(f180,plain,(
% 1.36/0.57    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_10),
% 1.36/0.57    inference(avatar_component_clause,[],[f178])).
% 1.36/0.57  fof(f178,plain,(
% 1.36/0.57    spl4_10 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.36/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.36/0.57  fof(f172,plain,(
% 1.36/0.57    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.36/0.57    inference(resolution,[],[f67,f102])).
% 1.36/0.57  fof(f328,plain,(
% 1.36/0.57    ~spl4_1 | spl4_2 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10),
% 1.36/0.57    inference(avatar_contradiction_clause,[],[f327])).
% 1.36/0.57  fof(f327,plain,(
% 1.36/0.57    $false | (~spl4_1 | spl4_2 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10)),
% 1.36/0.57    inference(subsumption_resolution,[],[f326,f225])).
% 1.36/0.57  fof(f326,plain,(
% 1.36/0.57    v1_funct_2(k4_relat_1(sK2),sK1,sK0) | (~spl4_1 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10)),
% 1.36/0.57    inference(forward_demodulation,[],[f325,f288])).
% 1.36/0.57  fof(f325,plain,(
% 1.36/0.57    v1_funct_2(k4_relat_1(sK2),sK1,k2_relat_1(k4_relat_1(sK2))) | (~spl4_1 | ~spl4_5 | ~spl4_7 | ~spl4_9)),
% 1.36/0.57    inference(subsumption_resolution,[],[f324,f227])).
% 1.36/0.57  fof(f324,plain,(
% 1.36/0.57    v1_funct_2(k4_relat_1(sK2),sK1,k2_relat_1(k4_relat_1(sK2))) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_7 | ~spl4_9)),
% 1.36/0.57    inference(subsumption_resolution,[],[f321,f228])).
% 1.36/0.57  fof(f321,plain,(
% 1.36/0.57    v1_funct_2(k4_relat_1(sK2),sK1,k2_relat_1(k4_relat_1(sK2))) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_7 | ~spl4_9)),
% 1.36/0.57    inference(superposition,[],[f79,f311])).
% 1.36/0.57  fof(f196,plain,(
% 1.36/0.57    spl4_1 | ~spl4_4),
% 1.36/0.57    inference(avatar_contradiction_clause,[],[f195])).
% 1.36/0.57  fof(f195,plain,(
% 1.36/0.57    $false | (spl4_1 | ~spl4_4)),
% 1.36/0.57    inference(subsumption_resolution,[],[f190,f135])).
% 1.36/0.57  fof(f190,plain,(
% 1.36/0.57    ~v1_relat_1(sK2) | spl4_1),
% 1.36/0.57    inference(subsumption_resolution,[],[f169,f65])).
% 1.36/0.57  fof(f65,plain,(
% 1.36/0.57    v1_funct_1(sK2)),
% 1.36/0.57    inference(cnf_transformation,[],[f57])).
% 1.36/0.57  fof(f169,plain,(
% 1.36/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_1),
% 1.36/0.57    inference(resolution,[],[f122,f82])).
% 1.36/0.57  fof(f82,plain,(
% 1.36/0.57    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f38])).
% 1.36/0.57  fof(f38,plain,(
% 1.36/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.57    inference(flattening,[],[f37])).
% 1.36/0.57  fof(f37,plain,(
% 1.36/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.57    inference(ennf_transformation,[],[f13])).
% 1.36/0.57  fof(f13,axiom,(
% 1.36/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.36/0.57  fof(f122,plain,(
% 1.36/0.57    ~v1_funct_1(k2_funct_1(sK2)) | spl4_1),
% 1.36/0.57    inference(avatar_component_clause,[],[f120])).
% 1.36/0.57  fof(f188,plain,(
% 1.36/0.57    spl4_4),
% 1.36/0.57    inference(avatar_contradiction_clause,[],[f187])).
% 1.36/0.57  fof(f187,plain,(
% 1.36/0.57    $false | spl4_4),
% 1.36/0.57    inference(subsumption_resolution,[],[f186,f86])).
% 1.36/0.57  fof(f86,plain,(
% 1.36/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.36/0.57    inference(cnf_transformation,[],[f8])).
% 1.36/0.57  fof(f8,axiom,(
% 1.36/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.36/0.57  fof(f186,plain,(
% 1.36/0.57    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 1.36/0.57    inference(subsumption_resolution,[],[f175,f136])).
% 1.36/0.57  fof(f136,plain,(
% 1.36/0.57    ~v1_relat_1(sK2) | spl4_4),
% 1.36/0.57    inference(avatar_component_clause,[],[f134])).
% 1.36/0.57  fof(f175,plain,(
% 1.36/0.57    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.36/0.57    inference(resolution,[],[f67,f77])).
% 1.36/0.57  fof(f77,plain,(
% 1.36/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f34])).
% 1.36/0.57  fof(f34,plain,(
% 1.36/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.36/0.57    inference(ennf_transformation,[],[f5])).
% 1.36/0.57  fof(f5,axiom,(
% 1.36/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.36/0.57  fof(f185,plain,(
% 1.36/0.57    spl4_10 | spl4_11),
% 1.36/0.57    inference(avatar_split_clause,[],[f176,f182,f178])).
% 1.36/0.57  fof(f176,plain,(
% 1.36/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.36/0.57    inference(subsumption_resolution,[],[f170,f66])).
% 1.36/0.57  fof(f170,plain,(
% 1.36/0.57    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.36/0.57    inference(resolution,[],[f67,f105])).
% 1.36/0.57  fof(f105,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.36/0.57    inference(cnf_transformation,[],[f64])).
% 1.36/0.57  fof(f168,plain,(
% 1.36/0.57    ~spl4_4 | spl4_9),
% 1.36/0.57    inference(avatar_split_clause,[],[f163,f165,f134])).
% 1.36/0.57  fof(f163,plain,(
% 1.36/0.57    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.36/0.57    inference(subsumption_resolution,[],[f145,f65])).
% 1.36/0.57  fof(f145,plain,(
% 1.36/0.57    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.36/0.57    inference(resolution,[],[f68,f83])).
% 1.36/0.57  fof(f83,plain,(
% 1.36/0.57    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f40])).
% 1.36/0.57  fof(f40,plain,(
% 1.36/0.57    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.57    inference(flattening,[],[f39])).
% 1.36/0.57  fof(f39,plain,(
% 1.36/0.57    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.57    inference(ennf_transformation,[],[f12])).
% 1.36/0.57  fof(f12,axiom,(
% 1.36/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 1.36/0.57  fof(f68,plain,(
% 1.36/0.57    v2_funct_1(sK2)),
% 1.36/0.57    inference(cnf_transformation,[],[f57])).
% 1.36/0.57  fof(f162,plain,(
% 1.36/0.57    ~spl4_4 | spl4_8),
% 1.36/0.57    inference(avatar_split_clause,[],[f157,f159,f134])).
% 1.36/0.57  fof(f157,plain,(
% 1.36/0.57    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.36/0.57    inference(subsumption_resolution,[],[f144,f65])).
% 1.36/0.57  fof(f144,plain,(
% 1.36/0.57    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.36/0.57    inference(resolution,[],[f68,f85])).
% 1.36/0.57  fof(f85,plain,(
% 1.36/0.57    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f42])).
% 1.36/0.57  fof(f42,plain,(
% 1.36/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.57    inference(flattening,[],[f41])).
% 1.36/0.57  fof(f41,plain,(
% 1.36/0.57    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.57    inference(ennf_transformation,[],[f15])).
% 1.36/0.57  fof(f15,axiom,(
% 1.36/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.36/0.57  fof(f156,plain,(
% 1.36/0.57    ~spl4_4 | spl4_7),
% 1.36/0.57    inference(avatar_split_clause,[],[f151,f153,f134])).
% 1.36/0.57  fof(f151,plain,(
% 1.36/0.57    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.36/0.57    inference(subsumption_resolution,[],[f143,f65])).
% 1.36/0.57  fof(f143,plain,(
% 1.36/0.57    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.36/0.57    inference(resolution,[],[f68,f84])).
% 1.36/0.57  fof(f84,plain,(
% 1.36/0.57    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f42])).
% 1.36/0.57  fof(f141,plain,(
% 1.36/0.57    ~spl4_4 | spl4_5),
% 1.36/0.57    inference(avatar_split_clause,[],[f132,f138,f134])).
% 1.36/0.57  fof(f132,plain,(
% 1.36/0.57    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.36/0.57    inference(resolution,[],[f65,f81])).
% 1.36/0.57  fof(f81,plain,(
% 1.36/0.57    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f38])).
% 1.36/0.57  fof(f131,plain,(
% 1.36/0.57    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.36/0.57    inference(avatar_split_clause,[],[f70,f128,f124,f120])).
% 1.36/0.57  fof(f70,plain,(
% 1.36/0.57    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.36/0.57    inference(cnf_transformation,[],[f57])).
% 1.36/0.57  % SZS output end Proof for theBenchmark
% 1.36/0.57  % (14291)------------------------------
% 1.36/0.57  % (14291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.57  % (14291)Termination reason: Refutation
% 1.36/0.57  
% 1.36/0.57  % (14291)Memory used [KB]: 11001
% 1.36/0.57  % (14291)Time elapsed: 0.128 s
% 1.36/0.57  % (14291)------------------------------
% 1.36/0.57  % (14291)------------------------------
% 1.36/0.57  % (14289)Success in time 0.202 s
%------------------------------------------------------------------------------
