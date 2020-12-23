%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t67_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:48 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  85 expanded)
%              Number of leaves         :    9 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  137 ( 250 expanded)
%              Number of equality atoms :   41 (  83 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f73,f85,f92,f105,f110,f136])).

fof(f136,plain,
    ( ~ spl3_8
    | spl3_15
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl3_8
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f134,f91])).

fof(f91,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_8
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f134,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f128,f104])).

fof(f104,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_15
  <=> k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f128,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0
    | ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl3_16 ),
    inference(resolution,[],[f109,f57])).

fof(f57,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t67_funct_2.p',d1_funct_2)).

fof(f109,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl3_16
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f110,plain,
    ( spl3_16
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f87,f83,f67,f108])).

fof(f67,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f83,plain,
    ( spl3_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f87,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(superposition,[],[f68,f84])).

fof(f84,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f68,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f105,plain,
    ( ~ spl3_15
    | spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f86,f83,f71,f103])).

fof(f71,plain,
    ( spl3_5
  <=> k1_relset_1(sK0,sK0,sK1) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f86,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(superposition,[],[f72,f84])).

fof(f72,plain,
    ( k1_relset_1(sK0,sK0,sK1) != sK0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f92,plain,
    ( spl3_8
    | ~ spl3_0
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f88,f83,f63,f90])).

fof(f63,plain,
    ( spl3_0
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f88,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl3_0
    | ~ spl3_6 ),
    inference(superposition,[],[f64,f84])).

fof(f64,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f63])).

fof(f85,plain,
    ( spl3_6
    | ~ spl3_0
    | ~ spl3_2
    | spl3_5 ),
    inference(avatar_split_clause,[],[f79,f71,f67,f63,f83])).

fof(f79,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f78,f64])).

fof(f78,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f76,f72])).

fof(f76,plain,
    ( k1_xboole_0 = sK0
    | k1_relset_1(sK0,sK0,sK1) = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f68,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f40,f71])).

fof(f40,plain,(
    k1_relset_1(sK0,sK0,sK1) != sK0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k1_relset_1(X0,X0,X1) != X0
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k1_relset_1(X0,X0,X1) != X0
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0) )
       => k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t67_funct_2.p',t67_funct_2)).

fof(f69,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f39,f67])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f38,f63])).

fof(f38,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
