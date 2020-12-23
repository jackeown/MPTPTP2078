%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 324 expanded)
%              Number of leaves         :   43 ( 135 expanded)
%              Depth                    :   14
%              Number of atoms          :  544 (1177 expanded)
%              Number of equality atoms :  120 ( 311 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f631,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f116,f120,f124,f128,f132,f136,f162,f169,f216,f221,f232,f237,f245,f270,f294,f302,f426,f472,f478,f483,f490,f491,f526,f527,f542,f621,f630])).

fof(f630,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK1
    | sK1 != k2_relat_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f621,plain,
    ( ~ spl4_63
    | ~ spl4_62
    | spl4_64 ),
    inference(avatar_split_clause,[],[f620,f530,f515,f524])).

fof(f524,plain,
    ( spl4_63
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f515,plain,
    ( spl4_62
  <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f530,plain,
    ( spl4_64
  <=> v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f620,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_62
    | spl4_64 ),
    inference(trivial_inequality_removal,[],[f619])).

fof(f619,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_62
    | spl4_64 ),
    inference(forward_demodulation,[],[f617,f516])).

fof(f516,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f515])).

fof(f617,plain,
    ( k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_64 ),
    inference(resolution,[],[f531,f351])).

fof(f351,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_xboole_0,X0)
      | k1_xboole_0 != k1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(duplicate_literal_removal,[],[f350])).

fof(f350,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f349,f97])).

fof(f97,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f349,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f146,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f146,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f101,f97])).

fof(f101,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f531,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl4_64 ),
    inference(avatar_component_clause,[],[f530])).

fof(f542,plain,
    ( ~ spl4_64
    | spl4_2
    | ~ spl4_37
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f541,f488,f366,f107,f530])).

fof(f107,plain,
    ( spl4_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f366,plain,
    ( spl4_37
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f488,plain,
    ( spl4_54
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f541,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_37
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f540,f489])).

fof(f489,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f488])).

fof(f540,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f108,f422])).

fof(f422,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f366])).

fof(f108,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f527,plain,
    ( k1_xboole_0 != sK2
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f526,plain,
    ( ~ spl4_63
    | spl4_3
    | ~ spl4_37
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f522,f488,f366,f110,f524])).

fof(f110,plain,
    ( spl4_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f522,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_37
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f521,f489])).

fof(f521,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f520,f97])).

fof(f520,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_3
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f111,f422])).

fof(f111,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f491,plain,
    ( sK1 != k2_relat_1(sK2)
    | sK0 != k1_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f490,plain,
    ( spl4_54
    | ~ spl4_9
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f486,f463,f134,f488])).

fof(f134,plain,
    ( spl4_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f463,plain,
    ( spl4_50
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f486,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_9
    | ~ spl4_50 ),
    inference(resolution,[],[f464,f173])).

fof(f173,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X3 )
    | ~ spl4_9 ),
    inference(resolution,[],[f171,f163])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_9 ),
    inference(resolution,[],[f81,f135])).

fof(f135,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f171,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f170,f97])).

fof(f170,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_xboole_0(X0) )
    | ~ spl4_9 ),
    inference(resolution,[],[f76,f135])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f464,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f463])).

fof(f483,plain,
    ( sK1 != k2_relat_1(sK2)
    | sK0 != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f478,plain,
    ( spl4_50
    | ~ spl4_32
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f477,f366,f300,f463])).

fof(f300,plain,
    ( spl4_32
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f477,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_32
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f454,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f454,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl4_32
    | ~ spl4_37 ),
    inference(superposition,[],[f301,f422])).

fof(f301,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f300])).

fof(f472,plain,
    ( spl4_36
    | ~ spl4_30
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f470,f366,f292,f363])).

fof(f363,plain,
    ( spl4_36
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f292,plain,
    ( spl4_30
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f470,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_30
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f452,f97])).

fof(f452,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))
    | ~ spl4_30
    | ~ spl4_37 ),
    inference(superposition,[],[f293,f422])).

fof(f293,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f292])).

fof(f426,plain,
    ( ~ spl4_6
    | spl4_37
    | spl4_42
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f420,f126,f424,f366,f122])).

fof(f122,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f424,plain,
    ( spl4_42
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f126,plain,
    ( spl4_7
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f420,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(resolution,[],[f411,f127])).

fof(f127,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f411,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(X5,X3,X4)
      | k1_relat_1(X5) = X3
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(duplicate_literal_removal,[],[f407])).

fof(f407,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f88,f86])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f302,plain,
    ( ~ spl4_13
    | ~ spl4_8
    | spl4_32
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f288,f267,f300,f130,f159])).

fof(f159,plain,
    ( spl4_13
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f130,plain,
    ( spl4_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f267,plain,
    ( spl4_25
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f288,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_25 ),
    inference(superposition,[],[f70,f268])).

fof(f268,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f267])).

fof(f70,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f294,plain,
    ( spl4_30
    | ~ spl4_21
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f285,f267,f230,f292])).

fof(f230,plain,
    ( spl4_21
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f285,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl4_21
    | ~ spl4_25 ),
    inference(superposition,[],[f231,f268])).

fof(f231,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f230])).

fof(f270,plain,
    ( ~ spl4_6
    | spl4_25
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f264,f114,f267,f122])).

fof(f114,plain,
    ( spl4_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f264,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(superposition,[],[f115,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f115,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f245,plain,
    ( ~ spl4_13
    | ~ spl4_8
    | spl4_20 ),
    inference(avatar_split_clause,[],[f243,f227,f130,f159])).

fof(f227,plain,
    ( spl4_20
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f243,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_20 ),
    inference(resolution,[],[f228,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f228,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f227])).

fof(f237,plain,
    ( ~ spl4_20
    | ~ spl4_1
    | spl4_22
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f233,f219,f214,f235,f104,f227])).

fof(f104,plain,
    ( spl4_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f235,plain,
    ( spl4_22
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f214,plain,
    ( spl4_18
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f219,plain,
    ( spl4_19
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f233,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f223,f220])).

fof(f220,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f219])).

fof(f223,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_18 ),
    inference(superposition,[],[f69,f215])).

fof(f215,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f214])).

fof(f69,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f232,plain,
    ( ~ spl4_20
    | ~ spl4_1
    | spl4_21
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f225,f219,f214,f230,f104,f227])).

fof(f225,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f222,f220])).

fof(f222,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_18 ),
    inference(superposition,[],[f70,f215])).

fof(f221,plain,
    ( ~ spl4_13
    | ~ spl4_8
    | spl4_19
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f217,f118,f219,f130,f159])).

fof(f118,plain,
    ( spl4_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f217,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f74,f119])).

fof(f119,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f216,plain,
    ( ~ spl4_13
    | ~ spl4_8
    | spl4_18
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f212,f118,f214,f130,f159])).

fof(f212,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f73,f119])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f169,plain,
    ( ~ spl4_6
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl4_6
    | spl4_13 ),
    inference(subsumption_resolution,[],[f123,f167])).

fof(f167,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_13 ),
    inference(resolution,[],[f85,f160])).

fof(f160,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f159])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f123,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f162,plain,
    ( ~ spl4_13
    | ~ spl4_8
    | spl4_1 ),
    inference(avatar_split_clause,[],[f157,f104,f130,f159])).

fof(f157,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(resolution,[],[f72,f105])).

fof(f105,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f72,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f136,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f62,f134])).

fof(f62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f132,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f56,f130])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f49])).

fof(f49,plain,
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f128,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f57,f126])).

fof(f57,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f124,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f58,f122])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f120,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f59,f118])).

fof(f59,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f116,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f60,f114])).

fof(f60,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f112,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f61,f110,f107,f104])).

fof(f61,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.43  % (1967)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.44  % (1967)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f631,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f112,f116,f120,f124,f128,f132,f136,f162,f169,f216,f221,f232,f237,f245,f270,f294,f302,f426,f472,f478,f483,f490,f491,f526,f527,f542,f621,f630])).
% 0.20/0.44  fof(f630,plain,(
% 0.20/0.44    k1_xboole_0 != sK2 | k1_xboole_0 != sK1 | sK1 != k2_relat_1(sK2) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.20/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.44  fof(f621,plain,(
% 0.20/0.44    ~spl4_63 | ~spl4_62 | spl4_64),
% 0.20/0.44    inference(avatar_split_clause,[],[f620,f530,f515,f524])).
% 0.20/0.44  fof(f524,plain,(
% 0.20/0.44    spl4_63 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 0.20/0.44  fof(f515,plain,(
% 0.20/0.44    spl4_62 <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 0.20/0.44  fof(f530,plain,(
% 0.20/0.44    spl4_64 <=> v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 0.20/0.44  fof(f620,plain,(
% 0.20/0.44    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_62 | spl4_64)),
% 0.20/0.44    inference(trivial_inequality_removal,[],[f619])).
% 0.20/0.44  fof(f619,plain,(
% 0.20/0.44    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_62 | spl4_64)),
% 0.20/0.44    inference(forward_demodulation,[],[f617,f516])).
% 0.20/0.44  fof(f516,plain,(
% 0.20/0.44    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl4_62),
% 0.20/0.44    inference(avatar_component_clause,[],[f515])).
% 0.20/0.44  fof(f617,plain,(
% 0.20/0.44    k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0)) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | spl4_64),
% 0.20/0.44    inference(resolution,[],[f531,f351])).
% 0.20/0.44  fof(f351,plain,(
% 0.20/0.44    ( ! [X0,X1] : (v1_funct_2(X1,k1_xboole_0,X0) | k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.44    inference(duplicate_literal_removal,[],[f350])).
% 0.20/0.44  fof(f350,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f349,f97])).
% 0.20/0.44  fof(f97,plain,(
% 0.20/0.44    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.44    inference(equality_resolution,[],[f79])).
% 0.20/0.44  fof(f79,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f52])).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.44    inference(flattening,[],[f51])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.44    inference(nnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.44  fof(f349,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.20/0.44    inference(superposition,[],[f146,f86])).
% 0.20/0.44  fof(f86,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f43])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.44    inference(ennf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.44  fof(f146,plain,(
% 0.20/0.44    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f101,f97])).
% 0.20/0.44  fof(f101,plain,(
% 0.20/0.44    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.44    inference(equality_resolution,[],[f91])).
% 0.20/0.44  fof(f91,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f55])).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.44    inference(nnf_transformation,[],[f46])).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.44    inference(flattening,[],[f45])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.44    inference(ennf_transformation,[],[f17])).
% 0.20/0.44  fof(f17,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.44  fof(f531,plain,(
% 0.20/0.44    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | spl4_64),
% 0.20/0.44    inference(avatar_component_clause,[],[f530])).
% 0.20/0.44  fof(f542,plain,(
% 0.20/0.44    ~spl4_64 | spl4_2 | ~spl4_37 | ~spl4_54),
% 0.20/0.44    inference(avatar_split_clause,[],[f541,f488,f366,f107,f530])).
% 0.20/0.44  fof(f107,plain,(
% 0.20/0.44    spl4_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.44  fof(f366,plain,(
% 0.20/0.44    spl4_37 <=> k1_xboole_0 = sK1),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.20/0.44  fof(f488,plain,(
% 0.20/0.44    spl4_54 <=> k1_xboole_0 = sK2),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.20/0.44  fof(f541,plain,(
% 0.20/0.44    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl4_2 | ~spl4_37 | ~spl4_54)),
% 0.20/0.44    inference(forward_demodulation,[],[f540,f489])).
% 0.20/0.44  fof(f489,plain,(
% 0.20/0.44    k1_xboole_0 = sK2 | ~spl4_54),
% 0.20/0.44    inference(avatar_component_clause,[],[f488])).
% 0.20/0.44  fof(f540,plain,(
% 0.20/0.44    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl4_2 | ~spl4_37)),
% 0.20/0.44    inference(forward_demodulation,[],[f108,f422])).
% 0.20/0.44  fof(f422,plain,(
% 0.20/0.44    k1_xboole_0 = sK1 | ~spl4_37),
% 0.20/0.44    inference(avatar_component_clause,[],[f366])).
% 0.20/0.44  fof(f108,plain,(
% 0.20/0.44    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl4_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f107])).
% 0.20/0.44  fof(f527,plain,(
% 0.20/0.44    k1_xboole_0 != sK2 | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.44  fof(f526,plain,(
% 0.20/0.44    ~spl4_63 | spl4_3 | ~spl4_37 | ~spl4_54),
% 0.20/0.44    inference(avatar_split_clause,[],[f522,f488,f366,f110,f524])).
% 0.20/0.44  fof(f110,plain,(
% 0.20/0.44    spl4_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.44  fof(f522,plain,(
% 0.20/0.44    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_37 | ~spl4_54)),
% 0.20/0.44    inference(forward_demodulation,[],[f521,f489])).
% 0.20/0.44  fof(f521,plain,(
% 0.20/0.44    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_37)),
% 0.20/0.44    inference(forward_demodulation,[],[f520,f97])).
% 0.20/0.44  fof(f520,plain,(
% 0.20/0.44    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_3 | ~spl4_37)),
% 0.20/0.44    inference(forward_demodulation,[],[f111,f422])).
% 0.20/0.44  fof(f111,plain,(
% 0.20/0.44    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f110])).
% 0.20/0.44  fof(f491,plain,(
% 0.20/0.44    sK1 != k2_relat_1(sK2) | sK0 != k1_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.20/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.44  fof(f490,plain,(
% 0.20/0.44    spl4_54 | ~spl4_9 | ~spl4_50),
% 0.20/0.44    inference(avatar_split_clause,[],[f486,f463,f134,f488])).
% 0.20/0.44  fof(f134,plain,(
% 0.20/0.44    spl4_9 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.44  fof(f463,plain,(
% 0.20/0.44    spl4_50 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.20/0.44  fof(f486,plain,(
% 0.20/0.44    k1_xboole_0 = sK2 | (~spl4_9 | ~spl4_50)),
% 0.20/0.44    inference(resolution,[],[f464,f173])).
% 0.20/0.44  fof(f173,plain,(
% 0.20/0.44    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X3) ) | ~spl4_9),
% 0.20/0.44    inference(resolution,[],[f171,f163])).
% 0.20/0.44  fof(f163,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl4_9),
% 0.20/0.44    inference(resolution,[],[f81,f135])).
% 0.20/0.44  fof(f135,plain,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0) | ~spl4_9),
% 0.20/0.44    inference(avatar_component_clause,[],[f134])).
% 0.20/0.44  fof(f81,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f41])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.44  fof(f171,plain,(
% 0.20/0.44    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_9),
% 0.20/0.44    inference(forward_demodulation,[],[f170,f97])).
% 0.20/0.44  fof(f170,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(X0)) ) | ~spl4_9),
% 0.20/0.44    inference(resolution,[],[f76,f135])).
% 0.20/0.44  fof(f76,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f38])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,axiom,(
% 0.20/0.44    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.20/0.44  fof(f464,plain,(
% 0.20/0.44    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_50),
% 0.20/0.44    inference(avatar_component_clause,[],[f463])).
% 0.20/0.44  fof(f483,plain,(
% 0.20/0.44    sK1 != k2_relat_1(sK2) | sK0 != k1_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.20/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.44  fof(f478,plain,(
% 0.20/0.44    spl4_50 | ~spl4_32 | ~spl4_37),
% 0.20/0.44    inference(avatar_split_clause,[],[f477,f366,f300,f463])).
% 0.20/0.44  fof(f300,plain,(
% 0.20/0.44    spl4_32 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.20/0.44  fof(f477,plain,(
% 0.20/0.44    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl4_32 | ~spl4_37)),
% 0.20/0.44    inference(forward_demodulation,[],[f454,f96])).
% 0.20/0.44  fof(f96,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.44    inference(equality_resolution,[],[f80])).
% 0.20/0.44  fof(f80,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.44    inference(cnf_transformation,[],[f52])).
% 0.20/0.44  fof(f454,plain,(
% 0.20/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | (~spl4_32 | ~spl4_37)),
% 0.20/0.44    inference(superposition,[],[f301,f422])).
% 0.20/0.44  fof(f301,plain,(
% 0.20/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~spl4_32),
% 0.20/0.44    inference(avatar_component_clause,[],[f300])).
% 0.20/0.44  fof(f472,plain,(
% 0.20/0.44    spl4_36 | ~spl4_30 | ~spl4_37),
% 0.20/0.44    inference(avatar_split_clause,[],[f470,f366,f292,f363])).
% 0.20/0.44  fof(f363,plain,(
% 0.20/0.44    spl4_36 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.20/0.44  fof(f292,plain,(
% 0.20/0.44    spl4_30 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.20/0.44  fof(f470,plain,(
% 0.20/0.44    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (~spl4_30 | ~spl4_37)),
% 0.20/0.44    inference(forward_demodulation,[],[f452,f97])).
% 0.20/0.44  fof(f452,plain,(
% 0.20/0.44    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) | (~spl4_30 | ~spl4_37)),
% 0.20/0.44    inference(superposition,[],[f293,f422])).
% 0.20/0.44  fof(f293,plain,(
% 0.20/0.44    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~spl4_30),
% 0.20/0.44    inference(avatar_component_clause,[],[f292])).
% 0.20/0.44  fof(f426,plain,(
% 0.20/0.44    ~spl4_6 | spl4_37 | spl4_42 | ~spl4_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f420,f126,f424,f366,f122])).
% 0.20/0.44  fof(f122,plain,(
% 0.20/0.44    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.44  fof(f424,plain,(
% 0.20/0.44    spl4_42 <=> sK0 = k1_relat_1(sK2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.20/0.44  fof(f126,plain,(
% 0.20/0.44    spl4_7 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.44  fof(f420,plain,(
% 0.20/0.44    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_7),
% 0.20/0.44    inference(resolution,[],[f411,f127])).
% 0.20/0.44  fof(f127,plain,(
% 0.20/0.44    v1_funct_2(sK2,sK0,sK1) | ~spl4_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f126])).
% 0.20/0.44  fof(f411,plain,(
% 0.20/0.44    ( ! [X4,X5,X3] : (~v1_funct_2(X5,X3,X4) | k1_relat_1(X5) = X3 | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.20/0.44    inference(duplicate_literal_removal,[],[f407])).
% 0.20/0.44  fof(f407,plain,(
% 0.20/0.44    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.20/0.44    inference(superposition,[],[f88,f86])).
% 0.20/0.44  fof(f88,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f55])).
% 0.20/0.44  fof(f302,plain,(
% 0.20/0.44    ~spl4_13 | ~spl4_8 | spl4_32 | ~spl4_25),
% 0.20/0.44    inference(avatar_split_clause,[],[f288,f267,f300,f130,f159])).
% 0.20/0.44  fof(f159,plain,(
% 0.20/0.44    spl4_13 <=> v1_relat_1(sK2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.44  fof(f130,plain,(
% 0.20/0.44    spl4_8 <=> v1_funct_1(sK2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.44  fof(f267,plain,(
% 0.20/0.44    spl4_25 <=> sK1 = k2_relat_1(sK2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.44  fof(f288,plain,(
% 0.20/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_25),
% 0.20/0.44    inference(superposition,[],[f70,f268])).
% 0.20/0.44  fof(f268,plain,(
% 0.20/0.44    sK1 = k2_relat_1(sK2) | ~spl4_25),
% 0.20/0.44    inference(avatar_component_clause,[],[f267])).
% 0.20/0.44  fof(f70,plain,(
% 0.20/0.44    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(flattening,[],[f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f20])).
% 0.20/0.44  fof(f20,axiom,(
% 0.20/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.44  fof(f294,plain,(
% 0.20/0.44    spl4_30 | ~spl4_21 | ~spl4_25),
% 0.20/0.44    inference(avatar_split_clause,[],[f285,f267,f230,f292])).
% 0.20/0.44  fof(f230,plain,(
% 0.20/0.44    spl4_21 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.44  fof(f285,plain,(
% 0.20/0.44    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl4_21 | ~spl4_25)),
% 0.20/0.44    inference(superposition,[],[f231,f268])).
% 0.20/0.44  fof(f231,plain,(
% 0.20/0.44    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl4_21),
% 0.20/0.44    inference(avatar_component_clause,[],[f230])).
% 0.20/0.44  fof(f270,plain,(
% 0.20/0.44    ~spl4_6 | spl4_25 | ~spl4_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f264,f114,f267,f122])).
% 0.20/0.44  fof(f114,plain,(
% 0.20/0.44    spl4_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.44  fof(f264,plain,(
% 0.20/0.44    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.20/0.44    inference(superposition,[],[f115,f87])).
% 0.20/0.44  fof(f87,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f44])).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.44    inference(ennf_transformation,[],[f15])).
% 0.20/0.44  fof(f15,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.44  fof(f115,plain,(
% 0.20/0.44    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f114])).
% 0.20/0.44  fof(f245,plain,(
% 0.20/0.44    ~spl4_13 | ~spl4_8 | spl4_20),
% 0.20/0.44    inference(avatar_split_clause,[],[f243,f227,f130,f159])).
% 0.20/0.44  fof(f227,plain,(
% 0.20/0.44    spl4_20 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.44  fof(f243,plain,(
% 0.20/0.44    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_20),
% 0.20/0.44    inference(resolution,[],[f228,f71])).
% 0.20/0.44  fof(f71,plain,(
% 0.20/0.44    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(flattening,[],[f32])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.44  fof(f228,plain,(
% 0.20/0.44    ~v1_relat_1(k2_funct_1(sK2)) | spl4_20),
% 0.20/0.44    inference(avatar_component_clause,[],[f227])).
% 0.20/0.44  fof(f237,plain,(
% 0.20/0.44    ~spl4_20 | ~spl4_1 | spl4_22 | ~spl4_18 | ~spl4_19),
% 0.20/0.44    inference(avatar_split_clause,[],[f233,f219,f214,f235,f104,f227])).
% 0.20/0.44  fof(f104,plain,(
% 0.20/0.44    spl4_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.44  fof(f235,plain,(
% 0.20/0.44    spl4_22 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.44  fof(f214,plain,(
% 0.20/0.44    spl4_18 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.44  fof(f219,plain,(
% 0.20/0.44    spl4_19 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.44  fof(f233,plain,(
% 0.20/0.44    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_18 | ~spl4_19)),
% 0.20/0.44    inference(forward_demodulation,[],[f223,f220])).
% 0.20/0.44  fof(f220,plain,(
% 0.20/0.44    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl4_19),
% 0.20/0.44    inference(avatar_component_clause,[],[f219])).
% 0.20/0.44  fof(f223,plain,(
% 0.20/0.44    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_18),
% 0.20/0.44    inference(superposition,[],[f69,f215])).
% 0.20/0.44  fof(f215,plain,(
% 0.20/0.44    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl4_18),
% 0.20/0.44    inference(avatar_component_clause,[],[f214])).
% 0.20/0.44  fof(f69,plain,(
% 0.20/0.44    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f31])).
% 0.20/0.44  fof(f232,plain,(
% 0.20/0.44    ~spl4_20 | ~spl4_1 | spl4_21 | ~spl4_18 | ~spl4_19),
% 0.20/0.44    inference(avatar_split_clause,[],[f225,f219,f214,f230,f104,f227])).
% 0.20/0.44  fof(f225,plain,(
% 0.20/0.44    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_18 | ~spl4_19)),
% 0.20/0.44    inference(forward_demodulation,[],[f222,f220])).
% 0.20/0.44  fof(f222,plain,(
% 0.20/0.44    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_18),
% 0.20/0.44    inference(superposition,[],[f70,f215])).
% 0.20/0.44  fof(f221,plain,(
% 0.20/0.44    ~spl4_13 | ~spl4_8 | spl4_19 | ~spl4_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f217,f118,f219,f130,f159])).
% 0.20/0.44  fof(f118,plain,(
% 0.20/0.44    spl4_5 <=> v2_funct_1(sK2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.44  fof(f217,plain,(
% 0.20/0.44    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_5),
% 0.20/0.44    inference(resolution,[],[f74,f119])).
% 0.20/0.44  fof(f119,plain,(
% 0.20/0.44    v2_funct_1(sK2) | ~spl4_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f118])).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(flattening,[],[f34])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,axiom,(
% 0.20/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.44  fof(f216,plain,(
% 0.20/0.44    ~spl4_13 | ~spl4_8 | spl4_18 | ~spl4_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f212,f118,f214,f130,f159])).
% 0.20/0.44  fof(f212,plain,(
% 0.20/0.44    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_5),
% 0.20/0.44    inference(resolution,[],[f73,f119])).
% 0.20/0.44  fof(f73,plain,(
% 0.20/0.44    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f35])).
% 0.20/0.44  fof(f169,plain,(
% 0.20/0.44    ~spl4_6 | spl4_13),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f168])).
% 0.20/0.44  fof(f168,plain,(
% 0.20/0.44    $false | (~spl4_6 | spl4_13)),
% 0.20/0.44    inference(subsumption_resolution,[],[f123,f167])).
% 0.20/0.44  fof(f167,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_13),
% 0.20/0.44    inference(resolution,[],[f85,f160])).
% 0.20/0.44  fof(f160,plain,(
% 0.20/0.44    ~v1_relat_1(sK2) | spl4_13),
% 0.20/0.44    inference(avatar_component_clause,[],[f159])).
% 0.20/0.44  fof(f85,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f42])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.44    inference(ennf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.44  fof(f123,plain,(
% 0.20/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f122])).
% 0.20/0.44  fof(f162,plain,(
% 0.20/0.44    ~spl4_13 | ~spl4_8 | spl4_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f157,f104,f130,f159])).
% 0.20/0.44  fof(f157,plain,(
% 0.20/0.44    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_1),
% 0.20/0.44    inference(resolution,[],[f72,f105])).
% 0.20/0.44  fof(f105,plain,(
% 0.20/0.44    ~v1_funct_1(k2_funct_1(sK2)) | spl4_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f104])).
% 0.20/0.44  fof(f72,plain,(
% 0.20/0.44    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f33])).
% 0.20/0.44  fof(f136,plain,(
% 0.20/0.44    spl4_9),
% 0.20/0.44    inference(avatar_split_clause,[],[f62,f134])).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.44  fof(f132,plain,(
% 0.20/0.44    spl4_8),
% 0.20/0.44    inference(avatar_split_clause,[],[f56,f130])).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    v1_funct_1(sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f50])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f49])).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.44    inference(flattening,[],[f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.44    inference(ennf_transformation,[],[f22])).
% 0.20/0.44  fof(f22,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.44    inference(negated_conjecture,[],[f21])).
% 0.20/0.44  fof(f21,conjecture,(
% 0.20/0.44    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.44  fof(f128,plain,(
% 0.20/0.44    spl4_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f57,f126])).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f50])).
% 0.20/0.44  fof(f124,plain,(
% 0.20/0.44    spl4_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f58,f122])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.44    inference(cnf_transformation,[],[f50])).
% 0.20/0.44  fof(f120,plain,(
% 0.20/0.44    spl4_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f59,f118])).
% 0.20/0.44  fof(f59,plain,(
% 0.20/0.44    v2_funct_1(sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f50])).
% 0.20/0.44  fof(f116,plain,(
% 0.20/0.44    spl4_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f60,f114])).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f50])).
% 0.20/0.44  fof(f112,plain,(
% 0.20/0.44    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f61,f110,f107,f104])).
% 0.20/0.44  fof(f61,plain,(
% 0.20/0.44    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.44    inference(cnf_transformation,[],[f50])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (1967)------------------------------
% 0.20/0.44  % (1967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (1967)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (1967)Memory used [KB]: 11001
% 0.20/0.44  % (1967)Time elapsed: 0.019 s
% 0.20/0.44  % (1967)------------------------------
% 0.20/0.44  % (1967)------------------------------
% 0.20/0.45  % (1960)Success in time 0.086 s
%------------------------------------------------------------------------------
