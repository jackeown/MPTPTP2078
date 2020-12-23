%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 330 expanded)
%              Number of leaves         :   53 ( 143 expanded)
%              Depth                    :   13
%              Number of atoms          :  711 (1622 expanded)
%              Number of equality atoms :  141 ( 204 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f474,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f132,f142,f147,f152,f157,f167,f195,f209,f213,f218,f248,f267,f285,f292,f305,f310,f322,f341,f354,f397,f461,f462,f463,f470,f472])).

fof(f472,plain,
    ( sK1 != k2_funct_1(sK1)
    | sK1 != k6_partfun1(sK0)
    | k6_partfun1(sK0) != sK2
    | sK2 = k2_funct_1(sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f470,plain,
    ( ~ spl5_32
    | ~ spl5_39 ),
    inference(avatar_contradiction_clause,[],[f468])).

fof(f468,plain,
    ( $false
    | ~ spl5_32
    | ~ spl5_39 ),
    inference(subsumption_resolution,[],[f299,f375])).

fof(f375,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_39 ),
    inference(resolution,[],[f353,f87])).

fof(f87,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f353,plain,
    ( r2_hidden(sK4(sK0,sK2),sK0)
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl5_39
  <=> r2_hidden(sK4(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f299,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl5_32
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f463,plain,
    ( k1_xboole_0 != sK0
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f462,plain,
    ( sK2 != k2_funct_1(sK1)
    | k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f461,plain,
    ( ~ spl5_19
    | ~ spl5_16
    | ~ spl5_28
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9
    | spl5_51
    | spl5_52
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f452,f164,f458,f454,f149,f129,f114,f144,f119,f109,f264,f192,f206])).

fof(f206,plain,
    ( spl5_19
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f192,plain,
    ( spl5_16
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f264,plain,
    ( spl5_28
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f109,plain,
    ( spl5_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f119,plain,
    ( spl5_3
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f144,plain,
    ( spl5_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f114,plain,
    ( spl5_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f129,plain,
    ( spl5_5
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f149,plain,
    ( spl5_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f454,plain,
    ( spl5_51
  <=> sK2 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f458,plain,
    ( spl5_52
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f164,plain,
    ( spl5_12
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f452,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_2(sK1,sK0)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl5_12 ),
    inference(duplicate_literal_removal,[],[f449])).

fof(f449,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_2(sK1,sK0)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl5_12 ),
    inference(resolution,[],[f442,f166])).

fof(f166,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f164])).

fof(f442,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X0,X3),k6_partfun1(X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k2_funct_1(X0) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X0,X2,X1)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_2(X0,X1)
      | ~ v5_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f437,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f437,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,k2_relat_1(X0),k2_relat_1(X0),X1,X0,X2),k6_partfun1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = k2_relat_1(X0)
      | k2_funct_1(X0) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),X1)))
      | ~ v1_funct_2(X2,k2_relat_1(X0),X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
      | ~ v1_funct_2(X0,X1,k2_relat_1(X0))
      | ~ v1_funct_1(X0) ) ),
    inference(equality_resolution,[],[f387])).

fof(f387,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relat_1(X2) != X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_funct_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f386])).

fof(f386,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relat_1(X2) != X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_funct_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f376,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f376,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_funct_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(global_subsumption,[],[f71,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | v2_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f397,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | spl5_44
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f326,f144,f394,f124,f119,f109])).

fof(f124,plain,
    ( spl5_4
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f394,plain,
    ( spl5_44
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f326,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl5_8 ),
    inference(resolution,[],[f67,f146])).

fof(f146,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f144])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f354,plain,
    ( ~ spl5_20
    | ~ spl5_2
    | spl5_38
    | spl5_39
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f325,f319,f351,f347,f114,f215])).

fof(f215,plain,
    ( spl5_20
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f347,plain,
    ( spl5_38
  <=> k6_partfun1(sK0) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f319,plain,
    ( spl5_35
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f325,plain,
    ( r2_hidden(sK4(sK0,sK2),sK0)
    | k6_partfun1(sK0) = sK2
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_35 ),
    inference(superposition,[],[f104,f321])).

fof(f321,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f319])).

fof(f104,plain,(
    ! [X1] :
      ( r2_hidden(sK4(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_partfun1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | r2_hidden(sK4(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f93,f73])).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f93,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK4(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK4(X0,X1) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f54,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK4(X0,X1) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f341,plain,
    ( spl5_37
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f336,f302,f338])).

fof(f338,plain,
    ( spl5_37
  <=> sK1 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f302,plain,
    ( spl5_33
  <=> sK1 = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f336,plain,
    ( sK1 = k2_funct_1(sK1)
    | ~ spl5_33 ),
    inference(superposition,[],[f95,f304])).

fof(f304,plain,
    ( sK1 = k6_partfun1(sK0)
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f302])).

fof(f95,plain,(
    ! [X0] : k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f80,f73,f73])).

fof(f80,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

fof(f322,plain,
    ( ~ spl5_9
    | spl5_35
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f316,f307,f319,f149])).

fof(f307,plain,
    ( spl5_34
  <=> sK0 = k1_relset_1(sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f316,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_34 ),
    inference(superposition,[],[f309,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f309,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f307])).

fof(f310,plain,
    ( ~ spl5_2
    | ~ spl5_5
    | spl5_34
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f280,f149,f307,f129,f114])).

fof(f280,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f79,f151])).

fof(f151,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f149])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f305,plain,
    ( ~ spl5_32
    | ~ spl5_19
    | ~ spl5_1
    | spl5_33
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f293,f289,f302,f109,f206,f298])).

fof(f289,plain,
    ( spl5_31
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f293,plain,
    ( sK1 = k6_partfun1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_xboole_0(sK0)
    | ~ spl5_31 ),
    inference(superposition,[],[f274,f291])).

fof(f291,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f289])).

fof(f274,plain,(
    ! [X0] :
      ( k6_partfun1(k1_relat_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(resolution,[],[f104,f87])).

fof(f292,plain,
    ( ~ spl5_8
    | spl5_31
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f286,f282,f289,f144])).

fof(f282,plain,
    ( spl5_30
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f286,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_30 ),
    inference(superposition,[],[f284,f86])).

fof(f284,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f282])).

fof(f285,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | spl5_30
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f279,f144,f282,f119,f109])).

fof(f279,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl5_8 ),
    inference(resolution,[],[f79,f146])).

fof(f267,plain,
    ( spl5_28
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f256,f144,f124,f109,f264])).

fof(f256,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f78,f146])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f248,plain,
    ( spl5_25
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f234,f149,f245])).

fof(f245,plain,
    ( spl5_25
  <=> r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f234,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f107,f151])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f218,plain,
    ( ~ spl5_18
    | spl5_20
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f176,f149,f215,f202])).

fof(f202,plain,
    ( spl5_18
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f176,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | ~ spl5_9 ),
    inference(resolution,[],[f74,f151])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f213,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f75,f204])).

fof(f204,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f202])).

fof(f75,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f209,plain,
    ( ~ spl5_18
    | spl5_19
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f175,f144,f206,f202])).

fof(f175,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | ~ spl5_8 ),
    inference(resolution,[],[f74,f146])).

fof(f195,plain,
    ( spl5_16
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f189,f144,f192])).

fof(f189,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f90,f146])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f167,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f65,f164])).

fof(f65,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f44,f43])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v3_funct_2(X2,sK0,sK0)
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

fof(f157,plain,(
    ~ spl5_10 ),
    inference(avatar_split_clause,[],[f66,f154])).

fof(f154,plain,
    ( spl5_10
  <=> r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f66,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f152,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f64,f149])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f147,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f60,f144])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f142,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f82,f139])).

fof(f139,plain,
    ( spl5_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f82,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f132,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f62,f129])).

fof(f62,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f127,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f59,f124])).

fof(f59,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f122,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f58,f119])).

fof(f58,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f117,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f61,f114])).

fof(f61,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f112,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f57,f109])).

fof(f57,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:49:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (2377)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.44  % (2369)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.45  % (2360)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.47  % (2377)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f474,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f132,f142,f147,f152,f157,f167,f195,f209,f213,f218,f248,f267,f285,f292,f305,f310,f322,f341,f354,f397,f461,f462,f463,f470,f472])).
% 0.21/0.47  fof(f472,plain,(
% 0.21/0.47    sK1 != k2_funct_1(sK1) | sK1 != k6_partfun1(sK0) | k6_partfun1(sK0) != sK2 | sK2 = k2_funct_1(sK1)),
% 0.21/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.47  fof(f470,plain,(
% 0.21/0.47    ~spl5_32 | ~spl5_39),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f468])).
% 0.21/0.47  fof(f468,plain,(
% 0.21/0.47    $false | (~spl5_32 | ~spl5_39)),
% 0.21/0.47    inference(subsumption_resolution,[],[f299,f375])).
% 0.21/0.47  fof(f375,plain,(
% 0.21/0.47    ~v1_xboole_0(sK0) | ~spl5_39),
% 0.21/0.47    inference(resolution,[],[f353,f87])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.47    inference(rectify,[],[f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.47  fof(f353,plain,(
% 0.21/0.47    r2_hidden(sK4(sK0,sK2),sK0) | ~spl5_39),
% 0.21/0.47    inference(avatar_component_clause,[],[f351])).
% 0.21/0.47  fof(f351,plain,(
% 0.21/0.47    spl5_39 <=> r2_hidden(sK4(sK0,sK2),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.21/0.47  fof(f299,plain,(
% 0.21/0.47    v1_xboole_0(sK0) | ~spl5_32),
% 0.21/0.47    inference(avatar_component_clause,[],[f298])).
% 0.21/0.47  fof(f298,plain,(
% 0.21/0.47    spl5_32 <=> v1_xboole_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.21/0.47  fof(f463,plain,(
% 0.21/0.47    k1_xboole_0 != sK0 | v1_xboole_0(sK0) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.47  fof(f462,plain,(
% 0.21/0.47    sK2 != k2_funct_1(sK1) | k2_funct_2(sK0,sK1) != k2_funct_1(sK1) | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) | ~r2_relset_1(sK0,sK0,sK2,sK2)),
% 0.21/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.47  fof(f461,plain,(
% 0.21/0.47    ~spl5_19 | ~spl5_16 | ~spl5_28 | ~spl5_1 | ~spl5_3 | ~spl5_8 | ~spl5_2 | ~spl5_5 | ~spl5_9 | spl5_51 | spl5_52 | ~spl5_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f452,f164,f458,f454,f149,f129,f114,f144,f119,f109,f264,f192,f206])).
% 0.21/0.47  fof(f206,plain,(
% 0.21/0.47    spl5_19 <=> v1_relat_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.47  fof(f192,plain,(
% 0.21/0.47    spl5_16 <=> v5_relat_1(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.47  fof(f264,plain,(
% 0.21/0.47    spl5_28 <=> v2_funct_2(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    spl5_1 <=> v1_funct_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    spl5_3 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    spl5_8 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl5_2 <=> v1_funct_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    spl5_5 <=> v1_funct_2(sK2,sK0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    spl5_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.47  fof(f454,plain,(
% 0.21/0.47    spl5_51 <=> sK2 = k2_funct_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 0.21/0.47  fof(f458,plain,(
% 0.21/0.47    spl5_52 <=> k1_xboole_0 = sK0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    spl5_12 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.47  fof(f452,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~v2_funct_2(sK1,sK0) | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~spl5_12),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f449])).
% 0.21/0.47  fof(f449,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~v2_funct_2(sK1,sK0) | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~spl5_12),
% 0.21/0.47    inference(resolution,[],[f442,f166])).
% 0.21/0.47  fof(f166,plain,(
% 0.21/0.47    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) | ~spl5_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f164])).
% 0.21/0.47  fof(f442,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X0,X3),k6_partfun1(X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k2_funct_1(X0) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X0,X2,X1) | ~v1_funct_1(X0) | ~v2_funct_2(X0,X1) | ~v5_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(superposition,[],[f437,f84])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.21/0.47  fof(f437,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,k2_relat_1(X0),k2_relat_1(X0),X1,X0,X2),k6_partfun1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = k2_relat_1(X0) | k2_funct_1(X0) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),X1))) | ~v1_funct_2(X2,k2_relat_1(X0),X1) | ~v1_funct_1(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) | ~v1_funct_2(X0,X1,k2_relat_1(X0)) | ~v1_funct_1(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f387])).
% 0.21/0.47  fof(f387,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_relat_1(X2) != X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_funct_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f386])).
% 0.21/0.47  fof(f386,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_relat_1(X2) != X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_funct_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(superposition,[],[f376,f83])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.47  fof(f376,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_funct_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.47    inference(global_subsumption,[],[f71,f70])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.47    inference(flattening,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | v2_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.47    inference(flattening,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 0.21/0.47  fof(f397,plain,(
% 0.21/0.47    ~spl5_1 | ~spl5_3 | ~spl5_4 | spl5_44 | ~spl5_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f326,f144,f394,f124,f119,f109])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    spl5_4 <=> v3_funct_2(sK1,sK0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.47  fof(f394,plain,(
% 0.21/0.47    spl5_44 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 0.21/0.47  fof(f326,plain,(
% 0.21/0.47    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl5_8),
% 0.21/0.47    inference(resolution,[],[f67,f146])).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl5_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f144])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.47    inference(flattening,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.21/0.47  fof(f354,plain,(
% 0.21/0.47    ~spl5_20 | ~spl5_2 | spl5_38 | spl5_39 | ~spl5_35),
% 0.21/0.47    inference(avatar_split_clause,[],[f325,f319,f351,f347,f114,f215])).
% 0.21/0.47  fof(f215,plain,(
% 0.21/0.47    spl5_20 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.47  fof(f347,plain,(
% 0.21/0.47    spl5_38 <=> k6_partfun1(sK0) = sK2),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.21/0.47  fof(f319,plain,(
% 0.21/0.47    spl5_35 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.21/0.47  fof(f325,plain,(
% 0.21/0.47    r2_hidden(sK4(sK0,sK2),sK0) | k6_partfun1(sK0) = sK2 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl5_35),
% 0.21/0.47    inference(superposition,[],[f104,f321])).
% 0.21/0.47  fof(f321,plain,(
% 0.21/0.47    sK0 = k1_relat_1(sK2) | ~spl5_35),
% 0.21/0.47    inference(avatar_component_clause,[],[f319])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ( ! [X1] : (r2_hidden(sK4(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_partfun1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f98])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | r2_hidden(sK4(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f93,f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,axiom,(
% 0.21/0.47    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK4(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK4(X0,X1) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f54,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK4(X0,X1) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(rectify,[],[f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.21/0.47  fof(f341,plain,(
% 0.21/0.47    spl5_37 | ~spl5_33),
% 0.21/0.47    inference(avatar_split_clause,[],[f336,f302,f338])).
% 0.21/0.47  fof(f338,plain,(
% 0.21/0.47    spl5_37 <=> sK1 = k2_funct_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.21/0.47  fof(f302,plain,(
% 0.21/0.47    spl5_33 <=> sK1 = k6_partfun1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.21/0.47  fof(f336,plain,(
% 0.21/0.47    sK1 = k2_funct_1(sK1) | ~spl5_33),
% 0.21/0.47    inference(superposition,[],[f95,f304])).
% 0.21/0.47  fof(f304,plain,(
% 0.21/0.47    sK1 = k6_partfun1(sK0) | ~spl5_33),
% 0.21/0.47    inference(avatar_component_clause,[],[f302])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ( ! [X0] : (k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f80,f73,f73])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).
% 0.21/0.47  fof(f322,plain,(
% 0.21/0.47    ~spl5_9 | spl5_35 | ~spl5_34),
% 0.21/0.47    inference(avatar_split_clause,[],[f316,f307,f319,f149])).
% 0.21/0.47  fof(f307,plain,(
% 0.21/0.47    spl5_34 <=> sK0 = k1_relset_1(sK0,sK0,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.21/0.47  fof(f316,plain,(
% 0.21/0.47    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl5_34),
% 0.21/0.47    inference(superposition,[],[f309,f86])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.47  fof(f309,plain,(
% 0.21/0.47    sK0 = k1_relset_1(sK0,sK0,sK2) | ~spl5_34),
% 0.21/0.47    inference(avatar_component_clause,[],[f307])).
% 0.21/0.47  fof(f310,plain,(
% 0.21/0.47    ~spl5_2 | ~spl5_5 | spl5_34 | ~spl5_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f280,f149,f307,f129,f114])).
% 0.21/0.47  fof(f280,plain,(
% 0.21/0.47    sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~spl5_9),
% 0.21/0.47    inference(resolution,[],[f79,f151])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl5_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f149])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.47    inference(flattening,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 0.21/0.47  fof(f305,plain,(
% 0.21/0.47    ~spl5_32 | ~spl5_19 | ~spl5_1 | spl5_33 | ~spl5_31),
% 0.21/0.47    inference(avatar_split_clause,[],[f293,f289,f302,f109,f206,f298])).
% 0.21/0.47  fof(f289,plain,(
% 0.21/0.47    spl5_31 <=> sK0 = k1_relat_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.21/0.47  fof(f293,plain,(
% 0.21/0.47    sK1 = k6_partfun1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_xboole_0(sK0) | ~spl5_31),
% 0.21/0.47    inference(superposition,[],[f274,f291])).
% 0.21/0.47  fof(f291,plain,(
% 0.21/0.47    sK0 = k1_relat_1(sK1) | ~spl5_31),
% 0.21/0.47    inference(avatar_component_clause,[],[f289])).
% 0.21/0.47  fof(f274,plain,(
% 0.21/0.47    ( ! [X0] : (k6_partfun1(k1_relat_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(k1_relat_1(X0))) )),
% 0.21/0.47    inference(resolution,[],[f104,f87])).
% 0.21/0.47  fof(f292,plain,(
% 0.21/0.47    ~spl5_8 | spl5_31 | ~spl5_30),
% 0.21/0.47    inference(avatar_split_clause,[],[f286,f282,f289,f144])).
% 0.21/0.47  fof(f282,plain,(
% 0.21/0.47    spl5_30 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.47  fof(f286,plain,(
% 0.21/0.47    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl5_30),
% 0.21/0.47    inference(superposition,[],[f284,f86])).
% 0.21/0.47  fof(f284,plain,(
% 0.21/0.47    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl5_30),
% 0.21/0.47    inference(avatar_component_clause,[],[f282])).
% 0.21/0.47  fof(f285,plain,(
% 0.21/0.47    ~spl5_1 | ~spl5_3 | spl5_30 | ~spl5_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f279,f144,f282,f119,f109])).
% 0.21/0.47  fof(f279,plain,(
% 0.21/0.47    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl5_8),
% 0.21/0.47    inference(resolution,[],[f79,f146])).
% 0.21/0.47  fof(f267,plain,(
% 0.21/0.47    spl5_28 | ~spl5_1 | ~spl5_4 | ~spl5_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f256,f144,f124,f109,f264])).
% 0.21/0.47  fof(f256,plain,(
% 0.21/0.47    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0) | ~spl5_8),
% 0.21/0.47    inference(resolution,[],[f78,f146])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(flattening,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.21/0.47  fof(f248,plain,(
% 0.21/0.47    spl5_25 | ~spl5_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f234,f149,f245])).
% 0.21/0.47  fof(f245,plain,(
% 0.21/0.47    spl5_25 <=> r2_relset_1(sK0,sK0,sK2,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.47  fof(f234,plain,(
% 0.21/0.47    r2_relset_1(sK0,sK0,sK2,sK2) | ~spl5_9),
% 0.21/0.47    inference(resolution,[],[f107,f151])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f101])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(equality_resolution,[],[f69])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(nnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(flattening,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.47  fof(f218,plain,(
% 0.21/0.47    ~spl5_18 | spl5_20 | ~spl5_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f176,f149,f215,f202])).
% 0.21/0.47  fof(f202,plain,(
% 0.21/0.47    spl5_18 <=> v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.47  fof(f176,plain,(
% 0.21/0.47    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | ~spl5_9),
% 0.21/0.47    inference(resolution,[],[f74,f151])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.47  fof(f213,plain,(
% 0.21/0.47    spl5_18),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f210])).
% 0.21/0.47  fof(f210,plain,(
% 0.21/0.47    $false | spl5_18),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f75,f204])).
% 0.21/0.47  fof(f204,plain,(
% 0.21/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl5_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f202])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.47  fof(f209,plain,(
% 0.21/0.47    ~spl5_18 | spl5_19 | ~spl5_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f175,f144,f206,f202])).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    v1_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | ~spl5_8),
% 0.21/0.47    inference(resolution,[],[f74,f146])).
% 0.21/0.47  fof(f195,plain,(
% 0.21/0.47    spl5_16 | ~spl5_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f189,f144,f192])).
% 0.21/0.47  fof(f189,plain,(
% 0.21/0.47    v5_relat_1(sK1,sK0) | ~spl5_8),
% 0.21/0.47    inference(resolution,[],[f90,f146])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    spl5_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f65,f164])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f44,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.47    inference(flattening,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f19])).
% 0.21/0.47  fof(f19,conjecture,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    ~spl5_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f66,f154])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    spl5_10 <=> r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f45])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    spl5_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f64,f149])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f45])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    spl5_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f60,f144])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f45])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    spl5_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f82,f139])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    spl5_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    spl5_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f62,f129])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    v1_funct_2(sK2,sK0,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f45])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    spl5_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f59,f124])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    v3_funct_2(sK1,sK0,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f45])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    spl5_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f58,f119])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f45])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    spl5_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f61,f114])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f45])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    spl5_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f57,f109])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    v1_funct_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f45])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (2377)------------------------------
% 0.21/0.47  % (2377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (2377)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (2377)Memory used [KB]: 11129
% 0.21/0.47  % (2377)Time elapsed: 0.054 s
% 0.21/0.47  % (2377)------------------------------
% 0.21/0.47  % (2377)------------------------------
% 0.21/0.47  % (2352)Success in time 0.116 s
%------------------------------------------------------------------------------
