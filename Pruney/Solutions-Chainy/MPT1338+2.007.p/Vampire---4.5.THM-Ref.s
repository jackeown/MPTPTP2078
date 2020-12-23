%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 401 expanded)
%              Number of leaves         :   53 ( 169 expanded)
%              Depth                    :   13
%              Number of atoms          :  735 (1361 expanded)
%              Number of equality atoms :  156 ( 311 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f677,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f114,f131,f136,f141,f146,f151,f171,f178,f201,f216,f221,f252,f260,f283,f284,f304,f310,f341,f371,f396,f451,f461,f494,f499,f545,f556,f568,f613,f629,f672,f673])).

fof(f673,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f672,plain,
    ( ~ spl3_1
    | spl3_34
    | ~ spl3_36
    | ~ spl3_42
    | spl3_52 ),
    inference(avatar_contradiction_clause,[],[f671])).

fof(f671,plain,
    ( $false
    | ~ spl3_1
    | spl3_34
    | ~ spl3_36
    | ~ spl3_42
    | spl3_52 ),
    inference(subsumption_resolution,[],[f670,f395])).

fof(f395,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f393])).

fof(f393,plain,
    ( spl3_42
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f670,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_1
    | spl3_34
    | ~ spl3_36
    | spl3_52 ),
    inference(subsumption_resolution,[],[f669,f330])).

fof(f330,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl3_34 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl3_34
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f669,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_36
    | spl3_52 ),
    inference(resolution,[],[f500,f339])).

fof(f339,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl3_36
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f500,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),X0)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) )
    | ~ spl3_1
    | spl3_52 ),
    inference(resolution,[],[f489,f115])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ v1_funct_2(sK2,X0,X1) )
    | ~ spl3_1 ),
    inference(resolution,[],[f93,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f93,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f489,plain,
    ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | spl3_52 ),
    inference(avatar_component_clause,[],[f487])).

fof(f487,plain,
    ( spl3_52
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f629,plain,
    ( ~ spl3_13
    | ~ spl3_15
    | spl3_32 ),
    inference(avatar_contradiction_clause,[],[f628])).

fof(f628,plain,
    ( $false
    | ~ spl3_13
    | ~ spl3_15
    | spl3_32 ),
    inference(subsumption_resolution,[],[f623,f185])).

fof(f185,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl3_15
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f623,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ spl3_13
    | spl3_32 ),
    inference(subsumption_resolution,[],[f188,f309])).

fof(f309,plain,
    ( ~ v1_xboole_0(sK2)
    | spl3_32 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl3_32
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f188,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | v1_xboole_0(sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f177,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f177,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f613,plain,
    ( spl3_15
    | ~ spl3_63 ),
    inference(avatar_contradiction_clause,[],[f612])).

fof(f612,plain,
    ( $false
    | spl3_15
    | ~ spl3_63 ),
    inference(subsumption_resolution,[],[f590,f53])).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f590,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_15
    | ~ spl3_63 ),
    inference(superposition,[],[f186,f567])).

fof(f567,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_63 ),
    inference(avatar_component_clause,[],[f565])).

fof(f565,plain,
    ( spl3_63
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f186,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f184])).

fof(f568,plain,
    ( spl3_63
    | spl3_48
    | ~ spl3_54
    | ~ spl3_59 ),
    inference(avatar_split_clause,[],[f563,f542,f496,f458,f565])).

fof(f458,plain,
    ( spl3_48
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f496,plain,
    ( spl3_54
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f542,plain,
    ( spl3_59
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f563,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | spl3_48
    | ~ spl3_54
    | ~ spl3_59 ),
    inference(subsumption_resolution,[],[f512,f544])).

fof(f544,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f542])).

fof(f512,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | spl3_48
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f507,f460])).

fof(f460,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | spl3_48 ),
    inference(avatar_component_clause,[],[f458])).

fof(f507,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_54 ),
    inference(resolution,[],[f498,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f498,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f496])).

fof(f556,plain,
    ( spl3_61
    | ~ spl3_24
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f511,f496,f249,f553])).

fof(f553,plain,
    ( spl3_61
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f249,plain,
    ( spl3_24
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f511,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_24
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f503,f251])).

fof(f251,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f249])).

fof(f503,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_54 ),
    inference(resolution,[],[f498,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f545,plain,
    ( spl3_59
    | ~ spl3_1
    | ~ spl3_36
    | ~ spl3_42
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f454,f448,f393,f337,f91,f542])).

fof(f448,plain,
    ( spl3_47
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f454,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_36
    | ~ spl3_42
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f453,f339])).

fof(f453,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_42
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f452,f395])).

fof(f452,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_47 ),
    inference(superposition,[],[f117,f450])).

fof(f450,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f448])).

fof(f117,plain,
    ( ! [X4,X5] :
        ( v1_funct_2(k2_tops_2(X4,X5,sK2),X5,X4)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_2(sK2,X4,X5) )
    | ~ spl3_1 ),
    inference(resolution,[],[f93,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f499,plain,
    ( spl3_54
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_27
    | ~ spl3_36
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f485,f448,f337,f266,f175,f91,f496])).

fof(f266,plain,
    ( spl3_27
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f485,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_27
    | ~ spl3_36
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f484,f450])).

fof(f484,plain,
    ( m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_27
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f321,f339])).

fof(f321,plain,
    ( m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f320,f268])).

fof(f268,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f266])).

fof(f320,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f319,f268])).

fof(f319,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(resolution,[],[f118,f177])).

fof(f118,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_2(sK2,X6,X7)
        | m1_subset_1(k2_tops_2(X6,X7,sK2),k1_zfmisc_1(k2_zfmisc_1(X7,X6))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f93,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f494,plain,
    ( ~ spl3_52
    | spl3_53
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f417,f218,f198,f491,f487])).

fof(f491,plain,
    ( spl3_53
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f198,plain,
    ( spl3_16
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f218,plain,
    ( spl3_19
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f417,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(resolution,[],[f206,f220])).

fof(f220,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f218])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | k1_relat_1(sK2) = X0
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl3_16 ),
    inference(resolution,[],[f200,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f200,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f198])).

fof(f461,plain,
    ( ~ spl3_48
    | spl3_17
    | ~ spl3_27
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f455,f448,f266,f209,f458])).

fof(f209,plain,
    ( spl3_17
  <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f455,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | spl3_17
    | ~ spl3_27
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f294,f450])).

fof(f294,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_17
    | ~ spl3_27 ),
    inference(superposition,[],[f211,f268])).

fof(f211,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f209])).

fof(f451,plain,
    ( spl3_47
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f383,f337,f270,f266,f175,f96,f91,f448])).

fof(f96,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f270,plain,
    ( spl3_28
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f383,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f382,f268])).

fof(f382,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f381,f272])).

fof(f272,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f270])).

fof(f381,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_27
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f380,f268])).

fof(f380,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_27
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f379,f339])).

fof(f379,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f378,f268])).

fof(f378,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(resolution,[],[f122,f177])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_relset_1(X0,X1,sK2) != X1
        | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f119,f93])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_1(sK2)
        | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f98,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f98,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f396,plain,
    ( spl3_42
    | ~ spl3_13
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f293,f266,f175,f393])).

fof(f293,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_13
    | ~ spl3_27 ),
    inference(superposition,[],[f177,f268])).

fof(f371,plain,
    ( spl3_31
    | ~ spl3_34 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | spl3_31
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f365,f53])).

fof(f365,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_31
    | ~ spl3_34 ),
    inference(superposition,[],[f303,f331])).

fof(f331,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f329])).

fof(f303,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_31 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl3_31
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f341,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f310,plain,
    ( ~ spl3_32
    | spl3_31 ),
    inference(avatar_split_clause,[],[f305,f301,f307])).

fof(f305,plain,
    ( ~ v1_xboole_0(sK2)
    | spl3_31 ),
    inference(resolution,[],[f303,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f304,plain,
    ( ~ spl3_31
    | spl3_12
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f292,f266,f168,f301])).

fof(f168,plain,
    ( spl3_12
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f292,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_12
    | ~ spl3_27 ),
    inference(superposition,[],[f170,f268])).

fof(f170,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f168])).

fof(f284,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f283,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f260,plain,
    ( spl3_25
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f190,f175,f257])).

fof(f257,plain,
    ( spl3_25
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f190,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f177,f68])).

fof(f252,plain,
    ( spl3_24
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f242,f198,f96,f91,f249])).

fof(f242,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f124,f200])).

fof(f124,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f121,f93])).

fof(f121,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f98,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f221,plain,
    ( spl3_19
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f191,f175,f218])).

fof(f191,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f177,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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

fof(f216,plain,
    ( ~ spl3_17
    | ~ spl3_18
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f205,f143,f133,f213,f209])).

fof(f213,plain,
    ( spl3_18
  <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f133,plain,
    ( spl3_7
  <=> k2_struct_0(sK1) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f143,plain,
    ( spl3_9
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f205,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f204,f145])).

fof(f145,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f143])).

fof(f204,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f203,f135])).

fof(f135,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f133])).

fof(f203,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f202,f145])).

fof(f202,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f44,f135])).

fof(f44,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(f201,plain,
    ( spl3_16
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f189,f175,f198])).

fof(f189,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f177,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f178,plain,
    ( spl3_13
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f166,f143,f138,f133,f175])).

fof(f138,plain,
    ( spl3_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f166,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f160,f145])).

fof(f160,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f140,f135])).

fof(f140,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f171,plain,
    ( ~ spl3_12
    | spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f159,f133,f106,f101,f168])).

fof(f101,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f106,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f159,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f158,f103])).

fof(f103,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f158,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f157,f108])).

fof(f108,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f157,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(superposition,[],[f59,f135])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f151,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f48,f148])).

fof(f148,plain,
    ( spl3_10
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f48,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f146,plain,
    ( spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f126,f111,f143])).

fof(f111,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f126,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f113,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f113,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f141,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f47,f138])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f136,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f125,f106,f133])).

fof(f125,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f108,f57])).

fof(f131,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f46,f128])).

fof(f128,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f46,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f114,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f52,f111])).

fof(f52,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f109,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f51,f106])).

fof(f51,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f104,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f50,f101])).

fof(f50,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f99,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f49,f96])).

fof(f49,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f45,f91])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:02:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (20529)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (20536)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (20529)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f677,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f114,f131,f136,f141,f146,f151,f171,f178,f201,f216,f221,f252,f260,f283,f284,f304,f310,f341,f371,f396,f451,f461,f494,f499,f545,f556,f568,f613,f629,f672,f673])).
% 0.21/0.50  fof(f673,plain,(
% 0.21/0.50    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f672,plain,(
% 0.21/0.50    ~spl3_1 | spl3_34 | ~spl3_36 | ~spl3_42 | spl3_52),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f671])).
% 0.21/0.50  fof(f671,plain,(
% 0.21/0.50    $false | (~spl3_1 | spl3_34 | ~spl3_36 | ~spl3_42 | spl3_52)),
% 0.21/0.50    inference(subsumption_resolution,[],[f670,f395])).
% 0.21/0.50  fof(f395,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_42),
% 0.21/0.50    inference(avatar_component_clause,[],[f393])).
% 0.21/0.50  fof(f393,plain,(
% 0.21/0.50    spl3_42 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.50  fof(f670,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_1 | spl3_34 | ~spl3_36 | spl3_52)),
% 0.21/0.50    inference(subsumption_resolution,[],[f669,f330])).
% 0.21/0.50  fof(f330,plain,(
% 0.21/0.50    k1_xboole_0 != k2_relat_1(sK2) | spl3_34),
% 0.21/0.50    inference(avatar_component_clause,[],[f329])).
% 0.21/0.50  fof(f329,plain,(
% 0.21/0.50    spl3_34 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.50  fof(f669,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_1 | ~spl3_36 | spl3_52)),
% 0.21/0.50    inference(resolution,[],[f500,f339])).
% 0.21/0.50  fof(f339,plain,(
% 0.21/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_36),
% 0.21/0.50    inference(avatar_component_clause,[],[f337])).
% 0.21/0.50  fof(f337,plain,(
% 0.21/0.50    spl3_36 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.50  fof(f500,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),X0) | k1_xboole_0 = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | (~spl3_1 | spl3_52)),
% 0.21/0.50    inference(resolution,[],[f489,f115])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v1_funct_2(sK2,X0,X1)) ) | ~spl3_1),
% 0.21/0.50    inference(resolution,[],[f93,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    v1_funct_1(sK2) | ~spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl3_1 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f489,plain,(
% 0.21/0.50    ~v1_partfun1(sK2,k2_struct_0(sK0)) | spl3_52),
% 0.21/0.50    inference(avatar_component_clause,[],[f487])).
% 0.21/0.50  fof(f487,plain,(
% 0.21/0.50    spl3_52 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.21/0.50  fof(f629,plain,(
% 0.21/0.50    ~spl3_13 | ~spl3_15 | spl3_32),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f628])).
% 0.21/0.50  fof(f628,plain,(
% 0.21/0.50    $false | (~spl3_13 | ~spl3_15 | spl3_32)),
% 0.21/0.50    inference(subsumption_resolution,[],[f623,f185])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    v1_xboole_0(k2_struct_0(sK0)) | ~spl3_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f184])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    spl3_15 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.50  fof(f623,plain,(
% 0.21/0.50    ~v1_xboole_0(k2_struct_0(sK0)) | (~spl3_13 | spl3_32)),
% 0.21/0.50    inference(subsumption_resolution,[],[f188,f309])).
% 0.21/0.50  fof(f309,plain,(
% 0.21/0.50    ~v1_xboole_0(sK2) | spl3_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f307])).
% 0.21/0.50  fof(f307,plain,(
% 0.21/0.50    spl3_32 <=> v1_xboole_0(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    ~v1_xboole_0(k2_struct_0(sK0)) | v1_xboole_0(sK2) | ~spl3_13),
% 0.21/0.50    inference(resolution,[],[f177,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f175])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.50  fof(f613,plain,(
% 0.21/0.50    spl3_15 | ~spl3_63),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f612])).
% 0.21/0.50  fof(f612,plain,(
% 0.21/0.50    $false | (spl3_15 | ~spl3_63)),
% 0.21/0.50    inference(subsumption_resolution,[],[f590,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.50  fof(f590,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_xboole_0) | (spl3_15 | ~spl3_63)),
% 0.21/0.50    inference(superposition,[],[f186,f567])).
% 0.21/0.50  fof(f567,plain,(
% 0.21/0.50    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_63),
% 0.21/0.50    inference(avatar_component_clause,[],[f565])).
% 0.21/0.50  fof(f565,plain,(
% 0.21/0.50    spl3_63 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ~v1_xboole_0(k2_struct_0(sK0)) | spl3_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f184])).
% 0.21/0.50  fof(f568,plain,(
% 0.21/0.50    spl3_63 | spl3_48 | ~spl3_54 | ~spl3_59),
% 0.21/0.50    inference(avatar_split_clause,[],[f563,f542,f496,f458,f565])).
% 0.21/0.50  fof(f458,plain,(
% 0.21/0.50    spl3_48 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.21/0.50  fof(f496,plain,(
% 0.21/0.50    spl3_54 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.21/0.50  fof(f542,plain,(
% 0.21/0.50    spl3_59 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.21/0.50  fof(f563,plain,(
% 0.21/0.50    k1_xboole_0 = k2_struct_0(sK0) | (spl3_48 | ~spl3_54 | ~spl3_59)),
% 0.21/0.50    inference(subsumption_resolution,[],[f512,f544])).
% 0.21/0.50  fof(f544,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~spl3_59),
% 0.21/0.50    inference(avatar_component_clause,[],[f542])).
% 0.21/0.50  fof(f512,plain,(
% 0.21/0.50    k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | (spl3_48 | ~spl3_54)),
% 0.21/0.50    inference(subsumption_resolution,[],[f507,f460])).
% 0.21/0.50  fof(f460,plain,(
% 0.21/0.50    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | spl3_48),
% 0.21/0.50    inference(avatar_component_clause,[],[f458])).
% 0.21/0.50  fof(f507,plain,(
% 0.21/0.50    k1_xboole_0 = k2_struct_0(sK0) | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~spl3_54),
% 0.21/0.50    inference(resolution,[],[f498,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f498,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~spl3_54),
% 0.21/0.50    inference(avatar_component_clause,[],[f496])).
% 0.21/0.50  fof(f556,plain,(
% 0.21/0.50    spl3_61 | ~spl3_24 | ~spl3_54),
% 0.21/0.50    inference(avatar_split_clause,[],[f511,f496,f249,f553])).
% 0.21/0.50  fof(f553,plain,(
% 0.21/0.50    spl3_61 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    spl3_24 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.50  fof(f511,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_24 | ~spl3_54)),
% 0.21/0.50    inference(forward_demodulation,[],[f503,f251])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f249])).
% 0.21/0.50  fof(f503,plain,(
% 0.21/0.50    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~spl3_54),
% 0.21/0.50    inference(resolution,[],[f498,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f545,plain,(
% 0.21/0.50    spl3_59 | ~spl3_1 | ~spl3_36 | ~spl3_42 | ~spl3_47),
% 0.21/0.50    inference(avatar_split_clause,[],[f454,f448,f393,f337,f91,f542])).
% 0.21/0.50  fof(f448,plain,(
% 0.21/0.50    spl3_47 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.50  fof(f454,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_36 | ~spl3_42 | ~spl3_47)),
% 0.21/0.50    inference(subsumption_resolution,[],[f453,f339])).
% 0.21/0.50  fof(f453,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_1 | ~spl3_42 | ~spl3_47)),
% 0.21/0.50    inference(subsumption_resolution,[],[f452,f395])).
% 0.21/0.50  fof(f452,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_1 | ~spl3_47)),
% 0.21/0.50    inference(superposition,[],[f117,f450])).
% 0.21/0.50  fof(f450,plain,(
% 0.21/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_47),
% 0.21/0.50    inference(avatar_component_clause,[],[f448])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ( ! [X4,X5] : (v1_funct_2(k2_tops_2(X4,X5,sK2),X5,X4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(sK2,X4,X5)) ) | ~spl3_1),
% 0.21/0.50    inference(resolution,[],[f93,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.21/0.50  fof(f499,plain,(
% 0.21/0.50    spl3_54 | ~spl3_1 | ~spl3_13 | ~spl3_27 | ~spl3_36 | ~spl3_47),
% 0.21/0.50    inference(avatar_split_clause,[],[f485,f448,f337,f266,f175,f91,f496])).
% 0.21/0.50  fof(f266,plain,(
% 0.21/0.50    spl3_27 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.50  fof(f485,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_13 | ~spl3_27 | ~spl3_36 | ~spl3_47)),
% 0.21/0.50    inference(forward_demodulation,[],[f484,f450])).
% 0.21/0.50  fof(f484,plain,(
% 0.21/0.50    m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_13 | ~spl3_27 | ~spl3_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f321,f339])).
% 0.21/0.50  fof(f321,plain,(
% 0.21/0.50    m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_1 | ~spl3_13 | ~spl3_27)),
% 0.21/0.50    inference(forward_demodulation,[],[f320,f268])).
% 0.21/0.50  fof(f268,plain,(
% 0.21/0.50    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f266])).
% 0.21/0.50  fof(f320,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_13 | ~spl3_27)),
% 0.21/0.50    inference(forward_demodulation,[],[f319,f268])).
% 0.21/0.50  fof(f319,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_13)),
% 0.21/0.50    inference(resolution,[],[f118,f177])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ( ! [X6,X7] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_2(sK2,X6,X7) | m1_subset_1(k2_tops_2(X6,X7,sK2),k1_zfmisc_1(k2_zfmisc_1(X7,X6)))) ) | ~spl3_1),
% 0.21/0.50    inference(resolution,[],[f93,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f494,plain,(
% 0.21/0.50    ~spl3_52 | spl3_53 | ~spl3_16 | ~spl3_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f417,f218,f198,f491,f487])).
% 0.21/0.51  fof(f491,plain,(
% 0.21/0.51    spl3_53 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    spl3_16 <=> v1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    spl3_19 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.51  fof(f417,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_16 | ~spl3_19)),
% 0.21/0.51    inference(resolution,[],[f206,f220])).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f218])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    ( ! [X0] : (~v4_relat_1(sK2,X0) | k1_relat_1(sK2) = X0 | ~v1_partfun1(sK2,X0)) ) | ~spl3_16),
% 0.21/0.51    inference(resolution,[],[f200,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    v1_relat_1(sK2) | ~spl3_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f198])).
% 0.21/0.51  fof(f461,plain,(
% 0.21/0.51    ~spl3_48 | spl3_17 | ~spl3_27 | ~spl3_47),
% 0.21/0.51    inference(avatar_split_clause,[],[f455,f448,f266,f209,f458])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    spl3_17 <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.51  fof(f455,plain,(
% 0.21/0.51    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (spl3_17 | ~spl3_27 | ~spl3_47)),
% 0.21/0.51    inference(forward_demodulation,[],[f294,f450])).
% 0.21/0.51  fof(f294,plain,(
% 0.21/0.51    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (spl3_17 | ~spl3_27)),
% 0.21/0.51    inference(superposition,[],[f211,f268])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f209])).
% 0.21/0.51  fof(f451,plain,(
% 0.21/0.51    spl3_47 | ~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_27 | ~spl3_28 | ~spl3_36),
% 0.21/0.51    inference(avatar_split_clause,[],[f383,f337,f270,f266,f175,f96,f91,f448])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl3_2 <=> v2_funct_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f270,plain,(
% 0.21/0.51    spl3_28 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.51  fof(f383,plain,(
% 0.21/0.51    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_27 | ~spl3_28 | ~spl3_36)),
% 0.21/0.51    inference(forward_demodulation,[],[f382,f268])).
% 0.21/0.51  fof(f382,plain,(
% 0.21/0.51    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_27 | ~spl3_28 | ~spl3_36)),
% 0.21/0.51    inference(subsumption_resolution,[],[f381,f272])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f270])).
% 0.21/0.51  fof(f381,plain,(
% 0.21/0.51    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_27 | ~spl3_36)),
% 0.21/0.51    inference(forward_demodulation,[],[f380,f268])).
% 0.21/0.51  fof(f380,plain,(
% 0.21/0.51    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_27 | ~spl3_36)),
% 0.21/0.51    inference(subsumption_resolution,[],[f379,f339])).
% 0.21/0.51  fof(f379,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_27)),
% 0.21/0.51    inference(forward_demodulation,[],[f378,f268])).
% 0.21/0.51  fof(f378,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.21/0.51    inference(resolution,[],[f122,f177])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_relset_1(X0,X1,sK2) != X1 | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)) ) | (~spl3_1 | ~spl3_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f119,f93])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_1(sK2) | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)) ) | ~spl3_2),
% 0.21/0.51    inference(resolution,[],[f98,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    v2_funct_1(sK2) | ~spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f396,plain,(
% 0.21/0.51    spl3_42 | ~spl3_13 | ~spl3_27),
% 0.21/0.51    inference(avatar_split_clause,[],[f293,f266,f175,f393])).
% 0.21/0.51  fof(f293,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_13 | ~spl3_27)),
% 0.21/0.51    inference(superposition,[],[f177,f268])).
% 0.21/0.51  fof(f371,plain,(
% 0.21/0.51    spl3_31 | ~spl3_34),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f370])).
% 0.21/0.51  fof(f370,plain,(
% 0.21/0.51    $false | (spl3_31 | ~spl3_34)),
% 0.21/0.51    inference(subsumption_resolution,[],[f365,f53])).
% 0.21/0.51  fof(f365,plain,(
% 0.21/0.51    ~v1_xboole_0(k1_xboole_0) | (spl3_31 | ~spl3_34)),
% 0.21/0.51    inference(superposition,[],[f303,f331])).
% 0.21/0.51  fof(f331,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(sK2) | ~spl3_34),
% 0.21/0.51    inference(avatar_component_clause,[],[f329])).
% 0.21/0.51  fof(f303,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_relat_1(sK2)) | spl3_31),
% 0.21/0.51    inference(avatar_component_clause,[],[f301])).
% 0.21/0.51  fof(f301,plain,(
% 0.21/0.51    spl3_31 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f310,plain,(
% 0.21/0.51    ~spl3_32 | spl3_31),
% 0.21/0.51    inference(avatar_split_clause,[],[f305,f301,f307])).
% 0.21/0.51  fof(f305,plain,(
% 0.21/0.51    ~v1_xboole_0(sK2) | spl3_31),
% 0.21/0.51    inference(resolution,[],[f303,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).
% 0.21/0.51  fof(f304,plain,(
% 0.21/0.51    ~spl3_31 | spl3_12 | ~spl3_27),
% 0.21/0.51    inference(avatar_split_clause,[],[f292,f266,f168,f301])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    spl3_12 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_relat_1(sK2)) | (spl3_12 | ~spl3_27)),
% 0.21/0.51    inference(superposition,[],[f170,f268])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_struct_0(sK1)) | spl3_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f168])).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f283,plain,(
% 0.21/0.51    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f260,plain,(
% 0.21/0.51    spl3_25 | ~spl3_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f190,f175,f257])).
% 0.21/0.51  fof(f257,plain,(
% 0.21/0.51    spl3_25 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.21/0.51    inference(resolution,[],[f177,f68])).
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    spl3_24 | ~spl3_1 | ~spl3_2 | ~spl3_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f242,f198,f96,f91,f249])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f124,f200])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f121,f93])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.21/0.51    inference(resolution,[],[f98,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    spl3_19 | ~spl3_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f191,f175,f218])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.21/0.51    inference(resolution,[],[f177,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    ~spl3_17 | ~spl3_18 | ~spl3_7 | ~spl3_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f205,f143,f133,f213,f209])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    spl3_18 <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    spl3_7 <=> k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    spl3_9 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_7 | ~spl3_9)),
% 0.21/0.51    inference(forward_demodulation,[],[f204,f145])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f143])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_7 | ~spl3_9)),
% 0.21/0.51    inference(forward_demodulation,[],[f203,f135])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f133])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | (~spl3_7 | ~spl3_9)),
% 0.21/0.51    inference(forward_demodulation,[],[f202,f145])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl3_7),
% 0.21/0.51    inference(forward_demodulation,[],[f44,f135])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f18])).
% 0.21/0.51  fof(f18,conjecture,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    spl3_16 | ~spl3_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f189,f175,f198])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    v1_relat_1(sK2) | ~spl3_13),
% 0.21/0.51    inference(resolution,[],[f177,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    spl3_13 | ~spl3_7 | ~spl3_8 | ~spl3_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f166,f143,f138,f133,f175])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    spl3_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.21/0.51    inference(forward_demodulation,[],[f160,f145])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8)),
% 0.21/0.51    inference(forward_demodulation,[],[f140,f135])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f138])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    ~spl3_12 | spl3_3 | ~spl3_4 | ~spl3_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f159,f133,f106,f101,f168])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    spl3_3 <=> v2_struct_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    spl3_4 <=> l1_struct_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_struct_0(sK1)) | (spl3_3 | ~spl3_4 | ~spl3_7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f158,f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ~v2_struct_0(sK1) | spl3_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f101])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_struct_0(sK1)) | v2_struct_0(sK1) | (~spl3_4 | ~spl3_7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f157,f108])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    l1_struct_0(sK1) | ~spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f106])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_7),
% 0.21/0.51    inference(superposition,[],[f59,f135])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    spl3_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f148])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    spl3_10 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    spl3_9 | ~spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f126,f111,f143])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    spl3_5 <=> l1_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 0.21/0.51    inference(resolution,[],[f113,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    l1_struct_0(sK0) | ~spl3_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f111])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f47,f138])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    spl3_7 | ~spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f125,f106,f133])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_4),
% 0.21/0.51    inference(resolution,[],[f108,f57])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f128])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f52,f111])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    l1_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f51,f106])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    l1_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ~spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f50,f101])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ~v2_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f49,f96])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    v2_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f45,f91])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (20529)------------------------------
% 0.21/0.51  % (20529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20529)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (20529)Memory used [KB]: 11001
% 0.21/0.51  % (20529)Time elapsed: 0.077 s
% 0.21/0.51  % (20529)------------------------------
% 0.21/0.51  % (20529)------------------------------
% 0.21/0.51  % (20521)Success in time 0.15 s
%------------------------------------------------------------------------------
