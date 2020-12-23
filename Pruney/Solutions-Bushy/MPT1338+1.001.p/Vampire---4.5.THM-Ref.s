%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1338+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 394 expanded)
%              Number of leaves         :   39 ( 165 expanded)
%              Depth                    :   11
%              Number of atoms          :  583 (1314 expanded)
%              Number of equality atoms :  131 ( 332 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f319,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f80,f90,f94,f100,f104,f111,f115,f121,f152,f159,f173,f180,f184,f188,f201,f205,f213,f219,f235,f244,f272,f282,f287,f309,f318])).

fof(f318,plain,
    ( ~ spl3_6
    | ~ spl3_8
    | spl3_19
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_29
    | ~ spl3_43 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_8
    | spl3_19
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_29
    | ~ spl3_43 ),
    inference(subsumption_resolution,[],[f316,f299])).

fof(f299,plain,
    ( k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_22
    | ~ spl3_28
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f298,f211])).

fof(f211,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl3_28
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f298,plain,
    ( k2_relat_1(sK2) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_22
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f290,f187])).

fof(f187,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl3_22
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f290,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_43 ),
    inference(resolution,[],[f286,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f286,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl3_43
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f316,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_6
    | ~ spl3_8
    | spl3_19
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f315,f218])).

fof(f218,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl3_29
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f315,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_6
    | ~ spl3_8
    | spl3_19 ),
    inference(forward_demodulation,[],[f314,f99])).

fof(f99,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f314,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_6
    | spl3_19 ),
    inference(forward_demodulation,[],[f172,f89])).

fof(f89,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_6
  <=> k2_struct_0(sK1) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f172,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl3_19
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f309,plain,
    ( spl3_20
    | ~ spl3_21
    | ~ spl3_34
    | ~ spl3_43 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | spl3_20
    | ~ spl3_21
    | ~ spl3_34
    | ~ spl3_43 ),
    inference(subsumption_resolution,[],[f307,f179])).

fof(f179,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_20
  <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f307,plain,
    ( k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_21
    | ~ spl3_34
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f306,f238])).

fof(f238,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl3_34
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f306,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_21
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f295,f183])).

fof(f183,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl3_21
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f295,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_43 ),
    inference(resolution,[],[f286,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f287,plain,
    ( spl3_43
    | ~ spl3_29
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f283,f280,f217,f285])).

fof(f280,plain,
    ( spl3_42
  <=> m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f283,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_29
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f281,f218])).

fof(f281,plain,
    ( m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f280])).

fof(f282,plain,
    ( spl3_42
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f142,f119,f102,f62,f280])).

fof(f62,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f102,plain,
    ( spl3_9
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f119,plain,
    ( spl3_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f142,plain,
    ( m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f141,f63])).

fof(f63,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f141,plain,
    ( ~ v1_funct_1(sK2)
    | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f130,f103])).

fof(f103,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f130,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_12 ),
    inference(resolution,[],[f120,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f120,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f272,plain,
    ( spl3_10
    | ~ spl3_33 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | spl3_10
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f264,f54])).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f264,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_10
    | ~ spl3_33 ),
    inference(superposition,[],[f110,f234])).

fof(f234,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl3_33
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f110,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_10
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f244,plain,
    ( spl3_34
    | ~ spl3_25
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f242,f230,f199,f237])).

fof(f199,plain,
    ( spl3_25
  <=> k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f230,plain,
    ( spl3_32
  <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f242,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_25
    | ~ spl3_32 ),
    inference(superposition,[],[f231,f200])).

fof(f200,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f199])).

fof(f231,plain,
    ( k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f230])).

fof(f235,plain,
    ( spl3_32
    | spl3_33
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f133,f119,f102,f233,f230])).

fof(f133,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f125,f103])).

fof(f125,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_12 ),
    inference(resolution,[],[f120,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f219,plain,
    ( spl3_29
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f158,f150,f119,f102,f98,f88,f66,f62,f217])).

fof(f66,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f150,plain,
    ( spl3_14
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f158,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f136,f157])).

fof(f157,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f156,f99])).

fof(f156,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f151,f89])).

fof(f151,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f136,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f135,f67])).

fof(f67,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f135,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f134,f63])).

fof(f134,plain,
    ( ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f127,f103])).

fof(f127,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_12 ),
    inference(resolution,[],[f120,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f213,plain,
    ( spl3_28
    | ~ spl3_15
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f212,f203,f154,f210])).

fof(f154,plain,
    ( spl3_15
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f203,plain,
    ( spl3_26
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f212,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_15
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f204,f155])).

fof(f155,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f154])).

fof(f204,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f203])).

fof(f205,plain,
    ( spl3_26
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f131,f119,f203])).

fof(f131,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_12 ),
    inference(resolution,[],[f120,f52])).

fof(f201,plain,
    ( spl3_25
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f126,f119,f199])).

fof(f126,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_12 ),
    inference(resolution,[],[f120,f44])).

fof(f188,plain,
    ( spl3_22
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f144,f119,f66,f62,f186])).

fof(f144,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f83,f132])).

fof(f132,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_12 ),
    inference(resolution,[],[f120,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f83,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f81,f63])).

fof(f81,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f67,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f184,plain,
    ( spl3_21
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f143,f119,f66,f62,f182])).

fof(f143,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f84,f132])).

fof(f84,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f82,f63])).

fof(f82,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f67,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f180,plain,
    ( ~ spl3_20
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_12
    | ~ spl3_14
    | spl3_18 ),
    inference(avatar_split_clause,[],[f176,f168,f150,f119,f102,f98,f88,f66,f62,f178])).

fof(f168,plain,
    ( spl3_18
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f176,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_12
    | ~ spl3_14
    | spl3_18 ),
    inference(forward_demodulation,[],[f175,f158])).

fof(f175,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_6
    | ~ spl3_8
    | spl3_18 ),
    inference(forward_demodulation,[],[f174,f99])).

fof(f174,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_6
    | spl3_18 ),
    inference(forward_demodulation,[],[f169,f89])).

fof(f169,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f168])).

fof(f173,plain,
    ( ~ spl3_18
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f29,f171,f168])).

fof(f29,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f159,plain,
    ( spl3_15
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f157,f150,f98,f88,f154])).

fof(f152,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f33,f150])).

fof(f33,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f121,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f117,f113,f98,f88,f119])).

fof(f113,plain,
    ( spl3_11
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f117,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f116,f99])).

fof(f116,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f114,f89])).

fof(f114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f32,f113])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f111,plain,
    ( ~ spl3_10
    | spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f107,f88,f74,f70,f109])).

fof(f70,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f74,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f107,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f106,f71])).

fof(f71,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f106,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f105,f75])).

fof(f75,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f105,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_6 ),
    inference(superposition,[],[f53,f89])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f104,plain,
    ( spl3_9
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f96,f92,f88,f78,f102])).

fof(f78,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f92,plain,
    ( spl3_7
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f96,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f95,f86])).

fof(f86,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f79,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f79,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f95,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f93,f89])).

fof(f93,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f100,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f86,f78,f98])).

fof(f94,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f31,f92])).

fof(f31,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f90,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f85,f74,f88])).

fof(f85,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f75,f51])).

fof(f80,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f37,f78])).

fof(f37,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f36,f74])).

fof(f36,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f35,f70])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f34,f66])).

fof(f34,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
