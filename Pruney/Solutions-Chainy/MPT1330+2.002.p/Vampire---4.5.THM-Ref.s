%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 304 expanded)
%              Number of leaves         :   40 ( 138 expanded)
%              Depth                    :   12
%              Number of atoms          :  497 (1211 expanded)
%              Number of equality atoms :   95 ( 346 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f332,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f63,f67,f71,f75,f79,f83,f89,f93,f101,f111,f125,f135,f143,f152,f156,f174,f175,f179,f217,f231,f313,f317,f324,f329,f331])).

fof(f331,plain,
    ( ~ spl3_12
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | ~ spl3_12
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f105,f172])).

fof(f172,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl3_21
  <=> ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f105,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl3_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f329,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f328,f91,f87,f65,f104])).

fof(f65,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f87,plain,
    ( spl3_9
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f91,plain,
    ( spl3_10
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f328,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f327,f92])).

fof(f92,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f327,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f66,f88])).

fof(f88,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f66,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f324,plain,
    ( ~ spl3_4
    | ~ spl3_36 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f66,f312])).

fof(f312,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl3_36
  <=> ! [X1,X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f317,plain,
    ( ~ spl3_29
    | ~ spl3_33 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl3_29
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f216,f238])).

fof(f238,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl3_33
  <=> ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f216,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl3_29
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f313,plain,
    ( spl3_33
    | spl3_36
    | spl3_32
    | ~ spl3_2
    | ~ spl3_20
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f308,f215,f167,f58,f229,f311,f237])).

fof(f229,plain,
    ( spl3_32
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f58,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f167,plain,
    ( spl3_20
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f308,plain,
    ( ! [X2,X0,X1] :
        ( k1_xboole_0 = k1_relat_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) )
    | ~ spl3_2
    | ~ spl3_20
    | ~ spl3_29 ),
    inference(resolution,[],[f306,f216])).

fof(f306,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_xboole_0 = k1_relat_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4))) )
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(resolution,[],[f305,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f305,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_relat_1(X7)
        | k1_xboole_0 = k1_relat_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(X7))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) )
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(resolution,[],[f303,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f303,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_xboole_0 = k1_relat_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) )
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(resolution,[],[f279,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f279,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 = k1_relat_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ v1_relat_1(X0) )
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(resolution,[],[f245,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f245,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f244,f178])).

fof(f178,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f244,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_partfun1(X0,k2_struct_0(sK1)) )
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f242,f178])).

fof(f242,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X1)))
        | v1_partfun1(X0,k2_struct_0(sK1)) )
    | ~ spl3_20 ),
    inference(resolution,[],[f168,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f168,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f167])).

fof(f231,plain,
    ( ~ spl3_32
    | ~ spl3_3
    | spl3_16 ),
    inference(avatar_split_clause,[],[f227,f133,f61,f229])).

fof(f61,plain,
    ( spl3_3
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f133,plain,
    ( spl3_16
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f227,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl3_3
    | spl3_16 ),
    inference(superposition,[],[f134,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f134,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f133])).

fof(f217,plain,
    ( spl3_29
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f188,f104,f61,f215])).

fof(f188,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))))
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(superposition,[],[f105,f62])).

fof(f179,plain,
    ( spl3_2
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f177,f167,f58])).

fof(f177,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_20 ),
    inference(resolution,[],[f168,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f175,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f174,plain,
    ( spl3_21
    | ~ spl3_13
    | spl3_20
    | spl3_16
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f159,f141,f104,f133,f167,f109,f171])).

fof(f109,plain,
    ( spl3_13
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f141,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ v4_relat_1(sK2,X0)
        | k1_relat_1(sK2) = X0
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f159,plain,
    ( ! [X1] :
        ( k2_struct_0(sK0) = k1_relat_1(sK2)
        | v1_xboole_0(k2_struct_0(sK1))
        | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X1))) )
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(resolution,[],[f157,f105])).

fof(f157,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relat_1(sK2) = X0
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
    | ~ spl3_18 ),
    inference(resolution,[],[f142,f49])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(sK2,X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | k1_relat_1(sK2) = X0
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f141])).

fof(f156,plain,(
    spl3_19 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl3_19 ),
    inference(resolution,[],[f151,f42])).

fof(f151,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_19
  <=> v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f152,plain,
    ( ~ spl3_19
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10
    | spl3_17 ),
    inference(avatar_split_clause,[],[f148,f138,f91,f87,f65,f150])).

fof(f138,plain,
    ( spl3_17
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f148,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10
    | spl3_17 ),
    inference(forward_demodulation,[],[f147,f92])).

fof(f147,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl3_4
    | ~ spl3_9
    | spl3_17 ),
    inference(forward_demodulation,[],[f145,f88])).

fof(f145,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl3_4
    | spl3_17 ),
    inference(resolution,[],[f144,f66])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl3_17 ),
    inference(resolution,[],[f139,f41])).

fof(f139,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f138])).

fof(f143,plain,
    ( ~ spl3_17
    | spl3_18
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f136,f73,f141,f138])).

fof(f73,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | k1_relat_1(sK2) = X0
        | ~ v4_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_6 ),
    inference(resolution,[],[f126,f46])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(sK2,X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f44,f74])).

fof(f74,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f135,plain,
    ( ~ spl3_15
    | ~ spl3_16
    | spl3_14 ),
    inference(avatar_split_clause,[],[f128,f123,f133,f130])).

fof(f130,plain,
    ( spl3_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f123,plain,
    ( spl3_14
  <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f128,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | spl3_14 ),
    inference(inner_rewriting,[],[f127])).

fof(f127,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl3_14 ),
    inference(superposition,[],[f124,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f124,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f123])).

fof(f125,plain,
    ( ~ spl3_12
    | ~ spl3_14
    | spl3_11 ),
    inference(avatar_split_clause,[],[f120,f99,f123,f104])).

fof(f99,plain,
    ( spl3_11
  <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f120,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl3_11 ),
    inference(superposition,[],[f100,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f100,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f111,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f107,f91,f87,f69,f109])).

fof(f69,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f107,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f96,f92])).

fof(f96,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(superposition,[],[f70,f88])).

fof(f70,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f101,plain,
    ( ~ spl3_11
    | spl3_1
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f97,f91,f87,f54,f99])).

fof(f54,plain,
    ( spl3_1
  <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f97,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f94,f92])).

fof(f94,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1
    | ~ spl3_9 ),
    inference(superposition,[],[f55,f88])).

fof(f55,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f93,plain,
    ( spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f85,f81,f91])).

fof(f81,plain,
    ( spl3_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f85,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f40,f82])).

fof(f82,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f81])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f89,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f84,f77,f87])).

fof(f77,plain,
    ( spl3_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f84,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f40,f78])).

fof(f78,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f83,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f32,f81])).

fof(f32,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
                & ( k1_xboole_0 = k2_struct_0(X0)
                  | k1_xboole_0 != k2_struct_0(X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(sK0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
            & ( k1_xboole_0 = k2_struct_0(sK0)
              | k1_xboole_0 != k2_struct_0(X1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
          & ( k1_xboole_0 = k2_struct_0(sK0)
            | k1_xboole_0 != k2_struct_0(sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
        & ( k1_xboole_0 = k2_struct_0(sK0)
          | k1_xboole_0 != k2_struct_0(sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
      & ( k1_xboole_0 = k2_struct_0(sK0)
        | k1_xboole_0 != k2_struct_0(sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

fof(f79,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f34,f73])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f35,f69])).

fof(f35,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f36,f65])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f37,f61,f58])).

fof(f37,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f38,f54])).

fof(f38,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:54:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (15029)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (15036)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (15028)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (15029)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (15037)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f332,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f56,f63,f67,f71,f75,f79,f83,f89,f93,f101,f111,f125,f135,f143,f152,f156,f174,f175,f179,f217,f231,f313,f317,f324,f329,f331])).
% 0.22/0.49  fof(f331,plain,(
% 0.22/0.49    ~spl3_12 | ~spl3_21),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f330])).
% 0.22/0.49  fof(f330,plain,(
% 0.22/0.49    $false | (~spl3_12 | ~spl3_21)),
% 0.22/0.49    inference(subsumption_resolution,[],[f105,f172])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | ~spl3_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f171])).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    spl3_21 <=> ! [X0] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f104])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    spl3_12 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.49  fof(f329,plain,(
% 0.22/0.49    spl3_12 | ~spl3_4 | ~spl3_9 | ~spl3_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f328,f91,f87,f65,f104])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    spl3_9 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl3_10 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.49  fof(f328,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_9 | ~spl3_10)),
% 0.22/0.49    inference(forward_demodulation,[],[f327,f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f91])).
% 0.22/0.49  fof(f327,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_9)),
% 0.22/0.49    inference(forward_demodulation,[],[f66,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f87])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f65])).
% 0.22/0.49  fof(f324,plain,(
% 0.22/0.49    ~spl3_4 | ~spl3_36),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f321])).
% 0.22/0.49  fof(f321,plain,(
% 0.22/0.49    $false | (~spl3_4 | ~spl3_36)),
% 0.22/0.49    inference(subsumption_resolution,[],[f66,f312])).
% 0.22/0.49  fof(f312,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_36),
% 0.22/0.49    inference(avatar_component_clause,[],[f311])).
% 0.22/0.49  fof(f311,plain,(
% 0.22/0.49    spl3_36 <=> ! [X1,X0] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.49  fof(f317,plain,(
% 0.22/0.49    ~spl3_29 | ~spl3_33),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f315])).
% 0.22/0.49  fof(f315,plain,(
% 0.22/0.49    $false | (~spl3_29 | ~spl3_33)),
% 0.22/0.49    inference(subsumption_resolution,[],[f216,f238])).
% 0.22/0.49  fof(f238,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | ~spl3_33),
% 0.22/0.49    inference(avatar_component_clause,[],[f237])).
% 0.22/0.49  fof(f237,plain,(
% 0.22/0.49    spl3_33 <=> ! [X0] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.49  fof(f216,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) | ~spl3_29),
% 0.22/0.49    inference(avatar_component_clause,[],[f215])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    spl3_29 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.49  fof(f313,plain,(
% 0.22/0.49    spl3_33 | spl3_36 | spl3_32 | ~spl3_2 | ~spl3_20 | ~spl3_29),
% 0.22/0.49    inference(avatar_split_clause,[],[f308,f215,f167,f58,f229,f311,f237])).
% 0.22/0.49  fof(f229,plain,(
% 0.22/0.49    spl3_32 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    spl3_2 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    spl3_20 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.49  fof(f308,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) ) | (~spl3_2 | ~spl3_20 | ~spl3_29)),
% 0.22/0.49    inference(resolution,[],[f306,f216])).
% 0.22/0.49  fof(f306,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))) ) | (~spl3_2 | ~spl3_20)),
% 0.22/0.49    inference(resolution,[],[f305,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.49  fof(f305,plain,(
% 0.22/0.49    ( ! [X6,X4,X7,X5] : (~v1_relat_1(X7) | k1_xboole_0 = k1_relat_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6))) | ~m1_subset_1(X4,k1_zfmisc_1(X7)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) ) | (~spl3_2 | ~spl3_20)),
% 0.22/0.49    inference(resolution,[],[f303,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.49  fof(f303,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) ) | (~spl3_2 | ~spl3_20)),
% 0.22/0.49    inference(resolution,[],[f279,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.49  fof(f279,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v4_relat_1(X0,k1_xboole_0) | k1_xboole_0 = k1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_relat_1(X0)) ) | (~spl3_2 | ~spl3_20)),
% 0.22/0.49    inference(resolution,[],[f245,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.49  fof(f245,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_partfun1(X0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) ) | (~spl3_2 | ~spl3_20)),
% 0.22/0.49    inference(forward_demodulation,[],[f244,f178])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f58])).
% 0.22/0.49  fof(f244,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X0,k2_struct_0(sK1))) ) | (~spl3_2 | ~spl3_20)),
% 0.22/0.49    inference(forward_demodulation,[],[f242,f178])).
% 0.22/0.49  fof(f242,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X1))) | v1_partfun1(X0,k2_struct_0(sK1))) ) | ~spl3_20),
% 0.22/0.49    inference(resolution,[],[f168,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.22/0.49  fof(f168,plain,(
% 0.22/0.49    v1_xboole_0(k2_struct_0(sK1)) | ~spl3_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f167])).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    ~spl3_32 | ~spl3_3 | spl3_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f227,f133,f61,f229])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    spl3_3 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    spl3_16 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    k1_xboole_0 != k1_relat_1(sK2) | (~spl3_3 | spl3_16)),
% 0.22/0.49    inference(superposition,[],[f134,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f61])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    k2_struct_0(sK0) != k1_relat_1(sK2) | spl3_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f133])).
% 0.22/0.49  fof(f217,plain,(
% 0.22/0.49    spl3_29 | ~spl3_3 | ~spl3_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f188,f104,f61,f215])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) | (~spl3_3 | ~spl3_12)),
% 0.22/0.49    inference(superposition,[],[f105,f62])).
% 0.22/0.49  fof(f179,plain,(
% 0.22/0.49    spl3_2 | ~spl3_20),
% 0.22/0.49    inference(avatar_split_clause,[],[f177,f167,f58])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_20),
% 0.22/0.49    inference(resolution,[],[f168,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.49  fof(f175,plain,(
% 0.22/0.49    u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    spl3_21 | ~spl3_13 | spl3_20 | spl3_16 | ~spl3_12 | ~spl3_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f159,f141,f104,f133,f167,f109,f171])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    spl3_13 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    spl3_18 <=> ! [X1,X0] : (~v1_funct_2(sK2,X0,X1) | ~v4_relat_1(sK2,X0) | k1_relat_1(sK2) = X0 | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    ( ! [X1] : (k2_struct_0(sK0) = k1_relat_1(sK2) | v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X1)))) ) | (~spl3_12 | ~spl3_18)),
% 0.22/0.49    inference(resolution,[],[f157,f105])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(sK2) = X0 | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) ) | ~spl3_18),
% 0.22/0.49    inference(resolution,[],[f142,f49])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v4_relat_1(sK2,X0) | ~v1_funct_2(sK2,X0,X1) | k1_relat_1(sK2) = X0 | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f141])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    spl3_19),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f154])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    $false | spl3_19),
% 0.22/0.49    inference(resolution,[],[f151,f42])).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | spl3_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f150])).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    spl3_19 <=> v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    ~spl3_19 | ~spl3_4 | ~spl3_9 | ~spl3_10 | spl3_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f148,f138,f91,f87,f65,f150])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    spl3_17 <=> v1_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | (~spl3_4 | ~spl3_9 | ~spl3_10 | spl3_17)),
% 0.22/0.49    inference(forward_demodulation,[],[f147,f92])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))) | (~spl3_4 | ~spl3_9 | spl3_17)),
% 0.22/0.49    inference(forward_demodulation,[],[f145,f88])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | (~spl3_4 | spl3_17)),
% 0.22/0.49    inference(resolution,[],[f144,f66])).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl3_17),
% 0.22/0.49    inference(resolution,[],[f139,f41])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | spl3_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f138])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    ~spl3_17 | spl3_18 | ~spl3_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f136,f73,f141,f138])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl3_6 <=> v1_funct_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | k1_relat_1(sK2) = X0 | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl3_6),
% 0.22/0.49    inference(resolution,[],[f126,f46])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_partfun1(sK2,X0) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) ) | ~spl3_6),
% 0.22/0.49    inference(resolution,[],[f44,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    v1_funct_1(sK2) | ~spl3_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f73])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    ~spl3_15 | ~spl3_16 | spl3_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f128,f123,f133,f130])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    spl3_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    spl3_14 <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    k2_struct_0(sK0) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | spl3_14),
% 0.22/0.49    inference(inner_rewriting,[],[f127])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    k2_struct_0(sK0) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl3_14),
% 0.22/0.49    inference(superposition,[],[f124,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | spl3_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f123])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    ~spl3_12 | ~spl3_14 | spl3_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f120,f99,f123,f104])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    spl3_11 <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl3_11),
% 0.22/0.49    inference(superposition,[],[f100,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f99])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    spl3_13 | ~spl3_5 | ~spl3_9 | ~spl3_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f107,f91,f87,f69,f109])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl3_5 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_9 | ~spl3_10)),
% 0.22/0.49    inference(forward_demodulation,[],[f96,f92])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_9)),
% 0.22/0.49    inference(superposition,[],[f70,f88])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f69])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    ~spl3_11 | spl3_1 | ~spl3_9 | ~spl3_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f97,f91,f87,f54,f99])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    spl3_1 <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (spl3_1 | ~spl3_9 | ~spl3_10)),
% 0.22/0.49    inference(forward_demodulation,[],[f94,f92])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (spl3_1 | ~spl3_9)),
% 0.22/0.49    inference(superposition,[],[f55,f88])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f54])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    spl3_10 | ~spl3_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f85,f81,f91])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    spl3_8 <=> l1_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_8),
% 0.22/0.49    inference(resolution,[],[f40,f82])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    l1_struct_0(sK0) | ~spl3_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f81])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl3_9 | ~spl3_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f84,f77,f87])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    spl3_7 <=> l1_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.22/0.49    inference(resolution,[],[f40,f78])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    l1_struct_0(sK1) | ~spl3_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f77])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    spl3_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f81])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    l1_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ((k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f29,f28,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f11])).
% 0.22/0.49  fof(f11,conjecture,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl3_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f77])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    l1_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    spl3_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f73])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    v1_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f69])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f65])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ~spl3_2 | spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f61,f58])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ~spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f38,f54])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (15029)------------------------------
% 0.22/0.50  % (15029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15029)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (15029)Memory used [KB]: 10874
% 0.22/0.50  % (15029)Time elapsed: 0.061 s
% 0.22/0.50  % (15029)------------------------------
% 0.22/0.50  % (15029)------------------------------
% 0.22/0.50  % (15036)Refutation not found, incomplete strategy% (15036)------------------------------
% 0.22/0.50  % (15036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15036)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (15036)Memory used [KB]: 1663
% 0.22/0.50  % (15036)Time elapsed: 0.072 s
% 0.22/0.50  % (15036)------------------------------
% 0.22/0.50  % (15036)------------------------------
% 0.22/0.50  % (15022)Success in time 0.13 s
%------------------------------------------------------------------------------
