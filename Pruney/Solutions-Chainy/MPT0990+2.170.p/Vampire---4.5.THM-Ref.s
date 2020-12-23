%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:58 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 361 expanded)
%              Number of leaves         :   47 ( 162 expanded)
%              Depth                    :    9
%              Number of atoms          :  720 (2108 expanded)
%              Number of equality atoms :  185 ( 650 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f628,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f154,f166,f170,f192,f196,f204,f217,f224,f234,f243,f258,f335,f352,f381,f394,f415,f608,f623,f627])).

fof(f627,plain,
    ( ~ spl4_14
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_21
    | spl4_66 ),
    inference(avatar_split_clause,[],[f626,f620,f221,f106,f96,f163])).

fof(f163,plain,
    ( spl4_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f96,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f106,plain,
    ( spl4_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f221,plain,
    ( spl4_21
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f620,plain,
    ( spl4_66
  <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f626,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_21
    | spl4_66 ),
    inference(trivial_inequality_removal,[],[f625])).

fof(f625,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_21
    | spl4_66 ),
    inference(forward_demodulation,[],[f624,f223])).

fof(f223,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f221])).

fof(f624,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_66 ),
    inference(superposition,[],[f622,f64])).

fof(f64,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f622,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
    | spl4_66 ),
    inference(avatar_component_clause,[],[f620])).

fof(f623,plain,
    ( ~ spl4_14
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_66
    | spl4_8
    | ~ spl4_24
    | ~ spl4_36
    | ~ spl4_19
    | ~ spl4_65 ),
    inference(avatar_split_clause,[],[f618,f606,f201,f349,f255,f131,f620,f106,f96,f163])).

fof(f131,plain,
    ( spl4_8
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f255,plain,
    ( spl4_24
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f349,plain,
    ( spl4_36
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f201,plain,
    ( spl4_19
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

% (19210)Refutation not found, incomplete strategy% (19210)------------------------------
% (19210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19210)Termination reason: Refutation not found, incomplete strategy

% (19210)Memory used [KB]: 1918
fof(f606,plain,
    ( spl4_65
  <=> ! [X4] :
        ( k6_partfun1(sK1) != k5_relat_1(X4,sK2)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4)
        | sK3 = X4
        | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

% (19210)Time elapsed: 0.190 s
% (19210)------------------------------
% (19210)------------------------------
fof(f618,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) = sK3
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_19
    | ~ spl4_65 ),
    inference(trivial_inequality_removal,[],[f617])).

fof(f617,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) = sK3
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_19
    | ~ spl4_65 ),
    inference(forward_demodulation,[],[f616,f203])).

fof(f203,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f201])).

fof(f616,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) = sK3
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_65 ),
    inference(superposition,[],[f607,f84])).

fof(f84,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f62,f75])).

fof(f75,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f62,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f607,plain,
    ( ! [X4] :
        ( k6_partfun1(sK1) != k5_relat_1(X4,sK2)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4)
        | sK3 = X4
        | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(X4)) )
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f606])).

fof(f608,plain,
    ( ~ spl4_14
    | ~ spl4_1
    | ~ spl4_18
    | ~ spl4_2
    | spl4_65
    | ~ spl4_23
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f421,f391,f240,f606,f101,f189,f96,f163])).

fof(f189,plain,
    ( spl4_18
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f101,plain,
    ( spl4_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f240,plain,
    ( spl4_23
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f391,plain,
    ( spl4_42
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f421,plain,
    ( ! [X4] :
        ( k6_partfun1(sK1) != k5_relat_1(X4,sK2)
        | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(X4))
        | sK3 = X4
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4) )
    | ~ spl4_23
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f419,f242])).

fof(f242,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f240])).

fof(f419,plain,
    ( ! [X4] :
        ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(X4))
        | sK3 = X4
        | k5_relat_1(X4,sK2) != k6_partfun1(k1_relat_1(sK3))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4) )
    | ~ spl4_42 ),
    inference(superposition,[],[f93,f393])).

fof(f393,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f391])).

fof(f93,plain,(
    ! [X2,X3,X1] :
      ( k5_relat_1(X2,X3) != k6_partfun1(k2_relat_1(X1))
      | X1 = X3
      | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_partfun1(X0)
      | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3))
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f80,f75,f75])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_relat_1(X0)
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

% (19219)Refutation not found, incomplete strategy% (19219)------------------------------
% (19219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19219)Termination reason: Refutation not found, incomplete strategy

% (19219)Memory used [KB]: 11129
% (19219)Time elapsed: 0.136 s
% (19219)------------------------------
% (19219)------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X2,X3) = k6_relat_1(X0)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & k2_relat_1(X1) = X0 )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l72_funct_1)).

fof(f415,plain,
    ( ~ spl4_9
    | ~ spl4_10
    | spl4_41 ),
    inference(avatar_contradiction_clause,[],[f403])).

fof(f403,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_10
    | spl4_41 ),
    inference(unit_resulting_resolution,[],[f138,f143,f389,f286])).

fof(f286,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f83,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f389,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_41 ),
    inference(avatar_component_clause,[],[f387])).

fof(f387,plain,
    ( spl4_41
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f143,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl4_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f138,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl4_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f394,plain,
    ( ~ spl4_41
    | spl4_42
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f385,f378,f391,f387])).

fof(f378,plain,
    ( spl4_40
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f385,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_40 ),
    inference(resolution,[],[f380,f246])).

fof(f246,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f71,f74])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f380,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f378])).

fof(f381,plain,
    ( ~ spl4_1
    | ~ spl4_9
    | ~ spl4_2
    | ~ spl4_10
    | spl4_40
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f347,f151,f378,f141,f101,f136,f96])).

fof(f151,plain,
    ( spl4_12
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f347,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(superposition,[],[f153,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f153,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f151])).

fof(f352,plain,
    ( ~ spl4_17
    | spl4_36
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f340,f332,f349,f185])).

fof(f185,plain,
    ( spl4_17
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f332,plain,
    ( spl4_34
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f340,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_34 ),
    inference(resolution,[],[f334,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f334,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f332])).

fof(f335,plain,
    ( ~ spl4_1
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_3
    | spl4_34
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f330,f146,f332,f106,f136,f121,f96])).

fof(f121,plain,
    ( spl4_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f146,plain,
    ( spl4_11
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f330,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_11 ),
    inference(trivial_inequality_removal,[],[f327])).

fof(f327,plain,
    ( sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_11 ),
    inference(superposition,[],[f60,f148])).

fof(f148,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f258,plain,
    ( ~ spl4_1
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_3
    | spl4_24
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f253,f146,f255,f106,f136,f121,f96])).

fof(f253,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_11 ),
    inference(trivial_inequality_removal,[],[f250])).

fof(f250,plain,
    ( sK1 != sK1
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_11 ),
    inference(superposition,[],[f58,f148])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f243,plain,
    ( ~ spl4_10
    | spl4_23
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f235,f231,f240,f141])).

fof(f231,plain,
    ( spl4_22
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f235,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_22 ),
    inference(superposition,[],[f233,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f233,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f231])).

fof(f234,plain,
    ( spl4_22
    | spl4_4
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f211,f141,f126,f111,f231])).

fof(f111,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f126,plain,
    ( spl4_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f211,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_10 ),
    inference(resolution,[],[f65,f143])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f27])).

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

fof(f224,plain,
    ( ~ spl4_9
    | spl4_21
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f218,f214,f221,f136])).

fof(f214,plain,
    ( spl4_20
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f218,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_20 ),
    inference(superposition,[],[f216,f81])).

fof(f216,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f214])).

fof(f217,plain,
    ( spl4_20
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f210,f136,f121,f116,f214])).

fof(f116,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f210,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_9 ),
    inference(resolution,[],[f65,f138])).

fof(f204,plain,
    ( ~ spl4_9
    | spl4_19
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f198,f146,f201,f136])).

fof(f198,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_11 ),
    inference(superposition,[],[f77,f148])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f196,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl4_17 ),
    inference(unit_resulting_resolution,[],[f79,f187])).

fof(f187,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f185])).

fof(f79,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f192,plain,
    ( ~ spl4_17
    | spl4_18
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f156,f141,f189,f185])).

fof(f156,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_10 ),
    inference(resolution,[],[f78,f143])).

fof(f170,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f79,f161])).

fof(f161,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl4_13
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f166,plain,
    ( ~ spl4_13
    | spl4_14
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f155,f136,f163,f159])).

fof(f155,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_9 ),
    inference(resolution,[],[f78,f138])).

fof(f154,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f53,f151])).

fof(f53,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f42,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f149,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f52,f146])).

fof(f52,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f144,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f51,f141])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f139,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f48,f136])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f134,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f57,f131])).

fof(f57,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f43])).

fof(f129,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f50,f126])).

fof(f50,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f124,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f47,f121])).

fof(f47,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f119,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f56,f116])).

fof(f56,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f114,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f55,f111])).

fof(f55,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f43])).

fof(f109,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f54,f106])).

fof(f54,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f104,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f49,f101])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f99,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f46,f96])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:46:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.56  % (19223)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (19217)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (19215)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (19216)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.57  % (19223)Refutation not found, incomplete strategy% (19223)------------------------------
% 0.21/0.57  % (19223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (19231)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.57  % (19232)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.57  % (19225)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.57  % (19225)Refutation not found, incomplete strategy% (19225)------------------------------
% 0.21/0.57  % (19225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (19233)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.58  % (19225)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (19225)Memory used [KB]: 10746
% 0.21/0.58  % (19225)Time elapsed: 0.139 s
% 0.21/0.58  % (19225)------------------------------
% 0.21/0.58  % (19225)------------------------------
% 0.21/0.58  % (19224)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.58  % (19214)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.63/0.58  % (19212)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.63/0.58  % (19227)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.63/0.58  % (19230)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.63/0.58  % (19223)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (19223)Memory used [KB]: 1918
% 1.63/0.58  % (19223)Time elapsed: 0.135 s
% 1.63/0.58  % (19223)------------------------------
% 1.63/0.58  % (19223)------------------------------
% 1.63/0.59  % (19209)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.63/0.59  % (19222)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.63/0.59  % (19235)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.63/0.59  % (19220)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.63/0.59  % (19238)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.63/0.59  % (19210)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.63/0.59  % (19213)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.63/0.59  % (19237)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.63/0.60  % (19211)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.63/0.60  % (19236)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.81/0.60  % (19229)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.81/0.60  % (19228)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.81/0.60  % (19219)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.81/0.60  % (19221)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.81/0.61  % (19226)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.81/0.61  % (19218)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.81/0.61  % (19234)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.81/0.61  % (19238)Refutation not found, incomplete strategy% (19238)------------------------------
% 1.81/0.61  % (19238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.61  % (19238)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.61  
% 1.81/0.61  % (19238)Memory used [KB]: 1791
% 1.81/0.61  % (19238)Time elapsed: 0.187 s
% 1.81/0.61  % (19238)------------------------------
% 1.81/0.61  % (19238)------------------------------
% 1.81/0.62  % (19237)Refutation not found, incomplete strategy% (19237)------------------------------
% 1.81/0.62  % (19237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.62  % (19237)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.62  
% 1.81/0.62  % (19237)Memory used [KB]: 11129
% 1.81/0.62  % (19237)Time elapsed: 0.177 s
% 1.81/0.62  % (19237)------------------------------
% 1.81/0.62  % (19237)------------------------------
% 1.81/0.63  % (19232)Refutation found. Thanks to Tanya!
% 1.81/0.63  % SZS status Theorem for theBenchmark
% 1.81/0.63  % SZS output start Proof for theBenchmark
% 1.81/0.63  fof(f628,plain,(
% 1.81/0.63    $false),
% 1.81/0.63    inference(avatar_sat_refutation,[],[f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f154,f166,f170,f192,f196,f204,f217,f224,f234,f243,f258,f335,f352,f381,f394,f415,f608,f623,f627])).
% 1.81/0.63  fof(f627,plain,(
% 1.81/0.63    ~spl4_14 | ~spl4_1 | ~spl4_3 | ~spl4_21 | spl4_66),
% 1.81/0.63    inference(avatar_split_clause,[],[f626,f620,f221,f106,f96,f163])).
% 1.81/0.63  fof(f163,plain,(
% 1.81/0.63    spl4_14 <=> v1_relat_1(sK2)),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.81/0.63  fof(f96,plain,(
% 1.81/0.63    spl4_1 <=> v1_funct_1(sK2)),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.81/0.63  fof(f106,plain,(
% 1.81/0.63    spl4_3 <=> v2_funct_1(sK2)),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.81/0.63  fof(f221,plain,(
% 1.81/0.63    spl4_21 <=> sK0 = k1_relat_1(sK2)),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.81/0.63  fof(f620,plain,(
% 1.81/0.63    spl4_66 <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(k2_funct_1(sK2)))),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 1.81/0.63  fof(f626,plain,(
% 1.81/0.63    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_21 | spl4_66)),
% 1.81/0.63    inference(trivial_inequality_removal,[],[f625])).
% 1.81/0.63  fof(f625,plain,(
% 1.81/0.63    k6_partfun1(sK0) != k6_partfun1(sK0) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_21 | spl4_66)),
% 1.81/0.63    inference(forward_demodulation,[],[f624,f223])).
% 1.81/0.63  fof(f223,plain,(
% 1.81/0.63    sK0 = k1_relat_1(sK2) | ~spl4_21),
% 1.81/0.63    inference(avatar_component_clause,[],[f221])).
% 1.81/0.63  fof(f624,plain,(
% 1.81/0.63    k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_66),
% 1.81/0.63    inference(superposition,[],[f622,f64])).
% 1.81/0.63  fof(f64,plain,(
% 1.81/0.63    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f25])).
% 1.81/0.63  fof(f25,plain,(
% 1.81/0.63    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.81/0.63    inference(flattening,[],[f24])).
% 1.81/0.63  fof(f24,plain,(
% 1.81/0.63    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.81/0.63    inference(ennf_transformation,[],[f4])).
% 1.81/0.63  fof(f4,axiom,(
% 1.81/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.81/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.81/0.63  fof(f622,plain,(
% 1.81/0.63    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k2_funct_1(sK2))) | spl4_66),
% 1.81/0.63    inference(avatar_component_clause,[],[f620])).
% 1.81/0.63  fof(f623,plain,(
% 1.81/0.63    ~spl4_14 | ~spl4_1 | ~spl4_3 | ~spl4_66 | spl4_8 | ~spl4_24 | ~spl4_36 | ~spl4_19 | ~spl4_65),
% 1.81/0.63    inference(avatar_split_clause,[],[f618,f606,f201,f349,f255,f131,f620,f106,f96,f163])).
% 1.81/0.63  fof(f131,plain,(
% 1.81/0.63    spl4_8 <=> k2_funct_1(sK2) = sK3),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.81/0.63  fof(f255,plain,(
% 1.81/0.63    spl4_24 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.81/0.63  fof(f349,plain,(
% 1.81/0.63    spl4_36 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.81/0.63  fof(f201,plain,(
% 1.81/0.63    spl4_19 <=> sK1 = k2_relat_1(sK2)),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.81/0.63  % (19210)Refutation not found, incomplete strategy% (19210)------------------------------
% 1.81/0.63  % (19210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.63  % (19210)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.63  
% 1.81/0.63  % (19210)Memory used [KB]: 1918
% 1.81/0.63  fof(f606,plain,(
% 1.81/0.63    spl4_65 <=> ! [X4] : (k6_partfun1(sK1) != k5_relat_1(X4,sK2) | ~v1_relat_1(X4) | ~v1_funct_1(X4) | sK3 = X4 | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(X4)))),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 1.81/0.63  % (19210)Time elapsed: 0.190 s
% 1.81/0.63  % (19210)------------------------------
% 1.81/0.63  % (19210)------------------------------
% 1.81/0.63  fof(f618,plain,(
% 1.81/0.63    ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k2_funct_1(sK2) = sK3 | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k2_funct_1(sK2))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_19 | ~spl4_65)),
% 1.81/0.63    inference(trivial_inequality_removal,[],[f617])).
% 1.81/0.63  fof(f617,plain,(
% 1.81/0.63    k6_partfun1(sK1) != k6_partfun1(sK1) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k2_funct_1(sK2) = sK3 | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k2_funct_1(sK2))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_19 | ~spl4_65)),
% 1.81/0.63    inference(forward_demodulation,[],[f616,f203])).
% 1.81/0.63  fof(f203,plain,(
% 1.81/0.63    sK1 = k2_relat_1(sK2) | ~spl4_19),
% 1.81/0.63    inference(avatar_component_clause,[],[f201])).
% 1.81/0.63  fof(f616,plain,(
% 1.81/0.63    k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k2_funct_1(sK2) = sK3 | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k2_funct_1(sK2))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_65),
% 1.81/0.63    inference(superposition,[],[f607,f84])).
% 1.81/0.63  fof(f84,plain,(
% 1.81/0.63    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/0.63    inference(definition_unfolding,[],[f62,f75])).
% 1.81/0.63  fof(f75,plain,(
% 1.81/0.63    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f14])).
% 1.81/0.63  fof(f14,axiom,(
% 1.81/0.63    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.81/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.81/0.63  fof(f62,plain,(
% 1.81/0.63    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f23])).
% 1.81/0.63  fof(f23,plain,(
% 1.81/0.63    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.81/0.63    inference(flattening,[],[f22])).
% 1.81/0.63  fof(f22,plain,(
% 1.81/0.63    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.81/0.63    inference(ennf_transformation,[],[f5])).
% 1.81/0.63  fof(f5,axiom,(
% 1.81/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.81/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.81/0.63  fof(f607,plain,(
% 1.81/0.63    ( ! [X4] : (k6_partfun1(sK1) != k5_relat_1(X4,sK2) | ~v1_relat_1(X4) | ~v1_funct_1(X4) | sK3 = X4 | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(X4))) ) | ~spl4_65),
% 1.81/0.63    inference(avatar_component_clause,[],[f606])).
% 1.81/0.63  fof(f608,plain,(
% 1.81/0.63    ~spl4_14 | ~spl4_1 | ~spl4_18 | ~spl4_2 | spl4_65 | ~spl4_23 | ~spl4_42),
% 1.81/0.63    inference(avatar_split_clause,[],[f421,f391,f240,f606,f101,f189,f96,f163])).
% 1.81/0.63  fof(f189,plain,(
% 1.81/0.63    spl4_18 <=> v1_relat_1(sK3)),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.81/0.63  fof(f101,plain,(
% 1.81/0.63    spl4_2 <=> v1_funct_1(sK3)),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.81/0.63  fof(f240,plain,(
% 1.81/0.63    spl4_23 <=> sK1 = k1_relat_1(sK3)),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.81/0.63  fof(f391,plain,(
% 1.81/0.63    spl4_42 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.81/0.63  fof(f421,plain,(
% 1.81/0.63    ( ! [X4] : (k6_partfun1(sK1) != k5_relat_1(X4,sK2) | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(X4)) | sK3 = X4 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) ) | (~spl4_23 | ~spl4_42)),
% 1.81/0.63    inference(forward_demodulation,[],[f419,f242])).
% 1.81/0.63  fof(f242,plain,(
% 1.81/0.63    sK1 = k1_relat_1(sK3) | ~spl4_23),
% 1.81/0.63    inference(avatar_component_clause,[],[f240])).
% 1.81/0.63  fof(f419,plain,(
% 1.81/0.63    ( ! [X4] : (k6_partfun1(sK0) != k6_partfun1(k2_relat_1(X4)) | sK3 = X4 | k5_relat_1(X4,sK2) != k6_partfun1(k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) ) | ~spl4_42),
% 1.81/0.63    inference(superposition,[],[f93,f393])).
% 1.81/0.63  fof(f393,plain,(
% 1.81/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_42),
% 1.81/0.63    inference(avatar_component_clause,[],[f391])).
% 1.81/0.63  fof(f93,plain,(
% 1.81/0.63    ( ! [X2,X3,X1] : (k5_relat_1(X2,X3) != k6_partfun1(k2_relat_1(X1)) | X1 = X3 | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.81/0.63    inference(equality_resolution,[],[f86])).
% 1.81/0.63  fof(f86,plain,(
% 1.81/0.63    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_partfun1(X0) | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.81/0.63    inference(definition_unfolding,[],[f80,f75,f75])).
% 1.81/0.63  fof(f80,plain,(
% 1.81/0.63    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f35])).
% 1.81/0.63  fof(f35,plain,(
% 1.81/0.63    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.81/0.63    inference(flattening,[],[f34])).
% 1.81/0.63  fof(f34,plain,(
% 1.81/0.63    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0)) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.81/0.63    inference(ennf_transformation,[],[f3])).
% 2.00/0.63  % (19219)Refutation not found, incomplete strategy% (19219)------------------------------
% 2.00/0.63  % (19219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.64  % (19219)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.64  
% 2.00/0.64  % (19219)Memory used [KB]: 11129
% 2.00/0.64  % (19219)Time elapsed: 0.136 s
% 2.00/0.64  % (19219)------------------------------
% 2.00/0.64  % (19219)------------------------------
% 2.00/0.65  fof(f3,axiom,(
% 2.00/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X2,X3) = k6_relat_1(X0) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & k2_relat_1(X1) = X0) => X1 = X3))))),
% 2.00/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l72_funct_1)).
% 2.00/0.65  fof(f415,plain,(
% 2.00/0.65    ~spl4_9 | ~spl4_10 | spl4_41),
% 2.00/0.65    inference(avatar_contradiction_clause,[],[f403])).
% 2.00/0.65  fof(f403,plain,(
% 2.00/0.65    $false | (~spl4_9 | ~spl4_10 | spl4_41)),
% 2.00/0.65    inference(unit_resulting_resolution,[],[f138,f143,f389,f286])).
% 2.00/0.65  fof(f286,plain,(
% 2.00/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/0.65    inference(duplicate_literal_removal,[],[f285])).
% 2.00/0.65  fof(f285,plain,(
% 2.00/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/0.65    inference(superposition,[],[f83,f82])).
% 2.00/0.65  fof(f82,plain,(
% 2.00/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/0.65    inference(cnf_transformation,[],[f38])).
% 2.00/0.65  fof(f38,plain,(
% 2.00/0.65    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.65    inference(flattening,[],[f37])).
% 2.00/0.65  fof(f37,plain,(
% 2.00/0.65    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.00/0.65    inference(ennf_transformation,[],[f9])).
% 2.00/0.65  fof(f9,axiom,(
% 2.00/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.00/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 2.00/0.65  fof(f83,plain,(
% 2.00/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/0.65    inference(cnf_transformation,[],[f40])).
% 2.00/0.65  fof(f40,plain,(
% 2.00/0.65    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.65    inference(flattening,[],[f39])).
% 2.00/0.65  fof(f39,plain,(
% 2.00/0.65    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.00/0.65    inference(ennf_transformation,[],[f6])).
% 2.00/0.65  fof(f6,axiom,(
% 2.00/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 2.00/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 2.00/0.65  fof(f389,plain,(
% 2.00/0.65    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_41),
% 2.00/0.65    inference(avatar_component_clause,[],[f387])).
% 2.00/0.65  fof(f387,plain,(
% 2.00/0.65    spl4_41 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.00/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 2.00/0.65  fof(f143,plain,(
% 2.00/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_10),
% 2.00/0.65    inference(avatar_component_clause,[],[f141])).
% 2.00/0.65  fof(f141,plain,(
% 2.00/0.65    spl4_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.00/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.00/0.65  fof(f138,plain,(
% 2.00/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_9),
% 2.00/0.65    inference(avatar_component_clause,[],[f136])).
% 2.00/0.65  fof(f136,plain,(
% 2.00/0.65    spl4_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.00/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.00/0.65  fof(f394,plain,(
% 2.00/0.65    ~spl4_41 | spl4_42 | ~spl4_40),
% 2.00/0.65    inference(avatar_split_clause,[],[f385,f378,f391,f387])).
% 2.00/0.65  fof(f378,plain,(
% 2.00/0.65    spl4_40 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.00/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 2.00/0.65  fof(f385,plain,(
% 2.00/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_40),
% 2.00/0.65    inference(resolution,[],[f380,f246])).
% 2.00/0.65  fof(f246,plain,(
% 2.00/0.65    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.00/0.65    inference(resolution,[],[f71,f74])).
% 2.00/0.65  fof(f74,plain,(
% 2.00/0.65    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.00/0.65    inference(cnf_transformation,[],[f12])).
% 2.00/0.65  fof(f12,axiom,(
% 2.00/0.65    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.00/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.00/0.65  fof(f71,plain,(
% 2.00/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/0.65    inference(cnf_transformation,[],[f45])).
% 2.00/0.65  fof(f45,plain,(
% 2.00/0.65    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.65    inference(nnf_transformation,[],[f29])).
% 2.00/0.65  fof(f29,plain,(
% 2.00/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.65    inference(flattening,[],[f28])).
% 2.00/0.65  fof(f28,plain,(
% 2.00/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.00/0.65    inference(ennf_transformation,[],[f10])).
% 2.00/0.65  fof(f10,axiom,(
% 2.00/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.00/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.00/0.65  fof(f380,plain,(
% 2.00/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~spl4_40),
% 2.00/0.65    inference(avatar_component_clause,[],[f378])).
% 2.00/0.65  fof(f381,plain,(
% 2.00/0.65    ~spl4_1 | ~spl4_9 | ~spl4_2 | ~spl4_10 | spl4_40 | ~spl4_12),
% 2.00/0.65    inference(avatar_split_clause,[],[f347,f151,f378,f141,f101,f136,f96])).
% 2.00/0.65  fof(f151,plain,(
% 2.00/0.65    spl4_12 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.00/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.00/0.65  fof(f347,plain,(
% 2.00/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_12),
% 2.00/0.65    inference(superposition,[],[f153,f76])).
% 2.00/0.65  fof(f76,plain,(
% 2.00/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.00/0.65    inference(cnf_transformation,[],[f31])).
% 2.00/0.65  fof(f31,plain,(
% 2.00/0.65    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.00/0.65    inference(flattening,[],[f30])).
% 2.00/0.65  fof(f30,plain,(
% 2.00/0.65    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.00/0.65    inference(ennf_transformation,[],[f13])).
% 2.00/0.65  fof(f13,axiom,(
% 2.00/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.00/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.00/0.65  fof(f153,plain,(
% 2.00/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_12),
% 2.00/0.65    inference(avatar_component_clause,[],[f151])).
% 2.00/0.65  fof(f352,plain,(
% 2.00/0.65    ~spl4_17 | spl4_36 | ~spl4_34),
% 2.00/0.65    inference(avatar_split_clause,[],[f340,f332,f349,f185])).
% 2.00/0.65  fof(f185,plain,(
% 2.00/0.65    spl4_17 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 2.00/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 2.00/0.65  fof(f332,plain,(
% 2.00/0.65    spl4_34 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.00/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 2.00/0.65  fof(f340,plain,(
% 2.00/0.65    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_34),
% 2.00/0.65    inference(resolution,[],[f334,f78])).
% 2.00/0.65  fof(f78,plain,(
% 2.00/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.00/0.65    inference(cnf_transformation,[],[f33])).
% 2.00/0.65  fof(f33,plain,(
% 2.00/0.65    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.00/0.65    inference(ennf_transformation,[],[f1])).
% 2.00/0.65  fof(f1,axiom,(
% 2.00/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.00/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.00/0.65  fof(f334,plain,(
% 2.00/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_34),
% 2.00/0.65    inference(avatar_component_clause,[],[f332])).
% 2.00/0.65  fof(f335,plain,(
% 2.00/0.65    ~spl4_1 | ~spl4_6 | ~spl4_9 | ~spl4_3 | spl4_34 | ~spl4_11),
% 2.00/0.65    inference(avatar_split_clause,[],[f330,f146,f332,f106,f136,f121,f96])).
% 2.00/0.65  fof(f121,plain,(
% 2.00/0.65    spl4_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.00/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.00/0.65  fof(f146,plain,(
% 2.00/0.65    spl4_11 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.00/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.00/0.65  fof(f330,plain,(
% 2.00/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_11),
% 2.00/0.65    inference(trivial_inequality_removal,[],[f327])).
% 2.00/0.65  fof(f327,plain,(
% 2.00/0.65    sK1 != sK1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_11),
% 2.00/0.65    inference(superposition,[],[f60,f148])).
% 2.00/0.65  fof(f148,plain,(
% 2.00/0.65    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_11),
% 2.00/0.65    inference(avatar_component_clause,[],[f146])).
% 2.00/0.65  fof(f60,plain,(
% 2.00/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.00/0.65    inference(cnf_transformation,[],[f21])).
% 2.00/0.65  fof(f21,plain,(
% 2.00/0.65    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.00/0.65    inference(flattening,[],[f20])).
% 2.00/0.65  fof(f20,plain,(
% 2.00/0.65    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.00/0.65    inference(ennf_transformation,[],[f15])).
% 2.00/0.65  fof(f15,axiom,(
% 2.00/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.00/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 2.00/0.65  fof(f258,plain,(
% 2.00/0.65    ~spl4_1 | ~spl4_6 | ~spl4_9 | ~spl4_3 | spl4_24 | ~spl4_11),
% 2.00/0.65    inference(avatar_split_clause,[],[f253,f146,f255,f106,f136,f121,f96])).
% 2.00/0.65  fof(f253,plain,(
% 2.00/0.65    v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_11),
% 2.00/0.65    inference(trivial_inequality_removal,[],[f250])).
% 2.00/0.65  fof(f250,plain,(
% 2.00/0.65    sK1 != sK1 | v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_11),
% 2.00/0.65    inference(superposition,[],[f58,f148])).
% 2.00/0.65  fof(f58,plain,(
% 2.00/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.00/0.65    inference(cnf_transformation,[],[f21])).
% 2.00/0.65  fof(f243,plain,(
% 2.00/0.65    ~spl4_10 | spl4_23 | ~spl4_22),
% 2.00/0.65    inference(avatar_split_clause,[],[f235,f231,f240,f141])).
% 2.00/0.65  fof(f231,plain,(
% 2.00/0.65    spl4_22 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 2.00/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 2.00/0.65  fof(f235,plain,(
% 2.00/0.65    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_22),
% 2.00/0.65    inference(superposition,[],[f233,f81])).
% 2.00/0.65  fof(f81,plain,(
% 2.00/0.65    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/0.65    inference(cnf_transformation,[],[f36])).
% 2.00/0.65  fof(f36,plain,(
% 2.00/0.65    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.65    inference(ennf_transformation,[],[f7])).
% 2.00/0.65  fof(f7,axiom,(
% 2.00/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.00/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.00/0.65  fof(f233,plain,(
% 2.00/0.65    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_22),
% 2.00/0.65    inference(avatar_component_clause,[],[f231])).
% 2.00/0.65  fof(f234,plain,(
% 2.00/0.65    spl4_22 | spl4_4 | ~spl4_7 | ~spl4_10),
% 2.00/0.65    inference(avatar_split_clause,[],[f211,f141,f126,f111,f231])).
% 2.00/0.65  fof(f111,plain,(
% 2.00/0.65    spl4_4 <=> k1_xboole_0 = sK0),
% 2.00/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.00/0.65  fof(f126,plain,(
% 2.00/0.65    spl4_7 <=> v1_funct_2(sK3,sK1,sK0)),
% 2.00/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.00/0.65  fof(f211,plain,(
% 2.00/0.65    ~v1_funct_2(sK3,sK1,sK0) | k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_10),
% 2.00/0.65    inference(resolution,[],[f65,f143])).
% 2.00/0.65  fof(f65,plain,(
% 2.00/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 2.00/0.65    inference(cnf_transformation,[],[f44])).
% 2.00/0.65  fof(f44,plain,(
% 2.00/0.65    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.65    inference(nnf_transformation,[],[f27])).
% 2.00/0.65  fof(f27,plain,(
% 2.00/0.65    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.65    inference(flattening,[],[f26])).
% 2.00/0.65  fof(f26,plain,(
% 2.00/0.65    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.65    inference(ennf_transformation,[],[f11])).
% 2.00/0.65  fof(f11,axiom,(
% 2.00/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.00/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.00/0.65  fof(f224,plain,(
% 2.00/0.65    ~spl4_9 | spl4_21 | ~spl4_20),
% 2.00/0.65    inference(avatar_split_clause,[],[f218,f214,f221,f136])).
% 2.00/0.65  fof(f214,plain,(
% 2.00/0.65    spl4_20 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 2.00/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 2.00/0.65  fof(f218,plain,(
% 2.00/0.65    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_20),
% 2.00/0.65    inference(superposition,[],[f216,f81])).
% 2.00/0.65  fof(f216,plain,(
% 2.00/0.65    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_20),
% 2.00/0.65    inference(avatar_component_clause,[],[f214])).
% 2.00/0.65  fof(f217,plain,(
% 2.00/0.65    spl4_20 | spl4_5 | ~spl4_6 | ~spl4_9),
% 2.00/0.65    inference(avatar_split_clause,[],[f210,f136,f121,f116,f214])).
% 2.00/0.65  fof(f116,plain,(
% 2.00/0.65    spl4_5 <=> k1_xboole_0 = sK1),
% 2.00/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.00/0.65  fof(f210,plain,(
% 2.00/0.65    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_9),
% 2.00/0.65    inference(resolution,[],[f65,f138])).
% 2.00/0.65  fof(f204,plain,(
% 2.00/0.65    ~spl4_9 | spl4_19 | ~spl4_11),
% 2.00/0.65    inference(avatar_split_clause,[],[f198,f146,f201,f136])).
% 2.00/0.65  fof(f198,plain,(
% 2.00/0.65    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_11),
% 2.00/0.65    inference(superposition,[],[f77,f148])).
% 2.00/0.65  fof(f77,plain,(
% 2.00/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/0.65    inference(cnf_transformation,[],[f32])).
% 2.00/0.65  fof(f32,plain,(
% 2.00/0.65    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.65    inference(ennf_transformation,[],[f8])).
% 2.00/0.65  fof(f8,axiom,(
% 2.00/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.00/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.00/0.65  fof(f196,plain,(
% 2.00/0.65    spl4_17),
% 2.00/0.65    inference(avatar_contradiction_clause,[],[f193])).
% 2.00/0.65  fof(f193,plain,(
% 2.00/0.65    $false | spl4_17),
% 2.00/0.65    inference(unit_resulting_resolution,[],[f79,f187])).
% 2.00/0.65  fof(f187,plain,(
% 2.00/0.65    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_17),
% 2.00/0.65    inference(avatar_component_clause,[],[f185])).
% 2.00/0.65  fof(f79,plain,(
% 2.00/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.00/0.65    inference(cnf_transformation,[],[f2])).
% 2.00/0.65  fof(f2,axiom,(
% 2.00/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.00/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.00/0.65  fof(f192,plain,(
% 2.00/0.65    ~spl4_17 | spl4_18 | ~spl4_10),
% 2.00/0.65    inference(avatar_split_clause,[],[f156,f141,f189,f185])).
% 2.00/0.65  fof(f156,plain,(
% 2.00/0.65    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_10),
% 2.00/0.65    inference(resolution,[],[f78,f143])).
% 2.00/0.65  fof(f170,plain,(
% 2.00/0.65    spl4_13),
% 2.00/0.65    inference(avatar_contradiction_clause,[],[f167])).
% 2.00/0.65  fof(f167,plain,(
% 2.00/0.65    $false | spl4_13),
% 2.00/0.65    inference(unit_resulting_resolution,[],[f79,f161])).
% 2.00/0.65  fof(f161,plain,(
% 2.00/0.65    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_13),
% 2.00/0.65    inference(avatar_component_clause,[],[f159])).
% 2.00/0.65  fof(f159,plain,(
% 2.00/0.65    spl4_13 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.00/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.00/0.65  fof(f166,plain,(
% 2.00/0.65    ~spl4_13 | spl4_14 | ~spl4_9),
% 2.00/0.65    inference(avatar_split_clause,[],[f155,f136,f163,f159])).
% 2.00/0.65  fof(f155,plain,(
% 2.00/0.65    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_9),
% 2.00/0.65    inference(resolution,[],[f78,f138])).
% 2.00/0.65  fof(f154,plain,(
% 2.00/0.65    spl4_12),
% 2.00/0.65    inference(avatar_split_clause,[],[f53,f151])).
% 2.00/0.65  fof(f53,plain,(
% 2.00/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.00/0.65    inference(cnf_transformation,[],[f43])).
% 2.00/0.65  fof(f43,plain,(
% 2.00/0.65    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.00/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f42,f41])).
% 2.00/0.65  fof(f41,plain,(
% 2.00/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.00/0.65    introduced(choice_axiom,[])).
% 2.00/0.66  fof(f42,plain,(
% 2.00/0.66    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.00/0.66    introduced(choice_axiom,[])).
% 2.00/0.66  fof(f19,plain,(
% 2.00/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.00/0.66    inference(flattening,[],[f18])).
% 2.00/0.66  fof(f18,plain,(
% 2.00/0.66    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.00/0.66    inference(ennf_transformation,[],[f17])).
% 2.00/0.66  fof(f17,negated_conjecture,(
% 2.00/0.66    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.00/0.66    inference(negated_conjecture,[],[f16])).
% 2.00/0.66  fof(f16,conjecture,(
% 2.00/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.00/0.66  fof(f149,plain,(
% 2.00/0.66    spl4_11),
% 2.00/0.66    inference(avatar_split_clause,[],[f52,f146])).
% 2.00/0.66  fof(f52,plain,(
% 2.00/0.66    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.00/0.66    inference(cnf_transformation,[],[f43])).
% 2.00/0.66  fof(f144,plain,(
% 2.00/0.66    spl4_10),
% 2.00/0.66    inference(avatar_split_clause,[],[f51,f141])).
% 2.00/0.66  fof(f51,plain,(
% 2.00/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.00/0.66    inference(cnf_transformation,[],[f43])).
% 2.00/0.66  fof(f139,plain,(
% 2.00/0.66    spl4_9),
% 2.00/0.66    inference(avatar_split_clause,[],[f48,f136])).
% 2.00/0.66  fof(f48,plain,(
% 2.00/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.00/0.66    inference(cnf_transformation,[],[f43])).
% 2.00/0.66  fof(f134,plain,(
% 2.00/0.66    ~spl4_8),
% 2.00/0.66    inference(avatar_split_clause,[],[f57,f131])).
% 2.00/0.66  fof(f57,plain,(
% 2.00/0.66    k2_funct_1(sK2) != sK3),
% 2.00/0.66    inference(cnf_transformation,[],[f43])).
% 2.00/0.66  fof(f129,plain,(
% 2.00/0.66    spl4_7),
% 2.00/0.66    inference(avatar_split_clause,[],[f50,f126])).
% 2.00/0.66  fof(f50,plain,(
% 2.00/0.66    v1_funct_2(sK3,sK1,sK0)),
% 2.00/0.66    inference(cnf_transformation,[],[f43])).
% 2.00/0.66  fof(f124,plain,(
% 2.00/0.66    spl4_6),
% 2.00/0.66    inference(avatar_split_clause,[],[f47,f121])).
% 2.00/0.66  fof(f47,plain,(
% 2.00/0.66    v1_funct_2(sK2,sK0,sK1)),
% 2.00/0.66    inference(cnf_transformation,[],[f43])).
% 2.00/0.66  fof(f119,plain,(
% 2.00/0.66    ~spl4_5),
% 2.00/0.66    inference(avatar_split_clause,[],[f56,f116])).
% 2.00/0.66  fof(f56,plain,(
% 2.00/0.66    k1_xboole_0 != sK1),
% 2.00/0.66    inference(cnf_transformation,[],[f43])).
% 2.00/0.66  fof(f114,plain,(
% 2.00/0.66    ~spl4_4),
% 2.00/0.66    inference(avatar_split_clause,[],[f55,f111])).
% 2.00/0.66  fof(f55,plain,(
% 2.00/0.66    k1_xboole_0 != sK0),
% 2.00/0.66    inference(cnf_transformation,[],[f43])).
% 2.00/0.66  fof(f109,plain,(
% 2.00/0.66    spl4_3),
% 2.00/0.66    inference(avatar_split_clause,[],[f54,f106])).
% 2.00/0.66  fof(f54,plain,(
% 2.00/0.66    v2_funct_1(sK2)),
% 2.00/0.66    inference(cnf_transformation,[],[f43])).
% 2.00/0.66  fof(f104,plain,(
% 2.00/0.66    spl4_2),
% 2.00/0.66    inference(avatar_split_clause,[],[f49,f101])).
% 2.00/0.66  fof(f49,plain,(
% 2.00/0.66    v1_funct_1(sK3)),
% 2.00/0.66    inference(cnf_transformation,[],[f43])).
% 2.00/0.66  fof(f99,plain,(
% 2.00/0.66    spl4_1),
% 2.00/0.66    inference(avatar_split_clause,[],[f46,f96])).
% 2.00/0.66  fof(f46,plain,(
% 2.00/0.66    v1_funct_1(sK2)),
% 2.00/0.66    inference(cnf_transformation,[],[f43])).
% 2.00/0.66  % SZS output end Proof for theBenchmark
% 2.00/0.66  % (19232)------------------------------
% 2.00/0.66  % (19232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.66  % (19232)Termination reason: Refutation
% 2.00/0.66  
% 2.00/0.66  % (19232)Memory used [KB]: 11385
% 2.00/0.66  % (19232)Time elapsed: 0.194 s
% 2.00/0.66  % (19232)------------------------------
% 2.00/0.66  % (19232)------------------------------
% 2.00/0.66  % (19228)Refutation not found, incomplete strategy% (19228)------------------------------
% 2.00/0.66  % (19228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.66  % (19228)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.66  
% 2.00/0.66  % (19228)Memory used [KB]: 2046
% 2.00/0.66  % (19228)Time elapsed: 0.206 s
% 2.00/0.66  % (19228)------------------------------
% 2.00/0.66  % (19228)------------------------------
% 2.00/0.66  % (19208)Success in time 0.284 s
%------------------------------------------------------------------------------
