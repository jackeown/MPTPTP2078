%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 325 expanded)
%              Number of leaves         :   39 ( 109 expanded)
%              Depth                    :    8
%              Number of atoms          :  516 (1676 expanded)
%              Number of equality atoms :  133 ( 517 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f701,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f132,f241,f243,f246,f268,f281,f283,f292,f294,f307,f321,f331,f345,f358,f360,f418,f454,f467,f474,f554,f565,f633,f649,f692])).

fof(f692,plain,
    ( ~ spl4_55
    | ~ spl4_56 ),
    inference(avatar_contradiction_clause,[],[f674])).

fof(f674,plain,
    ( $false
    | ~ spl4_55
    | ~ spl4_56 ),
    inference(subsumption_resolution,[],[f52,f673])).

fof(f673,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_55
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f625,f632])).

fof(f632,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f630])).

fof(f630,plain,
    ( spl4_56
  <=> sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f625,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f623])).

fof(f623,plain,
    ( spl4_55
  <=> k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f52,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f649,plain,
    ( ~ spl4_3
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | spl4_55
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f643,f327,f623,f232,f228,f224,f123])).

fof(f123,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f224,plain,
    ( spl4_10
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f228,plain,
    ( spl4_11
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f232,plain,
    ( spl4_12
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f327,plain,
    ( spl4_23
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f643,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_23 ),
    inference(superposition,[],[f106,f329])).

fof(f329,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f327])).

fof(f106,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_partfun1(k1_relat_1(X0)))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f88,f67])).

fof(f67,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f88,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f61,f56])).

fof(f56,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f633,plain,
    ( ~ spl4_25
    | spl4_56
    | ~ spl4_26
    | ~ spl4_38
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f628,f563,f460,f355,f630,f351])).

fof(f351,plain,
    ( spl4_25
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f355,plain,
    ( spl4_26
  <=> sK3 = k5_relat_1(k6_partfun1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f460,plain,
    ( spl4_38
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f563,plain,
    ( spl4_49
  <=> ! [X0] :
        ( k5_relat_1(k6_partfun1(sK1),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f628,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(sK3)
    | ~ spl4_26
    | ~ spl4_38
    | ~ spl4_49 ),
    inference(forward_demodulation,[],[f616,f357])).

fof(f357,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f355])).

fof(f616,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(sK3)
    | ~ spl4_38
    | ~ spl4_49 ),
    inference(superposition,[],[f564,f462])).

fof(f462,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f460])).

fof(f564,plain,
    ( ! [X0] :
        ( k5_relat_1(k6_partfun1(sK1),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f563])).

fof(f565,plain,
    ( ~ spl4_12
    | ~ spl4_3
    | spl4_49
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f556,f551,f563,f123,f232])).

fof(f551,plain,
    ( spl4_47
  <=> k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f556,plain,
    ( ! [X0] :
        ( k5_relat_1(k6_partfun1(sK1),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0))
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl4_47 ),
    inference(superposition,[],[f63,f553])).

fof(f553,plain,
    ( k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f551])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f554,plain,
    ( spl4_47
    | spl4_20
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_1
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f549,f270,f110,f228,f224,f278,f551])).

fof(f278,plain,
    ( spl4_20
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f110,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f270,plain,
    ( spl4_18
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f549,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(trivial_inequality_removal,[],[f546])).

fof(f546,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(superposition,[],[f80,f47])).

fof(f47,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f474,plain,
    ( ~ spl4_11
    | ~ spl4_21
    | ~ spl4_32
    | ~ spl4_1
    | spl4_38
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f471,f451,f460,f110,f409,f313,f228])).

fof(f313,plain,
    ( spl4_21
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f409,plain,
    ( spl4_32
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f451,plain,
    ( spl4_36
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f471,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_36 ),
    inference(superposition,[],[f83,f453])).

fof(f453,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f451])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f467,plain,(
    spl4_35 ),
    inference(avatar_contradiction_clause,[],[f464])).

fof(f464,plain,
    ( $false
    | spl4_35 ),
    inference(unit_resulting_resolution,[],[f53,f44,f46,f55,f449,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f449,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl4_35
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f454,plain,
    ( ~ spl4_35
    | spl4_36 ),
    inference(avatar_split_clause,[],[f443,f451,f447])).

fof(f443,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f342,f48])).

fof(f48,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f342,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f82,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f418,plain,(
    spl4_32 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | spl4_32 ),
    inference(subsumption_resolution,[],[f44,f411])).

fof(f411,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_32 ),
    inference(avatar_component_clause,[],[f409])).

fof(f360,plain,(
    spl4_25 ),
    inference(avatar_contradiction_clause,[],[f359])).

fof(f359,plain,
    ( $false
    | spl4_25 ),
    inference(subsumption_resolution,[],[f97,f353])).

fof(f353,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f351])).

fof(f97,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f70,f46])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f358,plain,
    ( ~ spl4_25
    | spl4_26
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f349,f317,f355,f351])).

fof(f317,plain,
    ( spl4_22
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f349,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_22 ),
    inference(superposition,[],[f89,f319])).

fof(f319,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f317])).

fof(f89,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f62,f56])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f345,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | spl4_21 ),
    inference(subsumption_resolution,[],[f46,f315])).

fof(f315,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f313])).

fof(f331,plain,
    ( ~ spl4_1
    | spl4_23
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f324,f274,f327,f110])).

fof(f274,plain,
    ( spl4_19
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f324,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_19 ),
    inference(superposition,[],[f71,f276])).

fof(f276,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f274])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f321,plain,
    ( ~ spl4_21
    | spl4_22
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f310,f261,f317,f313])).

fof(f261,plain,
    ( spl4_16
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f310,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_16 ),
    inference(superposition,[],[f71,f263])).

fof(f263,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f261])).

fof(f307,plain,(
    ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f51,f280])).

fof(f280,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f278])).

fof(f51,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f294,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | spl4_18 ),
    inference(subsumption_resolution,[],[f54,f272])).

fof(f272,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f270])).

fof(f54,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f292,plain,(
    ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f50,f267])).

fof(f267,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl4_17
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f50,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f283,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f45,f259])).

fof(f259,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl4_15
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f45,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f281,plain,
    ( ~ spl4_18
    | spl4_19
    | spl4_20 ),
    inference(avatar_split_clause,[],[f255,f278,f274,f270])).

fof(f255,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f78,f55])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f268,plain,
    ( ~ spl4_15
    | spl4_16
    | spl4_17 ),
    inference(avatar_split_clause,[],[f253,f265,f261,f257])).

fof(f253,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(resolution,[],[f78,f46])).

fof(f246,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl4_12 ),
    inference(unit_resulting_resolution,[],[f98,f53,f234,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f234,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f232])).

fof(f98,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f70,f55])).

fof(f243,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f53,f230])).

fof(f230,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f228])).

fof(f241,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f49,f226])).

fof(f226,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f224])).

fof(f49,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f132,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f98,f125])).

fof(f125,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f123])).

fof(f120,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f55,f112])).

fof(f112,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (22163)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.50  % (22150)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (22171)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (22157)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (22161)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (22162)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (22160)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (22165)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (22179)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (22172)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (22164)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (22152)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (22174)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (22169)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (22156)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (22154)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (22151)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (22155)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (22153)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (22173)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (22167)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (22166)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (22166)Refutation not found, incomplete strategy% (22166)------------------------------
% 0.21/0.54  % (22166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22166)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22166)Memory used [KB]: 10746
% 0.21/0.54  % (22166)Time elapsed: 0.139 s
% 0.21/0.54  % (22166)------------------------------
% 0.21/0.54  % (22166)------------------------------
% 0.21/0.54  % (22175)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (22158)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (22177)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (22178)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (22176)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (22159)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (22168)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (22170)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (22163)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f701,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f120,f132,f241,f243,f246,f268,f281,f283,f292,f294,f307,f321,f331,f345,f358,f360,f418,f454,f467,f474,f554,f565,f633,f649,f692])).
% 0.21/0.56  fof(f692,plain,(
% 0.21/0.56    ~spl4_55 | ~spl4_56),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f674])).
% 0.21/0.56  fof(f674,plain,(
% 0.21/0.56    $false | (~spl4_55 | ~spl4_56)),
% 0.21/0.56    inference(subsumption_resolution,[],[f52,f673])).
% 0.21/0.56  fof(f673,plain,(
% 0.21/0.56    sK3 = k2_funct_1(sK2) | (~spl4_55 | ~spl4_56)),
% 0.21/0.56    inference(forward_demodulation,[],[f625,f632])).
% 0.21/0.56  fof(f632,plain,(
% 0.21/0.56    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_56),
% 0.21/0.56    inference(avatar_component_clause,[],[f630])).
% 0.21/0.56  fof(f630,plain,(
% 0.21/0.56    spl4_56 <=> sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.21/0.56  fof(f625,plain,(
% 0.21/0.56    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_55),
% 0.21/0.56    inference(avatar_component_clause,[],[f623])).
% 0.21/0.56  fof(f623,plain,(
% 0.21/0.56    spl4_55 <=> k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    sK3 != k2_funct_1(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.56    inference(flattening,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.57    inference(negated_conjecture,[],[f18])).
% 0.21/0.57  fof(f18,conjecture,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 0.21/0.57  fof(f649,plain,(
% 0.21/0.57    ~spl4_3 | ~spl4_10 | ~spl4_11 | ~spl4_12 | spl4_55 | ~spl4_23),
% 0.21/0.57    inference(avatar_split_clause,[],[f643,f327,f623,f232,f228,f224,f123])).
% 0.21/0.57  fof(f123,plain,(
% 0.21/0.57    spl4_3 <=> v1_relat_1(sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.57  fof(f224,plain,(
% 0.21/0.57    spl4_10 <=> v2_funct_1(sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.57  fof(f228,plain,(
% 0.21/0.57    spl4_11 <=> v1_funct_1(sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.57  fof(f232,plain,(
% 0.21/0.57    spl4_12 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.57  fof(f327,plain,(
% 0.21/0.57    spl4_23 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.57  fof(f643,plain,(
% 0.21/0.57    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_23),
% 0.21/0.57    inference(superposition,[],[f106,f329])).
% 0.21/0.57  fof(f329,plain,(
% 0.21/0.57    sK0 = k1_relat_1(sK2) | ~spl4_23),
% 0.21/0.57    inference(avatar_component_clause,[],[f327])).
% 0.21/0.57  fof(f106,plain,(
% 0.21/0.57    ( ! [X0] : (k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_partfun1(k1_relat_1(X0))) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(superposition,[],[f88,f67])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f61,f56])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,axiom,(
% 0.21/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.57  fof(f633,plain,(
% 0.21/0.57    ~spl4_25 | spl4_56 | ~spl4_26 | ~spl4_38 | ~spl4_49),
% 0.21/0.57    inference(avatar_split_clause,[],[f628,f563,f460,f355,f630,f351])).
% 0.21/0.57  fof(f351,plain,(
% 0.21/0.57    spl4_25 <=> v1_relat_1(sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.57  fof(f355,plain,(
% 0.21/0.57    spl4_26 <=> sK3 = k5_relat_1(k6_partfun1(sK1),sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.57  fof(f460,plain,(
% 0.21/0.57    spl4_38 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.57  fof(f563,plain,(
% 0.21/0.57    spl4_49 <=> ! [X0] : (k5_relat_1(k6_partfun1(sK1),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) | ~v1_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.21/0.57  fof(f628,plain,(
% 0.21/0.57    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(sK3) | (~spl4_26 | ~spl4_38 | ~spl4_49)),
% 0.21/0.57    inference(forward_demodulation,[],[f616,f357])).
% 0.21/0.57  fof(f357,plain,(
% 0.21/0.57    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_26),
% 0.21/0.57    inference(avatar_component_clause,[],[f355])).
% 0.21/0.57  fof(f616,plain,(
% 0.21/0.57    k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(sK3) | (~spl4_38 | ~spl4_49)),
% 0.21/0.57    inference(superposition,[],[f564,f462])).
% 0.21/0.57  fof(f462,plain,(
% 0.21/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_38),
% 0.21/0.57    inference(avatar_component_clause,[],[f460])).
% 0.21/0.57  fof(f564,plain,(
% 0.21/0.57    ( ! [X0] : (k5_relat_1(k6_partfun1(sK1),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) | ~v1_relat_1(X0)) ) | ~spl4_49),
% 0.21/0.57    inference(avatar_component_clause,[],[f563])).
% 0.21/0.57  fof(f565,plain,(
% 0.21/0.57    ~spl4_12 | ~spl4_3 | spl4_49 | ~spl4_47),
% 0.21/0.57    inference(avatar_split_clause,[],[f556,f551,f563,f123,f232])).
% 0.21/0.57  fof(f551,plain,(
% 0.21/0.57    spl4_47 <=> k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.21/0.57  fof(f556,plain,(
% 0.21/0.57    ( ! [X0] : (k5_relat_1(k6_partfun1(sK1),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK2))) ) | ~spl4_47),
% 0.21/0.57    inference(superposition,[],[f63,f553])).
% 0.21/0.57  fof(f553,plain,(
% 0.21/0.57    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~spl4_47),
% 0.21/0.57    inference(avatar_component_clause,[],[f551])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.57  fof(f554,plain,(
% 0.21/0.57    spl4_47 | spl4_20 | ~spl4_10 | ~spl4_11 | ~spl4_1 | ~spl4_18),
% 0.21/0.57    inference(avatar_split_clause,[],[f549,f270,f110,f228,f224,f278,f551])).
% 0.21/0.57  fof(f278,plain,(
% 0.21/0.57    spl4_20 <=> k1_xboole_0 = sK1),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.57  fof(f110,plain,(
% 0.21/0.57    spl4_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.57  fof(f270,plain,(
% 0.21/0.57    spl4_18 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.57  fof(f549,plain,(
% 0.21/0.57    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f546])).
% 0.21/0.57  fof(f546,plain,(
% 0.21/0.57    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 0.21/0.57    inference(superposition,[],[f80,f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.57    inference(flattening,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 0.21/0.57  fof(f474,plain,(
% 0.21/0.57    ~spl4_11 | ~spl4_21 | ~spl4_32 | ~spl4_1 | spl4_38 | ~spl4_36),
% 0.21/0.57    inference(avatar_split_clause,[],[f471,f451,f460,f110,f409,f313,f228])).
% 0.21/0.57  fof(f313,plain,(
% 0.21/0.57    spl4_21 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.57  fof(f409,plain,(
% 0.21/0.57    spl4_32 <=> v1_funct_1(sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.57  fof(f451,plain,(
% 0.21/0.57    spl4_36 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.57  fof(f471,plain,(
% 0.21/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_36),
% 0.21/0.57    inference(superposition,[],[f83,f453])).
% 0.21/0.57  fof(f453,plain,(
% 0.21/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_36),
% 0.21/0.57    inference(avatar_component_clause,[],[f451])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.57    inference(flattening,[],[f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.57  fof(f467,plain,(
% 0.21/0.57    spl4_35),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f464])).
% 0.21/0.57  fof(f464,plain,(
% 0.21/0.57    $false | spl4_35),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f53,f44,f46,f55,f449,f85])).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.57    inference(flattening,[],[f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.21/0.57  fof(f449,plain,(
% 0.21/0.57    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_35),
% 0.21/0.57    inference(avatar_component_clause,[],[f447])).
% 0.21/0.57  fof(f447,plain,(
% 0.21/0.57    spl4_35 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    v1_funct_1(sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    v1_funct_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f454,plain,(
% 0.21/0.57    ~spl4_35 | spl4_36),
% 0.21/0.57    inference(avatar_split_clause,[],[f443,f451,f447])).
% 0.21/0.57  fof(f443,plain,(
% 0.21/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.57    inference(resolution,[],[f342,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f342,plain,(
% 0.21/0.57    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 0.21/0.57    inference(resolution,[],[f82,f58])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.57  fof(f82,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(flattening,[],[f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.57  fof(f418,plain,(
% 0.21/0.57    spl4_32),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f417])).
% 0.21/0.57  fof(f417,plain,(
% 0.21/0.57    $false | spl4_32),
% 0.21/0.57    inference(subsumption_resolution,[],[f44,f411])).
% 0.21/0.57  fof(f411,plain,(
% 0.21/0.57    ~v1_funct_1(sK3) | spl4_32),
% 0.21/0.57    inference(avatar_component_clause,[],[f409])).
% 0.21/0.57  fof(f360,plain,(
% 0.21/0.57    spl4_25),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f359])).
% 0.21/0.57  fof(f359,plain,(
% 0.21/0.57    $false | spl4_25),
% 0.21/0.57    inference(subsumption_resolution,[],[f97,f353])).
% 0.21/0.57  fof(f353,plain,(
% 0.21/0.57    ~v1_relat_1(sK3) | spl4_25),
% 0.21/0.57    inference(avatar_component_clause,[],[f351])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    v1_relat_1(sK3)),
% 0.21/0.57    inference(resolution,[],[f70,f46])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.57  fof(f358,plain,(
% 0.21/0.57    ~spl4_25 | spl4_26 | ~spl4_22),
% 0.21/0.57    inference(avatar_split_clause,[],[f349,f317,f355,f351])).
% 0.21/0.57  fof(f317,plain,(
% 0.21/0.57    spl4_22 <=> sK1 = k1_relat_1(sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.57  fof(f349,plain,(
% 0.21/0.57    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | ~v1_relat_1(sK3) | ~spl4_22),
% 0.21/0.57    inference(superposition,[],[f89,f319])).
% 0.21/0.57  fof(f319,plain,(
% 0.21/0.57    sK1 = k1_relat_1(sK3) | ~spl4_22),
% 0.21/0.57    inference(avatar_component_clause,[],[f317])).
% 0.21/0.57  fof(f89,plain,(
% 0.21/0.57    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f62,f56])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 0.21/0.57  fof(f345,plain,(
% 0.21/0.57    spl4_21),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f344])).
% 0.21/0.57  fof(f344,plain,(
% 0.21/0.57    $false | spl4_21),
% 0.21/0.57    inference(subsumption_resolution,[],[f46,f315])).
% 0.21/0.57  fof(f315,plain,(
% 0.21/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_21),
% 0.21/0.57    inference(avatar_component_clause,[],[f313])).
% 0.21/0.57  fof(f331,plain,(
% 0.21/0.57    ~spl4_1 | spl4_23 | ~spl4_19),
% 0.21/0.57    inference(avatar_split_clause,[],[f324,f274,f327,f110])).
% 0.21/0.57  fof(f274,plain,(
% 0.21/0.57    spl4_19 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.57  fof(f324,plain,(
% 0.21/0.57    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_19),
% 0.21/0.57    inference(superposition,[],[f71,f276])).
% 0.21/0.57  fof(f276,plain,(
% 0.21/0.57    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_19),
% 0.21/0.57    inference(avatar_component_clause,[],[f274])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.57  fof(f321,plain,(
% 0.21/0.57    ~spl4_21 | spl4_22 | ~spl4_16),
% 0.21/0.57    inference(avatar_split_clause,[],[f310,f261,f317,f313])).
% 0.21/0.57  fof(f261,plain,(
% 0.21/0.57    spl4_16 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.57  fof(f310,plain,(
% 0.21/0.57    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_16),
% 0.21/0.57    inference(superposition,[],[f71,f263])).
% 0.21/0.57  fof(f263,plain,(
% 0.21/0.57    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_16),
% 0.21/0.57    inference(avatar_component_clause,[],[f261])).
% 0.21/0.57  fof(f307,plain,(
% 0.21/0.57    ~spl4_20),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f295])).
% 0.21/0.57  fof(f295,plain,(
% 0.21/0.57    $false | ~spl4_20),
% 0.21/0.57    inference(subsumption_resolution,[],[f51,f280])).
% 0.21/0.57  fof(f280,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | ~spl4_20),
% 0.21/0.57    inference(avatar_component_clause,[],[f278])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    k1_xboole_0 != sK1),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f294,plain,(
% 0.21/0.57    spl4_18),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f293])).
% 0.21/0.57  fof(f293,plain,(
% 0.21/0.57    $false | spl4_18),
% 0.21/0.57    inference(subsumption_resolution,[],[f54,f272])).
% 0.21/0.57  fof(f272,plain,(
% 0.21/0.57    ~v1_funct_2(sK2,sK0,sK1) | spl4_18),
% 0.21/0.57    inference(avatar_component_clause,[],[f270])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f292,plain,(
% 0.21/0.57    ~spl4_17),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f284])).
% 0.21/0.57  fof(f284,plain,(
% 0.21/0.57    $false | ~spl4_17),
% 0.21/0.57    inference(subsumption_resolution,[],[f50,f267])).
% 0.21/0.57  fof(f267,plain,(
% 0.21/0.57    k1_xboole_0 = sK0 | ~spl4_17),
% 0.21/0.57    inference(avatar_component_clause,[],[f265])).
% 0.21/0.57  fof(f265,plain,(
% 0.21/0.57    spl4_17 <=> k1_xboole_0 = sK0),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    k1_xboole_0 != sK0),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f283,plain,(
% 0.21/0.57    spl4_15),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f282])).
% 0.21/0.57  fof(f282,plain,(
% 0.21/0.57    $false | spl4_15),
% 0.21/0.57    inference(subsumption_resolution,[],[f45,f259])).
% 0.21/0.57  fof(f259,plain,(
% 0.21/0.57    ~v1_funct_2(sK3,sK1,sK0) | spl4_15),
% 0.21/0.57    inference(avatar_component_clause,[],[f257])).
% 0.21/0.57  fof(f257,plain,(
% 0.21/0.57    spl4_15 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f281,plain,(
% 0.21/0.57    ~spl4_18 | spl4_19 | spl4_20),
% 0.21/0.57    inference(avatar_split_clause,[],[f255,f278,f274,f270])).
% 0.21/0.57  fof(f255,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.57    inference(resolution,[],[f78,f55])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(flattening,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.57  fof(f268,plain,(
% 0.21/0.57    ~spl4_15 | spl4_16 | spl4_17),
% 0.21/0.57    inference(avatar_split_clause,[],[f253,f265,f261,f257])).
% 0.21/0.57  fof(f253,plain,(
% 0.21/0.57    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.57    inference(resolution,[],[f78,f46])).
% 0.21/0.57  fof(f246,plain,(
% 0.21/0.57    spl4_12),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f244])).
% 0.21/0.57  fof(f244,plain,(
% 0.21/0.57    $false | spl4_12),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f98,f53,f234,f64])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.57  fof(f234,plain,(
% 0.21/0.57    ~v1_relat_1(k2_funct_1(sK2)) | spl4_12),
% 0.21/0.57    inference(avatar_component_clause,[],[f232])).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    v1_relat_1(sK2)),
% 0.21/0.57    inference(resolution,[],[f70,f55])).
% 0.21/0.57  fof(f243,plain,(
% 0.21/0.57    spl4_11),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f242])).
% 0.21/0.57  fof(f242,plain,(
% 0.21/0.57    $false | spl4_11),
% 0.21/0.57    inference(subsumption_resolution,[],[f53,f230])).
% 0.21/0.57  fof(f230,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | spl4_11),
% 0.21/0.57    inference(avatar_component_clause,[],[f228])).
% 0.21/0.57  fof(f241,plain,(
% 0.21/0.57    spl4_10),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f240])).
% 0.21/0.57  fof(f240,plain,(
% 0.21/0.57    $false | spl4_10),
% 0.21/0.57    inference(subsumption_resolution,[],[f49,f226])).
% 0.21/0.57  fof(f226,plain,(
% 0.21/0.57    ~v2_funct_1(sK2) | spl4_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f224])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    v2_funct_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f132,plain,(
% 0.21/0.57    spl4_3),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f131])).
% 0.21/0.57  fof(f131,plain,(
% 0.21/0.57    $false | spl4_3),
% 0.21/0.57    inference(subsumption_resolution,[],[f98,f125])).
% 0.21/0.57  fof(f125,plain,(
% 0.21/0.57    ~v1_relat_1(sK2) | spl4_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f123])).
% 0.21/0.57  fof(f120,plain,(
% 0.21/0.57    spl4_1),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f119])).
% 0.21/0.57  fof(f119,plain,(
% 0.21/0.57    $false | spl4_1),
% 0.21/0.57    inference(subsumption_resolution,[],[f55,f112])).
% 0.21/0.57  fof(f112,plain,(
% 0.21/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f110])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (22163)------------------------------
% 0.21/0.57  % (22163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (22163)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (22163)Memory used [KB]: 6780
% 0.21/0.57  % (22163)Time elapsed: 0.160 s
% 0.21/0.57  % (22163)------------------------------
% 0.21/0.57  % (22163)------------------------------
% 1.66/0.57  % (22149)Success in time 0.215 s
%------------------------------------------------------------------------------
