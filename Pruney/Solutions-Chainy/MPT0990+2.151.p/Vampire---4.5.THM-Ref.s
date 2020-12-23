%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 317 expanded)
%              Number of leaves         :   41 ( 118 expanded)
%              Depth                    :   10
%              Number of atoms          :  603 (1570 expanded)
%              Number of equality atoms :  130 ( 436 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f493,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f106,f110,f114,f129,f131,f180,f182,f196,f235,f241,f251,f256,f273,f279,f306,f368,f375,f395,f410,f423,f429,f479,f483,f489,f492])).

fof(f492,plain,(
    ~ spl4_45 ),
    inference(avatar_contradiction_clause,[],[f490])).

fof(f490,plain,
    ( $false
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f47,f488])).

fof(f488,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f486])).

fof(f486,plain,
    ( spl4_45
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f47,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f489,plain,
    ( ~ spl4_1
    | ~ spl4_20
    | ~ spl4_21
    | spl4_45
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f484,f388,f486,f267,f263,f90])).

fof(f90,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f263,plain,
    ( spl4_20
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f267,plain,
    ( spl4_21
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f388,plain,
    ( spl4_34
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f484,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_34 ),
    inference(superposition,[],[f57,f390])).

fof(f390,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f388])).

fof(f57,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f483,plain,(
    spl4_44 ),
    inference(avatar_contradiction_clause,[],[f480])).

fof(f480,plain,
    ( $false
    | spl4_44 ),
    inference(unit_resulting_resolution,[],[f76,f478])).

fof(f478,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_44 ),
    inference(avatar_component_clause,[],[f476])).

fof(f476,plain,
    ( spl4_44
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f76,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f53,f51])).

fof(f51,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f53,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f479,plain,
    ( ~ spl4_3
    | ~ spl4_18
    | ~ spl4_44
    | ~ spl4_6
    | ~ spl4_22
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f474,f326,f271,f125,f476,f224,f99])).

fof(f99,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f224,plain,
    ( spl4_18
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f125,plain,
    ( spl4_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f271,plain,
    ( spl4_22
  <=> ! [X3] :
        ( sK1 != k2_relat_1(X3)
        | ~ v2_funct_1(k5_relat_1(X3,sK3))
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f326,plain,
    ( spl4_28
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f474,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_22
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f473,f328])).

fof(f328,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f326])).

fof(f473,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_22 ),
    inference(trivial_inequality_removal,[],[f471])).

fof(f471,plain,
    ( sK1 != sK1
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_22 ),
    inference(superposition,[],[f272,f127])).

fof(f127,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f272,plain,
    ( ! [X3] :
        ( sK1 != k2_relat_1(X3)
        | ~ v2_funct_1(k5_relat_1(X3,sK3))
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f271])).

fof(f429,plain,
    ( spl4_35
    | ~ spl4_38 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | spl4_35
    | ~ spl4_38 ),
    inference(trivial_inequality_removal,[],[f424])).

fof(f424,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | spl4_35
    | ~ spl4_38 ),
    inference(superposition,[],[f394,f421])).

fof(f421,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl4_38
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f394,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl4_35
  <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f423,plain,
    ( ~ spl4_15
    | spl4_38
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f417,f407,f419,f188])).

fof(f188,plain,
    ( spl4_15
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f407,plain,
    ( spl4_36
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f417,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_36 ),
    inference(superposition,[],[f63,f409])).

fof(f409,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f407])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f410,plain,
    ( spl4_36
    | ~ spl4_21
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_18
    | ~ spl4_15
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f402,f154,f188,f224,f167,f121,f267,f407])).

fof(f121,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f167,plain,
    ( spl4_12
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f154,plain,
    ( spl4_9
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f402,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f70,f43])).

fof(f43,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f395,plain,
    ( spl4_34
    | ~ spl4_1
    | ~ spl4_20
    | ~ spl4_18
    | ~ spl4_3
    | ~ spl4_21
    | ~ spl4_35
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f386,f326,f192,f125,f392,f267,f99,f224,f263,f90,f388])).

fof(f192,plain,
    ( spl4_16
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f386,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_28 ),
    inference(trivial_inequality_removal,[],[f385])).

fof(f385,plain,
    ( sK1 != sK1
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f384,f127])).

fof(f384,plain,
    ( sK1 != k2_relat_1(sK2)
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_16
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f383,f194])).

fof(f194,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f192])).

fof(f383,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_28 ),
    inference(superposition,[],[f78,f328])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f58,f51])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f375,plain,
    ( ~ spl4_18
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_5
    | spl4_28
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f372,f303,f326,f121,f267,f188,f224])).

fof(f303,plain,
    ( spl4_25
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f372,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_25 ),
    inference(superposition,[],[f73,f305])).

fof(f305,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f303])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f368,plain,(
    spl4_24 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | spl4_24 ),
    inference(unit_resulting_resolution,[],[f48,f39,f41,f50,f301,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f301,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl4_24
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f306,plain,
    ( ~ spl4_24
    | spl4_25 ),
    inference(avatar_split_clause,[],[f296,f303,f299])).

fof(f296,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f232,f43])).

fof(f232,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f72,f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f279,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | spl4_21 ),
    inference(subsumption_resolution,[],[f39,f269])).

fof(f269,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f267])).

fof(f273,plain,
    ( spl4_20
    | ~ spl4_1
    | ~ spl4_21
    | spl4_22
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f259,f192,f271,f267,f90,f263])).

fof(f259,plain,
    ( ! [X3] :
        ( sK1 != k2_relat_1(X3)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | ~ v2_funct_1(k5_relat_1(X3,sK3))
        | ~ v1_relat_1(sK3)
        | v2_funct_1(sK3) )
    | ~ spl4_16 ),
    inference(superposition,[],[f60,f194])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f256,plain,
    ( ~ spl4_9
    | spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f253,f162,f158,f154])).

fof(f158,plain,
    ( spl4_10
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f162,plain,
    ( spl4_11
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f253,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(resolution,[],[f41,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f251,plain,(
    ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f45,f164])).

fof(f164,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f162])).

fof(f45,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f241,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f41,f190])).

fof(f190,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f188])).

fof(f235,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl4_18 ),
    inference(subsumption_resolution,[],[f48,f226])).

fof(f226,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f224])).

fof(f196,plain,
    ( ~ spl4_15
    | spl4_16
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f185,f158,f192,f188])).

fof(f185,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_10 ),
    inference(superposition,[],[f62,f160])).

fof(f160,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f158])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f182,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl4_12 ),
    inference(subsumption_resolution,[],[f49,f169])).

fof(f169,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f167])).

fof(f49,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f180,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f40,f156])).

fof(f156,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f154])).

fof(f40,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f131,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f50,f123])).

fof(f123,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f129,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f119,f125,f121])).

fof(f119,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f42,f63])).

fof(f42,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f114,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f61,f105])).

fof(f105,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f110,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f61,f96])).

fof(f96,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f106,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f87,f103,f99])).

fof(f87,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f56,f50])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f97,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f86,f94,f90])).

fof(f86,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f56,f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (3565)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.49  % (3573)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (3559)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (3557)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (3547)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (3564)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (3546)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (3558)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (3549)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (3554)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (3545)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (3548)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (3563)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (3568)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (3560)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (3551)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (3562)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (3574)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (3556)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (3562)Refutation not found, incomplete strategy% (3562)------------------------------
% 0.20/0.54  % (3562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (3562)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (3562)Memory used [KB]: 10746
% 0.20/0.54  % (3562)Time elapsed: 0.123 s
% 0.20/0.54  % (3562)------------------------------
% 0.20/0.54  % (3562)------------------------------
% 0.20/0.54  % (3574)Refutation not found, incomplete strategy% (3574)------------------------------
% 0.20/0.54  % (3574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (3574)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (3574)Memory used [KB]: 11001
% 0.20/0.54  % (3556)Refutation not found, incomplete strategy% (3556)------------------------------
% 0.20/0.54  % (3556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (3574)Time elapsed: 0.132 s
% 0.20/0.54  % (3574)------------------------------
% 0.20/0.54  % (3574)------------------------------
% 0.20/0.54  % (3556)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (3556)Memory used [KB]: 11001
% 0.20/0.54  % (3556)Time elapsed: 0.132 s
% 0.20/0.54  % (3556)------------------------------
% 0.20/0.54  % (3556)------------------------------
% 0.20/0.54  % (3561)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (3566)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (3555)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (3553)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (3575)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (3572)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (3569)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.56  % (3567)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.56  % (3570)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.56  % (3552)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (3571)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.57  % (3559)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f493,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f97,f106,f110,f114,f129,f131,f180,f182,f196,f235,f241,f251,f256,f273,f279,f306,f368,f375,f395,f410,f423,f429,f479,f483,f489,f492])).
% 0.20/0.57  fof(f492,plain,(
% 0.20/0.57    ~spl4_45),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f490])).
% 0.20/0.57  fof(f490,plain,(
% 0.20/0.57    $false | ~spl4_45),
% 0.20/0.57    inference(subsumption_resolution,[],[f47,f488])).
% 0.20/0.57  fof(f488,plain,(
% 0.20/0.57    sK3 = k2_funct_1(sK2) | ~spl4_45),
% 0.20/0.57    inference(avatar_component_clause,[],[f486])).
% 0.20/0.57  fof(f486,plain,(
% 0.20/0.57    spl4_45 <=> sK3 = k2_funct_1(sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    sK3 != k2_funct_1(sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.57    inference(flattening,[],[f18])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f17])).
% 0.20/0.57  fof(f17,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.20/0.57    inference(negated_conjecture,[],[f16])).
% 0.20/0.57  fof(f16,conjecture,(
% 0.20/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 0.20/0.57  fof(f489,plain,(
% 0.20/0.57    ~spl4_1 | ~spl4_20 | ~spl4_21 | spl4_45 | ~spl4_34),
% 0.20/0.57    inference(avatar_split_clause,[],[f484,f388,f486,f267,f263,f90])).
% 0.20/0.57  fof(f90,plain,(
% 0.20/0.57    spl4_1 <=> v1_relat_1(sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.57  fof(f263,plain,(
% 0.20/0.57    spl4_20 <=> v2_funct_1(sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.57  fof(f267,plain,(
% 0.20/0.57    spl4_21 <=> v1_funct_1(sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.57  fof(f388,plain,(
% 0.20/0.57    spl4_34 <=> sK2 = k2_funct_1(sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.20/0.57  fof(f484,plain,(
% 0.20/0.57    sK3 = k2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_34),
% 0.20/0.57    inference(superposition,[],[f57,f390])).
% 0.20/0.57  fof(f390,plain,(
% 0.20/0.57    sK2 = k2_funct_1(sK3) | ~spl4_34),
% 0.20/0.57    inference(avatar_component_clause,[],[f388])).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.20/0.57  fof(f483,plain,(
% 0.20/0.57    spl4_44),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f480])).
% 0.20/0.57  fof(f480,plain,(
% 0.20/0.57    $false | spl4_44),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f76,f478])).
% 0.20/0.57  fof(f478,plain,(
% 0.20/0.57    ~v2_funct_1(k6_partfun1(sK0)) | spl4_44),
% 0.20/0.57    inference(avatar_component_clause,[],[f476])).
% 0.20/0.57  fof(f476,plain,(
% 0.20/0.57    spl4_44 <=> v2_funct_1(k6_partfun1(sK0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f53,f51])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,axiom,(
% 0.20/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.57  fof(f479,plain,(
% 0.20/0.57    ~spl4_3 | ~spl4_18 | ~spl4_44 | ~spl4_6 | ~spl4_22 | ~spl4_28),
% 0.20/0.57    inference(avatar_split_clause,[],[f474,f326,f271,f125,f476,f224,f99])).
% 0.20/0.57  fof(f99,plain,(
% 0.20/0.57    spl4_3 <=> v1_relat_1(sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.57  fof(f224,plain,(
% 0.20/0.57    spl4_18 <=> v1_funct_1(sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.57  fof(f125,plain,(
% 0.20/0.57    spl4_6 <=> sK1 = k2_relat_1(sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.57  fof(f271,plain,(
% 0.20/0.57    spl4_22 <=> ! [X3] : (sK1 != k2_relat_1(X3) | ~v2_funct_1(k5_relat_1(X3,sK3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.57  fof(f326,plain,(
% 0.20/0.57    spl4_28 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.57  fof(f474,plain,(
% 0.20/0.57    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_6 | ~spl4_22 | ~spl4_28)),
% 0.20/0.57    inference(forward_demodulation,[],[f473,f328])).
% 0.20/0.57  fof(f328,plain,(
% 0.20/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_28),
% 0.20/0.57    inference(avatar_component_clause,[],[f326])).
% 0.20/0.57  fof(f473,plain,(
% 0.20/0.57    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_6 | ~spl4_22)),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f471])).
% 0.20/0.57  fof(f471,plain,(
% 0.20/0.57    sK1 != sK1 | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_6 | ~spl4_22)),
% 0.20/0.57    inference(superposition,[],[f272,f127])).
% 0.20/0.57  fof(f127,plain,(
% 0.20/0.57    sK1 = k2_relat_1(sK2) | ~spl4_6),
% 0.20/0.57    inference(avatar_component_clause,[],[f125])).
% 0.20/0.57  fof(f272,plain,(
% 0.20/0.57    ( ! [X3] : (sK1 != k2_relat_1(X3) | ~v2_funct_1(k5_relat_1(X3,sK3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) ) | ~spl4_22),
% 0.20/0.57    inference(avatar_component_clause,[],[f271])).
% 0.20/0.57  fof(f429,plain,(
% 0.20/0.57    spl4_35 | ~spl4_38),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f428])).
% 0.20/0.57  fof(f428,plain,(
% 0.20/0.57    $false | (spl4_35 | ~spl4_38)),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f424])).
% 0.20/0.57  fof(f424,plain,(
% 0.20/0.57    k6_partfun1(sK0) != k6_partfun1(sK0) | (spl4_35 | ~spl4_38)),
% 0.20/0.57    inference(superposition,[],[f394,f421])).
% 0.20/0.57  fof(f421,plain,(
% 0.20/0.57    sK0 = k2_relat_1(sK3) | ~spl4_38),
% 0.20/0.57    inference(avatar_component_clause,[],[f419])).
% 0.20/0.57  fof(f419,plain,(
% 0.20/0.57    spl4_38 <=> sK0 = k2_relat_1(sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.20/0.57  fof(f394,plain,(
% 0.20/0.57    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | spl4_35),
% 0.20/0.57    inference(avatar_component_clause,[],[f392])).
% 0.20/0.57  fof(f392,plain,(
% 0.20/0.57    spl4_35 <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.20/0.57  fof(f423,plain,(
% 0.20/0.57    ~spl4_15 | spl4_38 | ~spl4_36),
% 0.20/0.57    inference(avatar_split_clause,[],[f417,f407,f419,f188])).
% 0.20/0.57  fof(f188,plain,(
% 0.20/0.57    spl4_15 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.57  fof(f407,plain,(
% 0.20/0.57    spl4_36 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.20/0.57  fof(f417,plain,(
% 0.20/0.57    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_36),
% 0.20/0.57    inference(superposition,[],[f63,f409])).
% 0.20/0.57  fof(f409,plain,(
% 0.20/0.57    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_36),
% 0.20/0.57    inference(avatar_component_clause,[],[f407])).
% 0.20/0.57  fof(f63,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.57  fof(f410,plain,(
% 0.20/0.57    spl4_36 | ~spl4_21 | ~spl4_5 | ~spl4_12 | ~spl4_18 | ~spl4_15 | ~spl4_9),
% 0.20/0.57    inference(avatar_split_clause,[],[f402,f154,f188,f224,f167,f121,f267,f407])).
% 0.20/0.57  fof(f121,plain,(
% 0.20/0.57    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.57  fof(f167,plain,(
% 0.20/0.57    spl4_12 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.57  fof(f154,plain,(
% 0.20/0.57    spl4_9 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.57  fof(f402,plain,(
% 0.20/0.57    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.20/0.57    inference(resolution,[],[f70,f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f70,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.57    inference(flattening,[],[f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 0.20/0.57  fof(f395,plain,(
% 0.20/0.57    spl4_34 | ~spl4_1 | ~spl4_20 | ~spl4_18 | ~spl4_3 | ~spl4_21 | ~spl4_35 | ~spl4_6 | ~spl4_16 | ~spl4_28),
% 0.20/0.57    inference(avatar_split_clause,[],[f386,f326,f192,f125,f392,f267,f99,f224,f263,f90,f388])).
% 0.20/0.57  fof(f192,plain,(
% 0.20/0.57    spl4_16 <=> sK1 = k1_relat_1(sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.57  fof(f386,plain,(
% 0.20/0.57    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_6 | ~spl4_16 | ~spl4_28)),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f385])).
% 0.20/0.57  fof(f385,plain,(
% 0.20/0.57    sK1 != sK1 | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_6 | ~spl4_16 | ~spl4_28)),
% 0.20/0.57    inference(forward_demodulation,[],[f384,f127])).
% 0.20/0.57  fof(f384,plain,(
% 0.20/0.57    sK1 != k2_relat_1(sK2) | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_16 | ~spl4_28)),
% 0.20/0.57    inference(forward_demodulation,[],[f383,f194])).
% 0.20/0.57  fof(f194,plain,(
% 0.20/0.57    sK1 = k1_relat_1(sK3) | ~spl4_16),
% 0.20/0.57    inference(avatar_component_clause,[],[f192])).
% 0.20/0.57  fof(f383,plain,(
% 0.20/0.57    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~spl4_28),
% 0.20/0.57    inference(superposition,[],[f78,f328])).
% 0.20/0.57  fof(f78,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 0.20/0.57    inference(definition_unfolding,[],[f58,f51])).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f23])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 0.20/0.57  fof(f375,plain,(
% 0.20/0.57    ~spl4_18 | ~spl4_15 | ~spl4_21 | ~spl4_5 | spl4_28 | ~spl4_25),
% 0.20/0.57    inference(avatar_split_clause,[],[f372,f303,f326,f121,f267,f188,f224])).
% 0.20/0.57  fof(f303,plain,(
% 0.20/0.57    spl4_25 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.57  fof(f372,plain,(
% 0.20/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_25),
% 0.20/0.57    inference(superposition,[],[f73,f305])).
% 0.20/0.57  fof(f305,plain,(
% 0.20/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_25),
% 0.20/0.57    inference(avatar_component_clause,[],[f303])).
% 0.20/0.57  fof(f73,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.57    inference(flattening,[],[f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.57    inference(ennf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.20/0.57  fof(f368,plain,(
% 0.20/0.57    spl4_24),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f354])).
% 0.20/0.57  fof(f354,plain,(
% 0.20/0.57    $false | spl4_24),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f48,f39,f41,f50,f301,f75])).
% 0.20/0.57  fof(f75,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.57    inference(flattening,[],[f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.20/0.57  fof(f301,plain,(
% 0.20/0.57    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_24),
% 0.20/0.57    inference(avatar_component_clause,[],[f299])).
% 0.20/0.57  fof(f299,plain,(
% 0.20/0.57    spl4_24 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    v1_funct_1(sK3)),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    v1_funct_1(sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f306,plain,(
% 0.20/0.57    ~spl4_24 | spl4_25),
% 0.20/0.57    inference(avatar_split_clause,[],[f296,f303,f299])).
% 0.20/0.57  fof(f296,plain,(
% 0.20/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.57    inference(resolution,[],[f232,f43])).
% 0.20/0.57  fof(f232,plain,(
% 0.20/0.57    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 0.20/0.57    inference(resolution,[],[f72,f55])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f12])).
% 0.20/0.57  fof(f12,axiom,(
% 0.20/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.20/0.57  fof(f72,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(flattening,[],[f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.57    inference(ennf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.57  fof(f279,plain,(
% 0.20/0.57    spl4_21),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f278])).
% 0.20/0.57  fof(f278,plain,(
% 0.20/0.57    $false | spl4_21),
% 0.20/0.57    inference(subsumption_resolution,[],[f39,f269])).
% 0.20/0.57  fof(f269,plain,(
% 0.20/0.57    ~v1_funct_1(sK3) | spl4_21),
% 0.20/0.57    inference(avatar_component_clause,[],[f267])).
% 0.20/0.57  fof(f273,plain,(
% 0.20/0.57    spl4_20 | ~spl4_1 | ~spl4_21 | spl4_22 | ~spl4_16),
% 0.20/0.57    inference(avatar_split_clause,[],[f259,f192,f271,f267,f90,f263])).
% 0.20/0.57  fof(f259,plain,(
% 0.20/0.57    ( ! [X3] : (sK1 != k2_relat_1(X3) | ~v1_funct_1(sK3) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | ~v2_funct_1(k5_relat_1(X3,sK3)) | ~v1_relat_1(sK3) | v2_funct_1(sK3)) ) | ~spl4_16),
% 0.20/0.57    inference(superposition,[],[f60,f194])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 0.20/0.57  fof(f256,plain,(
% 0.20/0.57    ~spl4_9 | spl4_10 | spl4_11),
% 0.20/0.57    inference(avatar_split_clause,[],[f253,f162,f158,f154])).
% 0.20/0.57  fof(f158,plain,(
% 0.20/0.57    spl4_10 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.57  fof(f162,plain,(
% 0.20/0.57    spl4_11 <=> k1_xboole_0 = sK0),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.57  fof(f253,plain,(
% 0.20/0.57    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.57    inference(resolution,[],[f41,f69])).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(flattening,[],[f29])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.57  fof(f251,plain,(
% 0.20/0.57    ~spl4_11),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f242])).
% 0.20/0.57  fof(f242,plain,(
% 0.20/0.57    $false | ~spl4_11),
% 0.20/0.57    inference(subsumption_resolution,[],[f45,f164])).
% 0.20/0.57  fof(f164,plain,(
% 0.20/0.57    k1_xboole_0 = sK0 | ~spl4_11),
% 0.20/0.57    inference(avatar_component_clause,[],[f162])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    k1_xboole_0 != sK0),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f241,plain,(
% 0.20/0.57    spl4_15),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f240])).
% 0.20/0.57  fof(f240,plain,(
% 0.20/0.57    $false | spl4_15),
% 0.20/0.57    inference(subsumption_resolution,[],[f41,f190])).
% 0.20/0.57  fof(f190,plain,(
% 0.20/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_15),
% 0.20/0.57    inference(avatar_component_clause,[],[f188])).
% 0.20/0.57  fof(f235,plain,(
% 0.20/0.57    spl4_18),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f234])).
% 0.20/0.57  fof(f234,plain,(
% 0.20/0.57    $false | spl4_18),
% 0.20/0.57    inference(subsumption_resolution,[],[f48,f226])).
% 0.20/0.57  fof(f226,plain,(
% 0.20/0.57    ~v1_funct_1(sK2) | spl4_18),
% 0.20/0.57    inference(avatar_component_clause,[],[f224])).
% 0.20/0.57  fof(f196,plain,(
% 0.20/0.57    ~spl4_15 | spl4_16 | ~spl4_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f185,f158,f192,f188])).
% 0.20/0.57  fof(f185,plain,(
% 0.20/0.57    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_10),
% 0.20/0.57    inference(superposition,[],[f62,f160])).
% 0.20/0.57  fof(f160,plain,(
% 0.20/0.57    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_10),
% 0.20/0.57    inference(avatar_component_clause,[],[f158])).
% 0.20/0.57  fof(f62,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.57  fof(f182,plain,(
% 0.20/0.57    spl4_12),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f181])).
% 0.20/0.57  fof(f181,plain,(
% 0.20/0.57    $false | spl4_12),
% 0.20/0.57    inference(subsumption_resolution,[],[f49,f169])).
% 0.20/0.57  fof(f169,plain,(
% 0.20/0.57    ~v1_funct_2(sK2,sK0,sK1) | spl4_12),
% 0.20/0.57    inference(avatar_component_clause,[],[f167])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f180,plain,(
% 0.20/0.57    spl4_9),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f179])).
% 0.20/0.57  fof(f179,plain,(
% 0.20/0.57    $false | spl4_9),
% 0.20/0.57    inference(subsumption_resolution,[],[f40,f156])).
% 0.20/0.57  fof(f156,plain,(
% 0.20/0.57    ~v1_funct_2(sK3,sK1,sK0) | spl4_9),
% 0.20/0.57    inference(avatar_component_clause,[],[f154])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f131,plain,(
% 0.20/0.57    spl4_5),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f130])).
% 0.20/0.57  fof(f130,plain,(
% 0.20/0.57    $false | spl4_5),
% 0.20/0.57    inference(subsumption_resolution,[],[f50,f123])).
% 0.20/0.57  fof(f123,plain,(
% 0.20/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_5),
% 0.20/0.57    inference(avatar_component_clause,[],[f121])).
% 0.20/0.57  fof(f129,plain,(
% 0.20/0.57    ~spl4_5 | spl4_6),
% 0.20/0.57    inference(avatar_split_clause,[],[f119,f125,f121])).
% 0.20/0.57  fof(f119,plain,(
% 0.20/0.57    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.57    inference(superposition,[],[f42,f63])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f114,plain,(
% 0.20/0.57    spl4_4),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f111])).
% 0.20/0.57  fof(f111,plain,(
% 0.20/0.57    $false | spl4_4),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f61,f105])).
% 0.20/0.57  fof(f105,plain,(
% 0.20/0.57    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 0.20/0.57    inference(avatar_component_clause,[],[f103])).
% 0.20/0.57  fof(f103,plain,(
% 0.20/0.57    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.57  fof(f61,plain,(
% 0.20/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.57  fof(f110,plain,(
% 0.20/0.57    spl4_2),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f107])).
% 0.20/0.57  fof(f107,plain,(
% 0.20/0.57    $false | spl4_2),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f61,f96])).
% 0.20/0.57  fof(f96,plain,(
% 0.20/0.57    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f94])).
% 0.20/0.57  fof(f94,plain,(
% 0.20/0.57    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.57  fof(f106,plain,(
% 0.20/0.57    spl4_3 | ~spl4_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f87,f103,f99])).
% 0.20/0.57  fof(f87,plain,(
% 0.20/0.57    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 0.20/0.57    inference(resolution,[],[f56,f50])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f20])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.57  fof(f97,plain,(
% 0.20/0.57    spl4_1 | ~spl4_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f86,f94,f90])).
% 0.20/0.57  fof(f86,plain,(
% 0.20/0.57    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 0.20/0.57    inference(resolution,[],[f56,f41])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (3559)------------------------------
% 0.20/0.57  % (3559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (3559)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (3559)Memory used [KB]: 6652
% 0.20/0.57  % (3559)Time elapsed: 0.141 s
% 0.20/0.57  % (3559)------------------------------
% 0.20/0.57  % (3559)------------------------------
% 0.20/0.57  % (3544)Success in time 0.211 s
%------------------------------------------------------------------------------
