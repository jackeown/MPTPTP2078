%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:53 EST 2020

% Result     : Theorem 2.24s
% Output     : Refutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :  274 (1412 expanded)
%              Number of leaves         :   37 ( 453 expanded)
%              Depth                    :   28
%              Number of atoms          : 1104 (12543 expanded)
%              Number of equality atoms :  277 (4252 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1092,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f199,f204,f336,f486,f490,f553,f562,f663,f695,f716,f1044,f1048,f1084])).

fof(f1084,plain,
    ( ~ spl4_2
    | ~ spl4_15
    | ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f1083])).

fof(f1083,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_15
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f1069,f211])).

fof(f211,plain,
    ( sK3 != k4_relat_1(sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f78,f198])).

fof(f198,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl4_2
  <=> k2_funct_1(sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f78,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f63,f62])).

fof(f62,plain,
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

fof(f63,plain,
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

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
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
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
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

fof(f1069,plain,
    ( sK3 = k4_relat_1(sK2)
    | ~ spl4_15
    | ~ spl4_25 ),
    inference(backward_demodulation,[],[f566,f1043])).

fof(f1043,plain,
    ( sK2 = k4_relat_1(sK3)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f1041])).

fof(f1041,plain,
    ( spl4_25
  <=> sK2 = k4_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f566,plain,
    ( sK3 = k4_relat_1(k4_relat_1(sK3))
    | ~ spl4_15 ),
    inference(resolution,[],[f543,f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f543,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f542])).

fof(f542,plain,
    ( spl4_15
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1048,plain,
    ( ~ spl4_15
    | spl4_24 ),
    inference(avatar_contradiction_clause,[],[f1047])).

fof(f1047,plain,
    ( $false
    | ~ spl4_15
    | spl4_24 ),
    inference(subsumption_resolution,[],[f1045,f543])).

fof(f1045,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_24 ),
    inference(resolution,[],[f1039,f118])).

fof(f118,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f1039,plain,
    ( ~ v1_relat_1(k4_relat_1(sK3))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f1037])).

fof(f1037,plain,
    ( spl4_24
  <=> v1_relat_1(k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f1044,plain,
    ( ~ spl4_24
    | spl4_25
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f1035,f550,f542,f483,f479,f329,f196,f192,f1041,f1037])).

fof(f192,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f329,plain,
    ( spl4_3
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f479,plain,
    ( spl4_13
  <=> v1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f483,plain,
    ( spl4_14
  <=> v2_funct_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f550,plain,
    ( spl4_17
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f1035,plain,
    ( sK2 = k4_relat_1(sK3)
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f1034,f761])).

fof(f761,plain,
    ( v1_funct_1(k4_relat_1(sK3))
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f760,f543])).

fof(f760,plain,
    ( v1_funct_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f757,f70])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f757,plain,
    ( v1_funct_1(k4_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(superposition,[],[f93,f749])).

fof(f749,plain,
    ( k4_relat_1(sK3) = k2_funct_1(sK3)
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f748,f543])).

fof(f748,plain,
    ( k4_relat_1(sK3) = k2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f732,f70])).

fof(f732,plain,
    ( k4_relat_1(sK3) = k2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_17 ),
    inference(resolution,[],[f552,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f552,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f550])).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f1034,plain,
    ( sK2 = k4_relat_1(sK3)
    | ~ v1_funct_1(k4_relat_1(sK3))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f1025,f755])).

fof(f755,plain,
    ( sK1 = k2_relat_1(k4_relat_1(sK3))
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(backward_demodulation,[],[f747,f749])).

fof(f747,plain,
    ( sK1 = k2_relat_1(k2_funct_1(sK3))
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f746,f224])).

fof(f224,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f159,f153])).

fof(f153,plain,(
    sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(global_subsumption,[],[f72,f152])).

fof(f152,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f151,f76])).

fof(f76,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f64])).

fof(f151,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f71,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f71,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f64])).

fof(f159,plain,(
    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f72,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f746,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f745,f543])).

fof(f745,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f731,f70])).

fof(f731,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_17 ),
    inference(resolution,[],[f552,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f1025,plain,
    ( sK2 = k4_relat_1(sK3)
    | sK1 != k2_relat_1(k4_relat_1(sK3))
    | ~ v1_funct_1(k4_relat_1(sK3))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(trivial_inequality_removal,[],[f1024])).

fof(f1024,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK2 = k4_relat_1(sK3)
    | sK1 != k2_relat_1(k4_relat_1(sK3))
    | ~ v1_funct_1(k4_relat_1(sK3))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(superposition,[],[f1007,f717])).

fof(f717,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f710,f126])).

fof(f126,plain,(
    ! [X0] : k6_partfun1(X0) = k4_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f116,f106,f106])).

fof(f106,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f116,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f710,plain,
    ( k4_relat_1(k6_partfun1(sK0)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f565,f331])).

fof(f331,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f329])).

fof(f565,plain,
    ( k4_relat_1(k5_relat_1(sK2,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_15 ),
    inference(resolution,[],[f543,f207])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k5_relat_1(sK2,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(sK2)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f193,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f193,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f192])).

fof(f1007,plain,
    ( ! [X2] :
        ( k6_partfun1(sK0) != k5_relat_1(X2,k4_relat_1(sK2))
        | sK2 = X2
        | sK1 != k2_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f1006,f531])).

fof(f531,plain,
    ( sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f530,f205])).

fof(f205,plain,
    ( sK2 = k4_relat_1(k4_relat_1(sK2))
    | ~ spl4_1 ),
    inference(resolution,[],[f193,f117])).

fof(f530,plain,
    ( k4_relat_1(k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f529,f480])).

fof(f480,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f479])).

fof(f529,plain,
    ( k4_relat_1(k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f510,f217])).

fof(f217,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f216,f193])).

fof(f216,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f213,f67])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f213,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f93,f198])).

fof(f510,plain,
    ( k4_relat_1(k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_14 ),
    inference(resolution,[],[f485,f91])).

fof(f485,plain,
    ( v2_funct_1(k4_relat_1(sK2))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f483])).

fof(f1006,plain,
    ( ! [X2] :
        ( k6_partfun1(sK0) != k5_relat_1(X2,k4_relat_1(sK2))
        | sK1 != k2_relat_1(X2)
        | k2_funct_1(k4_relat_1(sK2)) = X2
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f1005,f480])).

fof(f1005,plain,
    ( ! [X2] :
        ( k6_partfun1(sK0) != k5_relat_1(X2,k4_relat_1(sK2))
        | sK1 != k2_relat_1(X2)
        | k2_funct_1(k4_relat_1(sK2)) = X2
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k4_relat_1(sK2)) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f271,f485])).

fof(f271,plain,
    ( ! [X2] :
        ( k6_partfun1(sK0) != k5_relat_1(X2,k4_relat_1(sK2))
        | sK1 != k2_relat_1(X2)
        | k2_funct_1(k4_relat_1(sK2)) = X2
        | ~ v2_funct_1(k4_relat_1(sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k4_relat_1(sK2)) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f270,f238])).

fof(f238,plain,
    ( sK0 = k2_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f237,f201])).

fof(f201,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f154,f150])).

fof(f150,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f69,f149])).

fof(f149,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f148,f77])).

fof(f77,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f64])).

fof(f148,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f68,f94])).

fof(f68,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f64])).

fof(f154,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f69,f119])).

fof(f237,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f236,f198])).

fof(f236,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f146,f193])).

fof(f146,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f139,f67])).

fof(f139,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f75,f90])).

fof(f75,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f270,plain,
    ( ! [X2] :
        ( sK1 != k2_relat_1(X2)
        | k5_relat_1(X2,k4_relat_1(sK2)) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
        | k2_funct_1(k4_relat_1(sK2)) = X2
        | ~ v2_funct_1(k4_relat_1(sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k4_relat_1(sK2)) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f267,f217])).

fof(f267,plain,
    ( ! [X2] :
        ( sK1 != k2_relat_1(X2)
        | k5_relat_1(X2,k4_relat_1(sK2)) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
        | k2_funct_1(k4_relat_1(sK2)) = X2
        | ~ v2_funct_1(k4_relat_1(sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(k4_relat_1(sK2))
        | ~ v1_relat_1(k4_relat_1(sK2)) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f120,f257])).

fof(f257,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f229,f256])).

fof(f256,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f255,f125])).

fof(f125,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f114,f106])).

fof(f114,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f255,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_partfun1(sK1))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f254,f227])).

fof(f227,plain,
    ( k6_partfun1(sK1) = k5_relat_1(k4_relat_1(sK2),sK2)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f183,f198])).

fof(f183,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f182,f67])).

fof(f182,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f181,f68])).

fof(f181,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f180,f69])).

fof(f180,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f179,f75])).

fof(f179,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f167,f77])).

fof(f167,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f166])).

fof(f166,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f80,f73])).

fof(f73,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f254,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k5_relat_1(k4_relat_1(sK2),sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f253,f198])).

fof(f253,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f143,f193])).

fof(f143,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f136,f67])).

fof(f136,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f75,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(f229,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f228,f198])).

fof(f228,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f145,f193])).

fof(f145,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f138,f67])).

fof(f138,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f75,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k2_relat_1(X1)
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f84,f106])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f716,plain,
    ( ~ spl4_3
    | spl4_16 ),
    inference(avatar_contradiction_clause,[],[f715])).

fof(f715,plain,
    ( $false
    | ~ spl4_3
    | spl4_16 ),
    inference(subsumption_resolution,[],[f709,f121])).

fof(f121,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f103,f106])).

fof(f103,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f709,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ spl4_3
    | spl4_16 ),
    inference(backward_demodulation,[],[f548,f331])).

fof(f548,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f546])).

fof(f546,plain,
    ( spl4_16
  <=> v2_funct_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f695,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_4
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f694])).

fof(f694,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_4
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f693,f67])).

fof(f693,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_4
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f692,f69])).

fof(f692,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_4
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f691,f217])).

fof(f691,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_4
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f690,f452])).

fof(f452,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f451])).

fof(f451,plain,
    ( spl4_9
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f690,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_4
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f685,f335])).

fof(f335,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl4_4
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f685,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(superposition,[],[f108,f676])).

fof(f676,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f675,f226])).

fof(f226,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f178,f198])).

fof(f178,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f177,f67])).

fof(f177,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f176,f68])).

fof(f176,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f175,f69])).

fof(f175,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f174,f75])).

fof(f174,plain,
    ( ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f168,f77])).

fof(f168,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f165])).

fof(f165,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f79,f73])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f675,plain,
    ( k5_relat_1(sK2,k4_relat_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f668,f217])).

fof(f668,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | k5_relat_1(sK2,k4_relat_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))
    | ~ spl4_9 ),
    inference(resolution,[],[f452,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f155,f67])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f69,f109])).

fof(f109,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f663,plain,
    ( ~ spl4_2
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f662])).

fof(f662,plain,
    ( $false
    | ~ spl4_2
    | spl4_9 ),
    inference(subsumption_resolution,[],[f661,f453])).

fof(f453,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f451])).

fof(f661,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f660,f69])).

fof(f660,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f659,f73])).

fof(f659,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_2 ),
    inference(resolution,[],[f221,f68])).

fof(f221,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(sK2,X3,X2)
        | k2_relset_1(X3,X2,sK2) != X2
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f220,f67])).

fof(f220,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k2_relset_1(X3,X2,sK2) != X2
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ v1_funct_2(sK2,X3,X2)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f215,f75])).

fof(f215,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k2_relset_1(X3,X2,sK2) != X2
        | ~ v2_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ v1_funct_2(sK2,X3,X2)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_2 ),
    inference(superposition,[],[f83,f198])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
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

fof(f562,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f561])).

fof(f561,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f560,f111])).

fof(f111,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f560,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_15 ),
    inference(resolution,[],[f554,f72])).

fof(f554,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_15 ),
    inference(resolution,[],[f544,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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

fof(f544,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f542])).

fof(f553,plain,
    ( ~ spl4_15
    | ~ spl4_16
    | spl4_17
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f477,f196,f192,f550,f546,f542])).

fof(f477,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f472,f70])).

fof(f472,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f471])).

fof(f471,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f262,f224])).

fof(f262,plain,
    ( ! [X1] :
        ( sK1 != k1_relat_1(X1)
        | v2_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(sK2,X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f261,f193])).

fof(f261,plain,
    ( ! [X1] :
        ( sK1 != k1_relat_1(X1)
        | v2_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(sK2,X1))
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f259,f67])).

fof(f259,plain,
    ( ! [X1] :
        ( sK1 != k1_relat_1(X1)
        | v2_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(sK2,X1))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f101,f256])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k2_relat_1(X1)
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f490,plain,
    ( ~ spl4_1
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | ~ spl4_1
    | spl4_13 ),
    inference(subsumption_resolution,[],[f487,f193])).

fof(f487,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_13 ),
    inference(resolution,[],[f481,f118])).

fof(f481,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f479])).

fof(f486,plain,
    ( ~ spl4_13
    | spl4_14
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f476,f196,f192,f483,f479])).

fof(f476,plain,
    ( v2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f475,f121])).

fof(f475,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f474,f226])).

fof(f474,plain,
    ( v2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k5_relat_1(sK2,k4_relat_1(sK2)))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f473,f217])).

fof(f473,plain,
    ( v2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k5_relat_1(sK2,k4_relat_1(sK2)))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f468])).

fof(f468,plain,
    ( sK1 != sK1
    | v2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k5_relat_1(sK2,k4_relat_1(sK2)))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f262,f257])).

fof(f336,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f327,f333,f329])).

fof(f327,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f325,f326])).

fof(f326,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f315,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f315,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f74,f290])).

fof(f290,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f286,f70])).

fof(f286,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f157,f72])).

fof(f74,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f64])).

fof(f325,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f324,f67])).

fof(f324,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f323,f69])).

fof(f323,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f322,f70])).

fof(f322,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f317,f72])).

fof(f317,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f108,f290])).

fof(f204,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f202,f111])).

fof(f202,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_1 ),
    inference(resolution,[],[f200,f69])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_1 ),
    inference(resolution,[],[f194,f110])).

fof(f194,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f192])).

fof(f199,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f147,f196,f192])).

fof(f147,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f140,f67])).

fof(f140,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f75,f91])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:57:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.55  % (15561)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.56  % (15557)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.56  % (15565)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.58  % (15564)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.58  % (15577)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.58  % (15560)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.59  % (15573)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.59  % (15562)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.59  % (15573)Refutation not found, incomplete strategy% (15573)------------------------------
% 0.20/0.59  % (15573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (15559)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.60  % (15581)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.60  % (15573)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.60  
% 0.20/0.60  % (15573)Memory used [KB]: 10746
% 0.20/0.60  % (15573)Time elapsed: 0.156 s
% 0.20/0.60  % (15573)------------------------------
% 0.20/0.60  % (15573)------------------------------
% 0.20/0.61  % (15563)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.61  % (15585)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.61  % (15558)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.61  % (15567)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.84/0.62  % (15583)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.84/0.62  % (15572)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.84/0.63  % (15587)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.84/0.63  % (15584)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.84/0.63  % (15578)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.84/0.63  % (15575)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.84/0.63  % (15576)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.84/0.63  % (15566)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.84/0.63  % (15582)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.84/0.63  % (15574)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.84/0.64  % (15570)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 2.12/0.64  % (15579)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 2.12/0.64  % (15586)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.12/0.64  % (15568)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 2.12/0.65  % (15571)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 2.12/0.65  % (15569)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 2.24/0.71  % (15582)Refutation found. Thanks to Tanya!
% 2.24/0.71  % SZS status Theorem for theBenchmark
% 2.24/0.71  % SZS output start Proof for theBenchmark
% 2.24/0.71  fof(f1092,plain,(
% 2.24/0.71    $false),
% 2.24/0.71    inference(avatar_sat_refutation,[],[f199,f204,f336,f486,f490,f553,f562,f663,f695,f716,f1044,f1048,f1084])).
% 2.24/0.71  fof(f1084,plain,(
% 2.24/0.71    ~spl4_2 | ~spl4_15 | ~spl4_25),
% 2.24/0.71    inference(avatar_contradiction_clause,[],[f1083])).
% 2.24/0.71  fof(f1083,plain,(
% 2.24/0.71    $false | (~spl4_2 | ~spl4_15 | ~spl4_25)),
% 2.24/0.71    inference(subsumption_resolution,[],[f1069,f211])).
% 2.24/0.71  fof(f211,plain,(
% 2.24/0.71    sK3 != k4_relat_1(sK2) | ~spl4_2),
% 2.24/0.71    inference(superposition,[],[f78,f198])).
% 2.24/0.71  fof(f198,plain,(
% 2.24/0.71    k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl4_2),
% 2.24/0.71    inference(avatar_component_clause,[],[f196])).
% 2.24/0.71  fof(f196,plain,(
% 2.24/0.71    spl4_2 <=> k2_funct_1(sK2) = k4_relat_1(sK2)),
% 2.24/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.24/0.71  fof(f78,plain,(
% 2.24/0.71    k2_funct_1(sK2) != sK3),
% 2.24/0.71    inference(cnf_transformation,[],[f64])).
% 2.24/0.71  fof(f64,plain,(
% 2.24/0.71    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.24/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f63,f62])).
% 2.24/0.71  fof(f62,plain,(
% 2.24/0.71    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.24/0.71    introduced(choice_axiom,[])).
% 2.24/0.71  fof(f63,plain,(
% 2.24/0.71    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.24/0.71    introduced(choice_axiom,[])).
% 2.24/0.71  fof(f29,plain,(
% 2.24/0.71    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.24/0.71    inference(flattening,[],[f28])).
% 2.24/0.71  fof(f28,plain,(
% 2.24/0.71    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.24/0.71    inference(ennf_transformation,[],[f27])).
% 2.24/0.71  fof(f27,negated_conjecture,(
% 2.24/0.71    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.24/0.71    inference(negated_conjecture,[],[f26])).
% 2.24/0.71  fof(f26,conjecture,(
% 2.24/0.71    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 2.24/0.71  fof(f1069,plain,(
% 2.24/0.71    sK3 = k4_relat_1(sK2) | (~spl4_15 | ~spl4_25)),
% 2.24/0.71    inference(backward_demodulation,[],[f566,f1043])).
% 2.24/0.71  fof(f1043,plain,(
% 2.24/0.71    sK2 = k4_relat_1(sK3) | ~spl4_25),
% 2.24/0.71    inference(avatar_component_clause,[],[f1041])).
% 2.24/0.71  fof(f1041,plain,(
% 2.24/0.71    spl4_25 <=> sK2 = k4_relat_1(sK3)),
% 2.24/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 2.24/0.71  fof(f566,plain,(
% 2.24/0.71    sK3 = k4_relat_1(k4_relat_1(sK3)) | ~spl4_15),
% 2.24/0.71    inference(resolution,[],[f543,f117])).
% 2.24/0.71  fof(f117,plain,(
% 2.24/0.71    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 2.24/0.71    inference(cnf_transformation,[],[f59])).
% 2.24/0.71  fof(f59,plain,(
% 2.24/0.71    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.24/0.71    inference(ennf_transformation,[],[f4])).
% 2.24/0.71  fof(f4,axiom,(
% 2.24/0.71    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 2.24/0.71  fof(f543,plain,(
% 2.24/0.71    v1_relat_1(sK3) | ~spl4_15),
% 2.24/0.71    inference(avatar_component_clause,[],[f542])).
% 2.24/0.71  fof(f542,plain,(
% 2.24/0.71    spl4_15 <=> v1_relat_1(sK3)),
% 2.24/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.24/0.71  fof(f1048,plain,(
% 2.24/0.71    ~spl4_15 | spl4_24),
% 2.24/0.71    inference(avatar_contradiction_clause,[],[f1047])).
% 2.24/0.71  fof(f1047,plain,(
% 2.24/0.71    $false | (~spl4_15 | spl4_24)),
% 2.24/0.71    inference(subsumption_resolution,[],[f1045,f543])).
% 2.24/0.71  fof(f1045,plain,(
% 2.24/0.71    ~v1_relat_1(sK3) | spl4_24),
% 2.24/0.71    inference(resolution,[],[f1039,f118])).
% 2.24/0.71  fof(f118,plain,(
% 2.24/0.71    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.24/0.71    inference(cnf_transformation,[],[f60])).
% 2.24/0.71  fof(f60,plain,(
% 2.24/0.71    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.24/0.71    inference(ennf_transformation,[],[f2])).
% 2.24/0.71  fof(f2,axiom,(
% 2.24/0.71    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 2.24/0.71  fof(f1039,plain,(
% 2.24/0.71    ~v1_relat_1(k4_relat_1(sK3)) | spl4_24),
% 2.24/0.71    inference(avatar_component_clause,[],[f1037])).
% 2.24/0.71  fof(f1037,plain,(
% 2.24/0.71    spl4_24 <=> v1_relat_1(k4_relat_1(sK3))),
% 2.24/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.24/0.71  fof(f1044,plain,(
% 2.24/0.71    ~spl4_24 | spl4_25 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_17),
% 2.24/0.71    inference(avatar_split_clause,[],[f1035,f550,f542,f483,f479,f329,f196,f192,f1041,f1037])).
% 2.24/0.71  fof(f192,plain,(
% 2.24/0.71    spl4_1 <=> v1_relat_1(sK2)),
% 2.24/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.24/0.71  fof(f329,plain,(
% 2.24/0.71    spl4_3 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.24/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.24/0.71  fof(f479,plain,(
% 2.24/0.71    spl4_13 <=> v1_relat_1(k4_relat_1(sK2))),
% 2.24/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.24/0.71  fof(f483,plain,(
% 2.24/0.71    spl4_14 <=> v2_funct_1(k4_relat_1(sK2))),
% 2.24/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.24/0.71  fof(f550,plain,(
% 2.24/0.71    spl4_17 <=> v2_funct_1(sK3)),
% 2.24/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 2.24/0.71  fof(f1035,plain,(
% 2.24/0.71    sK2 = k4_relat_1(sK3) | ~v1_relat_1(k4_relat_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_17)),
% 2.24/0.71    inference(subsumption_resolution,[],[f1034,f761])).
% 2.24/0.71  fof(f761,plain,(
% 2.24/0.71    v1_funct_1(k4_relat_1(sK3)) | (~spl4_15 | ~spl4_17)),
% 2.24/0.71    inference(subsumption_resolution,[],[f760,f543])).
% 2.24/0.71  fof(f760,plain,(
% 2.24/0.71    v1_funct_1(k4_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_15 | ~spl4_17)),
% 2.24/0.71    inference(subsumption_resolution,[],[f757,f70])).
% 2.24/0.71  fof(f70,plain,(
% 2.24/0.71    v1_funct_1(sK3)),
% 2.24/0.71    inference(cnf_transformation,[],[f64])).
% 2.24/0.71  fof(f757,plain,(
% 2.24/0.71    v1_funct_1(k4_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_15 | ~spl4_17)),
% 2.24/0.71    inference(superposition,[],[f93,f749])).
% 2.24/0.71  fof(f749,plain,(
% 2.24/0.71    k4_relat_1(sK3) = k2_funct_1(sK3) | (~spl4_15 | ~spl4_17)),
% 2.24/0.71    inference(subsumption_resolution,[],[f748,f543])).
% 2.24/0.71  fof(f748,plain,(
% 2.24/0.71    k4_relat_1(sK3) = k2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_17),
% 2.24/0.71    inference(subsumption_resolution,[],[f732,f70])).
% 2.24/0.71  fof(f732,plain,(
% 2.24/0.71    k4_relat_1(sK3) = k2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_17),
% 2.24/0.71    inference(resolution,[],[f552,f91])).
% 2.24/0.71  fof(f91,plain,(
% 2.24/0.71    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.24/0.71    inference(cnf_transformation,[],[f43])).
% 2.24/0.71  fof(f43,plain,(
% 2.24/0.71    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.24/0.71    inference(flattening,[],[f42])).
% 2.24/0.71  fof(f42,plain,(
% 2.24/0.71    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.24/0.71    inference(ennf_transformation,[],[f9])).
% 2.24/0.71  fof(f9,axiom,(
% 2.24/0.71    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 2.24/0.71  fof(f552,plain,(
% 2.24/0.71    v2_funct_1(sK3) | ~spl4_17),
% 2.24/0.71    inference(avatar_component_clause,[],[f550])).
% 2.24/0.71  fof(f93,plain,(
% 2.24/0.71    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.24/0.71    inference(cnf_transformation,[],[f45])).
% 2.24/0.71  fof(f45,plain,(
% 2.24/0.71    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.24/0.71    inference(flattening,[],[f44])).
% 2.24/0.71  fof(f44,plain,(
% 2.24/0.71    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.24/0.71    inference(ennf_transformation,[],[f10])).
% 2.24/0.71  fof(f10,axiom,(
% 2.24/0.71    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.24/0.71  fof(f1034,plain,(
% 2.24/0.71    sK2 = k4_relat_1(sK3) | ~v1_funct_1(k4_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_17)),
% 2.24/0.71    inference(subsumption_resolution,[],[f1025,f755])).
% 2.24/0.71  fof(f755,plain,(
% 2.24/0.71    sK1 = k2_relat_1(k4_relat_1(sK3)) | (~spl4_15 | ~spl4_17)),
% 2.24/0.71    inference(backward_demodulation,[],[f747,f749])).
% 2.24/0.71  fof(f747,plain,(
% 2.24/0.71    sK1 = k2_relat_1(k2_funct_1(sK3)) | (~spl4_15 | ~spl4_17)),
% 2.24/0.71    inference(forward_demodulation,[],[f746,f224])).
% 2.24/0.71  fof(f224,plain,(
% 2.24/0.71    sK1 = k1_relat_1(sK3)),
% 2.24/0.71    inference(forward_demodulation,[],[f159,f153])).
% 2.24/0.71  fof(f153,plain,(
% 2.24/0.71    sK1 = k1_relset_1(sK1,sK0,sK3)),
% 2.24/0.71    inference(global_subsumption,[],[f72,f152])).
% 2.24/0.71  fof(f152,plain,(
% 2.24/0.71    sK1 = k1_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.24/0.71    inference(subsumption_resolution,[],[f151,f76])).
% 2.24/0.71  fof(f76,plain,(
% 2.24/0.71    k1_xboole_0 != sK0),
% 2.24/0.71    inference(cnf_transformation,[],[f64])).
% 2.24/0.71  fof(f151,plain,(
% 2.24/0.71    sK1 = k1_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.24/0.71    inference(resolution,[],[f71,f94])).
% 2.24/0.71  fof(f94,plain,(
% 2.24/0.71    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.24/0.71    inference(cnf_transformation,[],[f65])).
% 2.24/0.71  fof(f65,plain,(
% 2.24/0.71    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/0.71    inference(nnf_transformation,[],[f47])).
% 2.24/0.71  fof(f47,plain,(
% 2.24/0.71    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/0.71    inference(flattening,[],[f46])).
% 2.24/0.71  fof(f46,plain,(
% 2.24/0.71    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/0.71    inference(ennf_transformation,[],[f19])).
% 2.24/0.71  fof(f19,axiom,(
% 2.24/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.24/0.71  fof(f71,plain,(
% 2.24/0.71    v1_funct_2(sK3,sK1,sK0)),
% 2.24/0.71    inference(cnf_transformation,[],[f64])).
% 2.24/0.71  fof(f72,plain,(
% 2.24/0.71    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.24/0.71    inference(cnf_transformation,[],[f64])).
% 2.24/0.71  fof(f159,plain,(
% 2.24/0.71    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)),
% 2.24/0.71    inference(resolution,[],[f72,f119])).
% 2.24/0.71  fof(f119,plain,(
% 2.24/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.24/0.71    inference(cnf_transformation,[],[f61])).
% 2.24/0.71  fof(f61,plain,(
% 2.24/0.71    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/0.71    inference(ennf_transformation,[],[f17])).
% 2.24/0.71  fof(f17,axiom,(
% 2.24/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.24/0.71  fof(f746,plain,(
% 2.24/0.71    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | (~spl4_15 | ~spl4_17)),
% 2.24/0.71    inference(subsumption_resolution,[],[f745,f543])).
% 2.24/0.71  fof(f745,plain,(
% 2.24/0.71    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~spl4_17),
% 2.24/0.71    inference(subsumption_resolution,[],[f731,f70])).
% 2.24/0.71  fof(f731,plain,(
% 2.24/0.71    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_17),
% 2.24/0.71    inference(resolution,[],[f552,f90])).
% 2.24/0.71  fof(f90,plain,(
% 2.24/0.71    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.24/0.71    inference(cnf_transformation,[],[f41])).
% 2.24/0.71  fof(f41,plain,(
% 2.24/0.71    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.24/0.71    inference(flattening,[],[f40])).
% 2.24/0.71  fof(f40,plain,(
% 2.24/0.71    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.24/0.71    inference(ennf_transformation,[],[f13])).
% 2.24/0.71  fof(f13,axiom,(
% 2.24/0.71    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 2.24/0.71  fof(f1025,plain,(
% 2.24/0.71    sK2 = k4_relat_1(sK3) | sK1 != k2_relat_1(k4_relat_1(sK3)) | ~v1_funct_1(k4_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_13 | ~spl4_14 | ~spl4_15)),
% 2.24/0.71    inference(trivial_inequality_removal,[],[f1024])).
% 2.24/0.71  fof(f1024,plain,(
% 2.24/0.71    k6_partfun1(sK0) != k6_partfun1(sK0) | sK2 = k4_relat_1(sK3) | sK1 != k2_relat_1(k4_relat_1(sK3)) | ~v1_funct_1(k4_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_13 | ~spl4_14 | ~spl4_15)),
% 2.24/0.71    inference(superposition,[],[f1007,f717])).
% 2.24/0.71  fof(f717,plain,(
% 2.24/0.71    k6_partfun1(sK0) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) | (~spl4_1 | ~spl4_3 | ~spl4_15)),
% 2.24/0.71    inference(forward_demodulation,[],[f710,f126])).
% 2.24/0.71  fof(f126,plain,(
% 2.24/0.71    ( ! [X0] : (k6_partfun1(X0) = k4_relat_1(k6_partfun1(X0))) )),
% 2.24/0.71    inference(definition_unfolding,[],[f116,f106,f106])).
% 2.24/0.71  fof(f106,plain,(
% 2.24/0.71    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.24/0.71    inference(cnf_transformation,[],[f23])).
% 2.24/0.71  fof(f23,axiom,(
% 2.24/0.71    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.24/0.71  fof(f116,plain,(
% 2.24/0.71    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 2.24/0.71    inference(cnf_transformation,[],[f7])).
% 2.24/0.71  fof(f7,axiom,(
% 2.24/0.71    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 2.24/0.71  fof(f710,plain,(
% 2.24/0.71    k4_relat_1(k6_partfun1(sK0)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) | (~spl4_1 | ~spl4_3 | ~spl4_15)),
% 2.24/0.71    inference(backward_demodulation,[],[f565,f331])).
% 2.24/0.71  fof(f331,plain,(
% 2.24/0.71    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_3),
% 2.24/0.71    inference(avatar_component_clause,[],[f329])).
% 2.24/0.71  fof(f565,plain,(
% 2.24/0.71    k4_relat_1(k5_relat_1(sK2,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) | (~spl4_1 | ~spl4_15)),
% 2.24/0.71    inference(resolution,[],[f543,f207])).
% 2.24/0.71  fof(f207,plain,(
% 2.24/0.71    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(sK2,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(sK2))) ) | ~spl4_1),
% 2.24/0.71    inference(resolution,[],[f193,f112])).
% 2.24/0.71  fof(f112,plain,(
% 2.24/0.71    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 2.24/0.71    inference(cnf_transformation,[],[f57])).
% 2.24/0.71  fof(f57,plain,(
% 2.24/0.71    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.24/0.71    inference(ennf_transformation,[],[f5])).
% 2.24/0.71  fof(f5,axiom,(
% 2.24/0.71    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 2.24/0.71  fof(f193,plain,(
% 2.24/0.71    v1_relat_1(sK2) | ~spl4_1),
% 2.24/0.71    inference(avatar_component_clause,[],[f192])).
% 2.24/0.71  fof(f1007,plain,(
% 2.24/0.71    ( ! [X2] : (k6_partfun1(sK0) != k5_relat_1(X2,k4_relat_1(sK2)) | sK2 = X2 | sK1 != k2_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (~spl4_1 | ~spl4_2 | ~spl4_13 | ~spl4_14)),
% 2.24/0.71    inference(forward_demodulation,[],[f1006,f531])).
% 2.24/0.71  fof(f531,plain,(
% 2.24/0.71    sK2 = k2_funct_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_13 | ~spl4_14)),
% 2.24/0.71    inference(forward_demodulation,[],[f530,f205])).
% 2.24/0.71  fof(f205,plain,(
% 2.24/0.71    sK2 = k4_relat_1(k4_relat_1(sK2)) | ~spl4_1),
% 2.24/0.71    inference(resolution,[],[f193,f117])).
% 2.24/0.71  fof(f530,plain,(
% 2.24/0.71    k4_relat_1(k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_13 | ~spl4_14)),
% 2.24/0.71    inference(subsumption_resolution,[],[f529,f480])).
% 2.24/0.71  fof(f480,plain,(
% 2.24/0.71    v1_relat_1(k4_relat_1(sK2)) | ~spl4_13),
% 2.24/0.71    inference(avatar_component_clause,[],[f479])).
% 2.24/0.71  fof(f529,plain,(
% 2.24/0.71    k4_relat_1(k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_14)),
% 2.24/0.71    inference(subsumption_resolution,[],[f510,f217])).
% 2.24/0.71  fof(f217,plain,(
% 2.24/0.71    v1_funct_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f216,f193])).
% 2.24/0.71  fof(f216,plain,(
% 2.24/0.71    v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_2),
% 2.24/0.71    inference(subsumption_resolution,[],[f213,f67])).
% 2.24/0.71  fof(f67,plain,(
% 2.24/0.71    v1_funct_1(sK2)),
% 2.24/0.71    inference(cnf_transformation,[],[f64])).
% 2.24/0.71  fof(f213,plain,(
% 2.24/0.71    v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_2),
% 2.24/0.71    inference(superposition,[],[f93,f198])).
% 2.24/0.71  fof(f510,plain,(
% 2.24/0.71    k4_relat_1(k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~spl4_14),
% 2.24/0.71    inference(resolution,[],[f485,f91])).
% 2.24/0.71  fof(f485,plain,(
% 2.24/0.71    v2_funct_1(k4_relat_1(sK2)) | ~spl4_14),
% 2.24/0.71    inference(avatar_component_clause,[],[f483])).
% 2.24/0.71  fof(f1006,plain,(
% 2.24/0.71    ( ! [X2] : (k6_partfun1(sK0) != k5_relat_1(X2,k4_relat_1(sK2)) | sK1 != k2_relat_1(X2) | k2_funct_1(k4_relat_1(sK2)) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (~spl4_1 | ~spl4_2 | ~spl4_13 | ~spl4_14)),
% 2.24/0.71    inference(subsumption_resolution,[],[f1005,f480])).
% 2.24/0.71  fof(f1005,plain,(
% 2.24/0.71    ( ! [X2] : (k6_partfun1(sK0) != k5_relat_1(X2,k4_relat_1(sK2)) | sK1 != k2_relat_1(X2) | k2_funct_1(k4_relat_1(sK2)) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(k4_relat_1(sK2))) ) | (~spl4_1 | ~spl4_2 | ~spl4_14)),
% 2.24/0.71    inference(subsumption_resolution,[],[f271,f485])).
% 2.24/0.71  fof(f271,plain,(
% 2.24/0.71    ( ! [X2] : (k6_partfun1(sK0) != k5_relat_1(X2,k4_relat_1(sK2)) | sK1 != k2_relat_1(X2) | k2_funct_1(k4_relat_1(sK2)) = X2 | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(k4_relat_1(sK2))) ) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(forward_demodulation,[],[f270,f238])).
% 2.24/0.71  fof(f238,plain,(
% 2.24/0.71    sK0 = k2_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(forward_demodulation,[],[f237,f201])).
% 2.24/0.71  fof(f201,plain,(
% 2.24/0.71    sK0 = k1_relat_1(sK2)),
% 2.24/0.71    inference(forward_demodulation,[],[f154,f150])).
% 2.24/0.71  fof(f150,plain,(
% 2.24/0.71    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 2.24/0.71    inference(global_subsumption,[],[f69,f149])).
% 2.24/0.71  fof(f149,plain,(
% 2.24/0.71    sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.24/0.71    inference(subsumption_resolution,[],[f148,f77])).
% 2.24/0.71  fof(f77,plain,(
% 2.24/0.71    k1_xboole_0 != sK1),
% 2.24/0.71    inference(cnf_transformation,[],[f64])).
% 2.24/0.71  fof(f148,plain,(
% 2.24/0.71    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.24/0.71    inference(resolution,[],[f68,f94])).
% 2.24/0.71  fof(f68,plain,(
% 2.24/0.71    v1_funct_2(sK2,sK0,sK1)),
% 2.24/0.71    inference(cnf_transformation,[],[f64])).
% 2.24/0.71  fof(f69,plain,(
% 2.24/0.71    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.24/0.71    inference(cnf_transformation,[],[f64])).
% 2.24/0.71  fof(f154,plain,(
% 2.24/0.71    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 2.24/0.71    inference(resolution,[],[f69,f119])).
% 2.24/0.71  fof(f237,plain,(
% 2.24/0.71    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(forward_demodulation,[],[f236,f198])).
% 2.24/0.71  fof(f236,plain,(
% 2.24/0.71    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 2.24/0.71    inference(subsumption_resolution,[],[f146,f193])).
% 2.24/0.71  fof(f146,plain,(
% 2.24/0.71    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f139,f67])).
% 2.24/0.71  fof(f139,plain,(
% 2.24/0.71    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.24/0.71    inference(resolution,[],[f75,f90])).
% 2.24/0.71  fof(f75,plain,(
% 2.24/0.71    v2_funct_1(sK2)),
% 2.24/0.71    inference(cnf_transformation,[],[f64])).
% 2.24/0.71  fof(f270,plain,(
% 2.24/0.71    ( ! [X2] : (sK1 != k2_relat_1(X2) | k5_relat_1(X2,k4_relat_1(sK2)) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | k2_funct_1(k4_relat_1(sK2)) = X2 | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(k4_relat_1(sK2))) ) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f267,f217])).
% 2.24/0.71  fof(f267,plain,(
% 2.24/0.71    ( ! [X2] : (sK1 != k2_relat_1(X2) | k5_relat_1(X2,k4_relat_1(sK2)) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | k2_funct_1(k4_relat_1(sK2)) = X2 | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2))) ) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(superposition,[],[f120,f257])).
% 2.24/0.71  fof(f257,plain,(
% 2.24/0.71    sK1 = k1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(backward_demodulation,[],[f229,f256])).
% 2.24/0.71  fof(f256,plain,(
% 2.24/0.71    sK1 = k2_relat_1(sK2) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(forward_demodulation,[],[f255,f125])).
% 2.24/0.71  fof(f125,plain,(
% 2.24/0.71    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.24/0.71    inference(definition_unfolding,[],[f114,f106])).
% 2.24/0.71  fof(f114,plain,(
% 2.24/0.71    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.24/0.71    inference(cnf_transformation,[],[f6])).
% 2.24/0.71  fof(f6,axiom,(
% 2.24/0.71    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.24/0.71  fof(f255,plain,(
% 2.24/0.71    k2_relat_1(sK2) = k1_relat_1(k6_partfun1(sK1)) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(forward_demodulation,[],[f254,f227])).
% 2.24/0.71  fof(f227,plain,(
% 2.24/0.71    k6_partfun1(sK1) = k5_relat_1(k4_relat_1(sK2),sK2) | ~spl4_2),
% 2.24/0.71    inference(forward_demodulation,[],[f183,f198])).
% 2.24/0.71  fof(f183,plain,(
% 2.24/0.71    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 2.24/0.71    inference(subsumption_resolution,[],[f182,f67])).
% 2.24/0.71  fof(f182,plain,(
% 2.24/0.71    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~v1_funct_1(sK2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f181,f68])).
% 2.24/0.71  fof(f181,plain,(
% 2.24/0.71    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f180,f69])).
% 2.24/0.71  fof(f180,plain,(
% 2.24/0.71    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f179,f75])).
% 2.24/0.71  fof(f179,plain,(
% 2.24/0.71    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f167,f77])).
% 2.24/0.71  fof(f167,plain,(
% 2.24/0.71    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.24/0.71    inference(trivial_inequality_removal,[],[f166])).
% 2.24/0.71  fof(f166,plain,(
% 2.24/0.71    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.24/0.71    inference(superposition,[],[f80,f73])).
% 2.24/0.71  fof(f73,plain,(
% 2.24/0.71    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.24/0.71    inference(cnf_transformation,[],[f64])).
% 2.24/0.71  fof(f80,plain,(
% 2.24/0.71    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.24/0.71    inference(cnf_transformation,[],[f31])).
% 2.24/0.71  fof(f31,plain,(
% 2.24/0.71    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.24/0.71    inference(flattening,[],[f30])).
% 2.24/0.71  fof(f30,plain,(
% 2.24/0.71    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.24/0.71    inference(ennf_transformation,[],[f25])).
% 2.24/0.71  fof(f25,axiom,(
% 2.24/0.71    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 2.24/0.71  fof(f254,plain,(
% 2.24/0.71    k2_relat_1(sK2) = k1_relat_1(k5_relat_1(k4_relat_1(sK2),sK2)) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(forward_demodulation,[],[f253,f198])).
% 2.24/0.71  fof(f253,plain,(
% 2.24/0.71    k2_relat_1(sK2) = k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~spl4_1),
% 2.24/0.71    inference(subsumption_resolution,[],[f143,f193])).
% 2.24/0.71  fof(f143,plain,(
% 2.24/0.71    k2_relat_1(sK2) = k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~v1_relat_1(sK2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f136,f67])).
% 2.24/0.71  fof(f136,plain,(
% 2.24/0.71    k2_relat_1(sK2) = k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.24/0.71    inference(resolution,[],[f75,f87])).
% 2.24/0.71  fof(f87,plain,(
% 2.24/0.71    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.24/0.71    inference(cnf_transformation,[],[f39])).
% 2.24/0.71  fof(f39,plain,(
% 2.24/0.71    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.24/0.71    inference(flattening,[],[f38])).
% 2.24/0.71  fof(f38,plain,(
% 2.24/0.71    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.24/0.71    inference(ennf_transformation,[],[f15])).
% 2.24/0.71  fof(f15,axiom,(
% 2.24/0.71    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).
% 2.24/0.71  fof(f229,plain,(
% 2.24/0.71    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(forward_demodulation,[],[f228,f198])).
% 2.24/0.71  fof(f228,plain,(
% 2.24/0.71    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 2.24/0.71    inference(subsumption_resolution,[],[f145,f193])).
% 2.24/0.71  fof(f145,plain,(
% 2.24/0.71    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f138,f67])).
% 2.24/0.71  fof(f138,plain,(
% 2.24/0.71    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.24/0.71    inference(resolution,[],[f75,f89])).
% 2.24/0.71  fof(f89,plain,(
% 2.24/0.71    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.24/0.71    inference(cnf_transformation,[],[f41])).
% 2.24/0.71  fof(f120,plain,(
% 2.24/0.71    ( ! [X0,X1] : (k1_relat_1(X0) != k2_relat_1(X1) | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.24/0.71    inference(definition_unfolding,[],[f84,f106])).
% 2.24/0.71  fof(f84,plain,(
% 2.24/0.71    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.24/0.71    inference(cnf_transformation,[],[f35])).
% 2.24/0.71  fof(f35,plain,(
% 2.24/0.71    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.24/0.71    inference(flattening,[],[f34])).
% 2.24/0.71  fof(f34,plain,(
% 2.24/0.71    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.24/0.71    inference(ennf_transformation,[],[f16])).
% 2.24/0.71  fof(f16,axiom,(
% 2.24/0.71    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 2.24/0.71  fof(f716,plain,(
% 2.24/0.71    ~spl4_3 | spl4_16),
% 2.24/0.71    inference(avatar_contradiction_clause,[],[f715])).
% 2.24/0.71  fof(f715,plain,(
% 2.24/0.71    $false | (~spl4_3 | spl4_16)),
% 2.24/0.71    inference(subsumption_resolution,[],[f709,f121])).
% 2.24/0.71  fof(f121,plain,(
% 2.24/0.71    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.24/0.71    inference(definition_unfolding,[],[f103,f106])).
% 2.24/0.71  fof(f103,plain,(
% 2.24/0.71    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.24/0.71    inference(cnf_transformation,[],[f11])).
% 2.24/0.71  fof(f11,axiom,(
% 2.24/0.71    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.24/0.71  fof(f709,plain,(
% 2.24/0.71    ~v2_funct_1(k6_partfun1(sK0)) | (~spl4_3 | spl4_16)),
% 2.24/0.71    inference(backward_demodulation,[],[f548,f331])).
% 2.24/0.71  fof(f548,plain,(
% 2.24/0.71    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_16),
% 2.24/0.71    inference(avatar_component_clause,[],[f546])).
% 2.24/0.71  fof(f546,plain,(
% 2.24/0.71    spl4_16 <=> v2_funct_1(k5_relat_1(sK2,sK3))),
% 2.24/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 2.24/0.71  fof(f695,plain,(
% 2.24/0.71    ~spl4_1 | ~spl4_2 | spl4_4 | ~spl4_9),
% 2.24/0.71    inference(avatar_contradiction_clause,[],[f694])).
% 2.24/0.71  fof(f694,plain,(
% 2.24/0.71    $false | (~spl4_1 | ~spl4_2 | spl4_4 | ~spl4_9)),
% 2.24/0.71    inference(subsumption_resolution,[],[f693,f67])).
% 2.24/0.71  fof(f693,plain,(
% 2.24/0.71    ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | spl4_4 | ~spl4_9)),
% 2.24/0.71    inference(subsumption_resolution,[],[f692,f69])).
% 2.24/0.71  fof(f692,plain,(
% 2.24/0.71    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | spl4_4 | ~spl4_9)),
% 2.24/0.71    inference(subsumption_resolution,[],[f691,f217])).
% 2.24/0.71  fof(f691,plain,(
% 2.24/0.71    ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | spl4_4 | ~spl4_9)),
% 2.24/0.71    inference(subsumption_resolution,[],[f690,f452])).
% 2.24/0.71  fof(f452,plain,(
% 2.24/0.71    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_9),
% 2.24/0.71    inference(avatar_component_clause,[],[f451])).
% 2.24/0.71  fof(f451,plain,(
% 2.24/0.71    spl4_9 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.24/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.24/0.71  fof(f690,plain,(
% 2.24/0.71    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | spl4_4 | ~spl4_9)),
% 2.24/0.71    inference(subsumption_resolution,[],[f685,f335])).
% 2.24/0.71  fof(f335,plain,(
% 2.24/0.71    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_4),
% 2.24/0.71    inference(avatar_component_clause,[],[f333])).
% 2.24/0.71  fof(f333,plain,(
% 2.24/0.71    spl4_4 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.24/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.24/0.71  fof(f685,plain,(
% 2.24/0.71    m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_9)),
% 2.24/0.71    inference(superposition,[],[f108,f676])).
% 2.24/0.71  fof(f676,plain,(
% 2.24/0.71    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_9)),
% 2.24/0.71    inference(forward_demodulation,[],[f675,f226])).
% 2.24/0.71  fof(f226,plain,(
% 2.24/0.71    k6_partfun1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2)) | ~spl4_2),
% 2.24/0.71    inference(forward_demodulation,[],[f178,f198])).
% 2.24/0.71  fof(f178,plain,(
% 2.24/0.71    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.24/0.71    inference(subsumption_resolution,[],[f177,f67])).
% 2.24/0.71  fof(f177,plain,(
% 2.24/0.71    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f176,f68])).
% 2.24/0.71  fof(f176,plain,(
% 2.24/0.71    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f175,f69])).
% 2.24/0.71  fof(f175,plain,(
% 2.24/0.71    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f174,f75])).
% 2.24/0.71  fof(f174,plain,(
% 2.24/0.71    ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f168,f77])).
% 2.24/0.71  fof(f168,plain,(
% 2.24/0.71    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.24/0.71    inference(trivial_inequality_removal,[],[f165])).
% 2.24/0.71  fof(f165,plain,(
% 2.24/0.71    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.24/0.71    inference(superposition,[],[f79,f73])).
% 2.24/0.71  fof(f79,plain,(
% 2.24/0.71    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.24/0.71    inference(cnf_transformation,[],[f31])).
% 2.24/0.71  fof(f675,plain,(
% 2.24/0.71    k5_relat_1(sK2,k4_relat_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_9)),
% 2.24/0.71    inference(subsumption_resolution,[],[f668,f217])).
% 2.24/0.71  fof(f668,plain,(
% 2.24/0.71    ~v1_funct_1(k4_relat_1(sK2)) | k5_relat_1(sK2,k4_relat_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) | ~spl4_9),
% 2.24/0.71    inference(resolution,[],[f452,f157])).
% 2.24/0.71  fof(f157,plain,(
% 2.24/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)) )),
% 2.24/0.71    inference(subsumption_resolution,[],[f155,f67])).
% 2.24/0.71  fof(f155,plain,(
% 2.24/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) | ~v1_funct_1(sK2)) )),
% 2.24/0.71    inference(resolution,[],[f69,f109])).
% 2.24/0.71  fof(f109,plain,(
% 2.24/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 2.24/0.71    inference(cnf_transformation,[],[f55])).
% 2.24/0.71  fof(f55,plain,(
% 2.24/0.71    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.24/0.71    inference(flattening,[],[f54])).
% 2.24/0.71  fof(f54,plain,(
% 2.24/0.71    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.24/0.71    inference(ennf_transformation,[],[f22])).
% 2.24/0.71  fof(f22,axiom,(
% 2.24/0.71    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.24/0.71  fof(f108,plain,(
% 2.24/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.24/0.71    inference(cnf_transformation,[],[f53])).
% 2.24/0.71  fof(f53,plain,(
% 2.24/0.71    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.24/0.71    inference(flattening,[],[f52])).
% 2.24/0.71  fof(f52,plain,(
% 2.24/0.71    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.24/0.71    inference(ennf_transformation,[],[f20])).
% 2.24/0.71  fof(f20,axiom,(
% 2.24/0.71    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.24/0.71  fof(f663,plain,(
% 2.24/0.71    ~spl4_2 | spl4_9),
% 2.24/0.71    inference(avatar_contradiction_clause,[],[f662])).
% 2.24/0.71  fof(f662,plain,(
% 2.24/0.71    $false | (~spl4_2 | spl4_9)),
% 2.24/0.71    inference(subsumption_resolution,[],[f661,f453])).
% 2.24/0.71  fof(f453,plain,(
% 2.24/0.71    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_9),
% 2.24/0.71    inference(avatar_component_clause,[],[f451])).
% 2.24/0.71  fof(f661,plain,(
% 2.24/0.71    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_2),
% 2.24/0.71    inference(subsumption_resolution,[],[f660,f69])).
% 2.24/0.71  fof(f660,plain,(
% 2.24/0.71    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_2),
% 2.24/0.71    inference(subsumption_resolution,[],[f659,f73])).
% 2.24/0.71  fof(f659,plain,(
% 2.24/0.71    sK1 != k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_2),
% 2.24/0.71    inference(resolution,[],[f221,f68])).
% 2.24/0.71  fof(f221,plain,(
% 2.24/0.71    ( ! [X2,X3] : (~v1_funct_2(sK2,X3,X2) | k2_relset_1(X3,X2,sK2) != X2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl4_2),
% 2.24/0.71    inference(subsumption_resolution,[],[f220,f67])).
% 2.24/0.71  fof(f220,plain,(
% 2.24/0.71    ( ! [X2,X3] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relset_1(X3,X2,sK2) != X2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK2,X3,X2) | ~v1_funct_1(sK2)) ) | ~spl4_2),
% 2.24/0.71    inference(subsumption_resolution,[],[f215,f75])).
% 2.24/0.71  fof(f215,plain,(
% 2.24/0.71    ( ! [X2,X3] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relset_1(X3,X2,sK2) != X2 | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK2,X3,X2) | ~v1_funct_1(sK2)) ) | ~spl4_2),
% 2.24/0.71    inference(superposition,[],[f83,f198])).
% 2.24/0.71  fof(f83,plain,(
% 2.24/0.71    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.24/0.71    inference(cnf_transformation,[],[f33])).
% 2.24/0.71  fof(f33,plain,(
% 2.24/0.71    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.24/0.71    inference(flattening,[],[f32])).
% 2.24/0.71  fof(f32,plain,(
% 2.24/0.71    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.24/0.71    inference(ennf_transformation,[],[f24])).
% 2.24/0.71  fof(f24,axiom,(
% 2.24/0.71    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 2.24/0.71  fof(f562,plain,(
% 2.24/0.71    spl4_15),
% 2.24/0.71    inference(avatar_contradiction_clause,[],[f561])).
% 2.24/0.71  fof(f561,plain,(
% 2.24/0.71    $false | spl4_15),
% 2.24/0.71    inference(subsumption_resolution,[],[f560,f111])).
% 2.24/0.71  fof(f111,plain,(
% 2.24/0.71    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.24/0.71    inference(cnf_transformation,[],[f3])).
% 2.24/0.71  fof(f3,axiom,(
% 2.24/0.71    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.24/0.71  fof(f560,plain,(
% 2.24/0.71    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_15),
% 2.24/0.71    inference(resolution,[],[f554,f72])).
% 2.24/0.71  fof(f554,plain,(
% 2.24/0.71    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_15),
% 2.24/0.71    inference(resolution,[],[f544,f110])).
% 2.24/0.71  fof(f110,plain,(
% 2.24/0.71    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.24/0.71    inference(cnf_transformation,[],[f56])).
% 2.24/0.71  fof(f56,plain,(
% 2.24/0.71    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.24/0.71    inference(ennf_transformation,[],[f1])).
% 2.24/0.71  fof(f1,axiom,(
% 2.24/0.71    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.24/0.71  fof(f544,plain,(
% 2.24/0.71    ~v1_relat_1(sK3) | spl4_15),
% 2.24/0.71    inference(avatar_component_clause,[],[f542])).
% 2.24/0.71  fof(f553,plain,(
% 2.24/0.71    ~spl4_15 | ~spl4_16 | spl4_17 | ~spl4_1 | ~spl4_2),
% 2.24/0.71    inference(avatar_split_clause,[],[f477,f196,f192,f550,f546,f542])).
% 2.24/0.71  fof(f477,plain,(
% 2.24/0.71    v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f472,f70])).
% 2.24/0.71  fof(f472,plain,(
% 2.24/0.71    v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(trivial_inequality_removal,[],[f471])).
% 2.24/0.71  fof(f471,plain,(
% 2.24/0.71    sK1 != sK1 | v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(superposition,[],[f262,f224])).
% 2.24/0.71  fof(f262,plain,(
% 2.24/0.71    ( ! [X1] : (sK1 != k1_relat_1(X1) | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(sK2,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f261,f193])).
% 2.24/0.71  fof(f261,plain,(
% 2.24/0.71    ( ! [X1] : (sK1 != k1_relat_1(X1) | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(sK2,X1)) | ~v1_relat_1(sK2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f259,f67])).
% 2.24/0.71  fof(f259,plain,(
% 2.24/0.71    ( ! [X1] : (sK1 != k1_relat_1(X1) | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(sK2,X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(superposition,[],[f101,f256])).
% 2.24/0.71  fof(f101,plain,(
% 2.24/0.71    ( ! [X0,X1] : (k1_relat_1(X0) != k2_relat_1(X1) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.24/0.71    inference(cnf_transformation,[],[f49])).
% 2.24/0.71  fof(f49,plain,(
% 2.24/0.71    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.24/0.71    inference(flattening,[],[f48])).
% 2.24/0.71  fof(f48,plain,(
% 2.24/0.71    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.24/0.71    inference(ennf_transformation,[],[f12])).
% 2.24/0.71  fof(f12,axiom,(
% 2.24/0.71    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 2.24/0.71  fof(f490,plain,(
% 2.24/0.71    ~spl4_1 | spl4_13),
% 2.24/0.71    inference(avatar_contradiction_clause,[],[f489])).
% 2.24/0.71  fof(f489,plain,(
% 2.24/0.71    $false | (~spl4_1 | spl4_13)),
% 2.24/0.71    inference(subsumption_resolution,[],[f487,f193])).
% 2.24/0.71  fof(f487,plain,(
% 2.24/0.71    ~v1_relat_1(sK2) | spl4_13),
% 2.24/0.71    inference(resolution,[],[f481,f118])).
% 2.24/0.71  fof(f481,plain,(
% 2.24/0.71    ~v1_relat_1(k4_relat_1(sK2)) | spl4_13),
% 2.24/0.71    inference(avatar_component_clause,[],[f479])).
% 2.24/0.71  fof(f486,plain,(
% 2.24/0.71    ~spl4_13 | spl4_14 | ~spl4_1 | ~spl4_2),
% 2.24/0.71    inference(avatar_split_clause,[],[f476,f196,f192,f483,f479])).
% 2.24/0.71  fof(f476,plain,(
% 2.24/0.71    v2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f475,f121])).
% 2.24/0.71  fof(f475,plain,(
% 2.24/0.71    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(forward_demodulation,[],[f474,f226])).
% 2.24/0.71  fof(f474,plain,(
% 2.24/0.71    v2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k5_relat_1(sK2,k4_relat_1(sK2))) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f473,f217])).
% 2.24/0.71  fof(f473,plain,(
% 2.24/0.71    v2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k5_relat_1(sK2,k4_relat_1(sK2))) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(trivial_inequality_removal,[],[f468])).
% 2.24/0.71  fof(f468,plain,(
% 2.24/0.71    sK1 != sK1 | v2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k5_relat_1(sK2,k4_relat_1(sK2))) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.24/0.71    inference(superposition,[],[f262,f257])).
% 2.24/0.71  fof(f336,plain,(
% 2.24/0.71    spl4_3 | ~spl4_4),
% 2.24/0.71    inference(avatar_split_clause,[],[f327,f333,f329])).
% 2.24/0.71  fof(f327,plain,(
% 2.24/0.71    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.24/0.71    inference(global_subsumption,[],[f325,f326])).
% 2.24/0.71  fof(f326,plain,(
% 2.24/0.71    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.24/0.71    inference(resolution,[],[f315,f104])).
% 2.24/0.71  fof(f104,plain,(
% 2.24/0.71    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.24/0.71    inference(cnf_transformation,[],[f66])).
% 2.24/0.71  fof(f66,plain,(
% 2.24/0.71    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/0.71    inference(nnf_transformation,[],[f51])).
% 2.24/0.71  fof(f51,plain,(
% 2.24/0.71    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/0.71    inference(flattening,[],[f50])).
% 2.24/0.71  fof(f50,plain,(
% 2.24/0.71    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.24/0.71    inference(ennf_transformation,[],[f18])).
% 2.24/0.71  fof(f18,axiom,(
% 2.24/0.71    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.24/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.24/0.71  fof(f315,plain,(
% 2.24/0.71    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.24/0.71    inference(backward_demodulation,[],[f74,f290])).
% 2.24/0.71  fof(f290,plain,(
% 2.24/0.71    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.24/0.71    inference(subsumption_resolution,[],[f286,f70])).
% 2.24/0.71  fof(f286,plain,(
% 2.24/0.71    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.24/0.71    inference(resolution,[],[f157,f72])).
% 2.24/0.71  fof(f74,plain,(
% 2.24/0.71    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.24/0.71    inference(cnf_transformation,[],[f64])).
% 2.24/0.71  fof(f325,plain,(
% 2.24/0.71    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.24/0.71    inference(subsumption_resolution,[],[f324,f67])).
% 2.24/0.71  fof(f324,plain,(
% 2.24/0.71    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f323,f69])).
% 2.24/0.71  fof(f323,plain,(
% 2.24/0.71    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f322,f70])).
% 2.24/0.71  fof(f322,plain,(
% 2.24/0.71    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f317,f72])).
% 2.24/0.71  fof(f317,plain,(
% 2.24/0.71    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.24/0.71    inference(superposition,[],[f108,f290])).
% 2.24/0.71  fof(f204,plain,(
% 2.24/0.71    spl4_1),
% 2.24/0.71    inference(avatar_contradiction_clause,[],[f203])).
% 2.24/0.71  fof(f203,plain,(
% 2.24/0.71    $false | spl4_1),
% 2.24/0.71    inference(subsumption_resolution,[],[f202,f111])).
% 2.24/0.71  fof(f202,plain,(
% 2.24/0.71    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_1),
% 2.24/0.71    inference(resolution,[],[f200,f69])).
% 2.24/0.71  fof(f200,plain,(
% 2.24/0.71    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_1),
% 2.24/0.71    inference(resolution,[],[f194,f110])).
% 2.24/0.71  fof(f194,plain,(
% 2.24/0.71    ~v1_relat_1(sK2) | spl4_1),
% 2.24/0.71    inference(avatar_component_clause,[],[f192])).
% 2.24/0.71  fof(f199,plain,(
% 2.24/0.71    ~spl4_1 | spl4_2),
% 2.24/0.71    inference(avatar_split_clause,[],[f147,f196,f192])).
% 2.24/0.71  fof(f147,plain,(
% 2.24/0.71    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_relat_1(sK2)),
% 2.24/0.71    inference(subsumption_resolution,[],[f140,f67])).
% 2.24/0.71  fof(f140,plain,(
% 2.24/0.71    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.24/0.71    inference(resolution,[],[f75,f91])).
% 2.24/0.71  % SZS output end Proof for theBenchmark
% 2.24/0.71  % (15582)------------------------------
% 2.24/0.71  % (15582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.24/0.71  % (15582)Termination reason: Refutation
% 2.24/0.71  
% 2.24/0.71  % (15582)Memory used [KB]: 11257
% 2.24/0.71  % (15582)Time elapsed: 0.244 s
% 2.24/0.71  % (15582)------------------------------
% 2.24/0.71  % (15582)------------------------------
% 2.68/0.72  % (15556)Success in time 0.361 s
%------------------------------------------------------------------------------
