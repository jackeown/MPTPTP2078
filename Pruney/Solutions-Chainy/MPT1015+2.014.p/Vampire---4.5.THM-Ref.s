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
% DateTime   : Thu Dec  3 13:05:27 EST 2020

% Result     : Theorem 6.41s
% Output     : Refutation 6.48s
% Verified   : 
% Statistics : Number of formulae       :  301 (1653 expanded)
%              Number of leaves         :   46 ( 525 expanded)
%              Depth                    :   30
%              Number of atoms          : 1148 (12036 expanded)
%              Number of equality atoms :  215 ( 449 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2530,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f171,f181,f191,f209,f215,f245,f274,f343,f1342,f1437,f2065,f2126,f2160,f2192,f2195,f2226,f2451,f2520])).

fof(f2520,plain,
    ( spl3_24
    | ~ spl3_31 ),
    inference(avatar_contradiction_clause,[],[f2519])).

fof(f2519,plain,
    ( $false
    | spl3_24
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f2489,f93])).

fof(f93,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & v2_funct_1(sK1)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f80,f79])).

fof(f79,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & v2_funct_1(X1)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
          & v2_funct_1(sK1)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
        & v2_funct_1(sK1)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
      & v2_funct_1(sK1)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f35])).

fof(f35,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

fof(f2489,plain,
    ( ~ v2_funct_1(sK1)
    | spl3_24
    | ~ spl3_31 ),
    inference(backward_demodulation,[],[f410,f552])).

fof(f552,plain,
    ( sK1 = sK2
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f550])).

fof(f550,plain,
    ( spl3_31
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f410,plain,
    ( ~ v2_funct_1(sK2)
    | spl3_24 ),
    inference(avatar_component_clause,[],[f408])).

fof(f408,plain,
    ( spl3_24
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f2451,plain,
    ( ~ spl3_11
    | ~ spl3_12
    | spl3_31 ),
    inference(avatar_contradiction_clause,[],[f2450])).

fof(f2450,plain,
    ( $false
    | ~ spl3_11
    | ~ spl3_12
    | spl3_31 ),
    inference(subsumption_resolution,[],[f2449,f551])).

fof(f551,plain,
    ( sK1 != sK2
    | spl3_31 ),
    inference(avatar_component_clause,[],[f550])).

fof(f2449,plain,
    ( sK1 = sK2
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(resolution,[],[f2241,f266])).

fof(f266,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl3_12
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f2241,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK1 = X0 )
    | ~ spl3_11 ),
    inference(resolution,[],[f237,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f237,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl3_11
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f2226,plain,
    ( spl3_24
    | spl3_58 ),
    inference(avatar_split_clause,[],[f2225,f856,f408])).

fof(f856,plain,
    ( spl3_58
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f2225,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f2224,f89])).

fof(f89,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

fof(f2224,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f2223,f90])).

fof(f90,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f81])).

fof(f2223,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f2222,f91])).

fof(f91,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f81])).

fof(f2222,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f2221,f86])).

fof(f86,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f81])).

fof(f2221,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f2220,f87])).

fof(f87,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f81])).

fof(f2220,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f2219,f88])).

fof(f88,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f81])).

fof(f2219,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f2016,f93])).

fof(f2016,plain,
    ( ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f140,f1269])).

fof(f1269,plain,(
    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(backward_demodulation,[],[f679,f1143])).

fof(f1143,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f1115,f845])).

fof(f845,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK1) ),
    inference(backward_demodulation,[],[f92,f679])).

fof(f92,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f81])).

fof(f1115,plain,
    ( sK1 = k5_relat_1(sK2,sK1)
    | ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK1) ),
    inference(resolution,[],[f867,f224])).

fof(f224,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | sK1 = X1
      | ~ r2_relset_1(sK0,sK0,X1,sK1) ) ),
    inference(resolution,[],[f88,f142])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f867,plain,(
    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f866,f89])).

fof(f866,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f865,f91])).

fof(f865,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f864,f86])).

fof(f864,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f847,f88])).

fof(f847,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f146,f679])).

fof(f146,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f679,plain,(
    k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f670,f89])).

fof(f670,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f239,f91])).

fof(f239,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X2,X3,sK0,sK0,X4,sK1) = k5_relat_1(X4,sK1)
      | ~ v1_funct_1(X4) ) ),
    inference(subsumption_resolution,[],[f225,f86])).

fof(f225,plain,(
    ! [X4,X2,X3] :
      ( k1_partfun1(X2,X3,sK0,sK0,X4,sK1) = k5_relat_1(X4,sK1)
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(resolution,[],[f88,f144])).

fof(f144,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f140,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f2195,plain,
    ( ~ spl3_10
    | spl3_11 ),
    inference(avatar_split_clause,[],[f2194,f235,f231])).

fof(f231,plain,
    ( spl3_10
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f2194,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f1116,f1143])).

fof(f1116,plain,
    ( v1_xboole_0(k5_relat_1(sK2,sK1))
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f867,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f2192,plain,
    ( ~ spl3_10
    | spl3_12 ),
    inference(avatar_split_clause,[],[f1513,f264,f231])).

fof(f1513,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f91,f120])).

fof(f2160,plain,(
    ~ spl3_33 ),
    inference(avatar_contradiction_clause,[],[f2159])).

fof(f2159,plain,
    ( $false
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f2138,f260])).

fof(f260,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f91,f161])).

fof(f161,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f143])).

fof(f143,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f2138,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_33 ),
    inference(backward_demodulation,[],[f94,f571])).

fof(f571,plain,
    ( k6_partfun1(sK0) = sK2
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f569])).

fof(f569,plain,
    ( spl3_33
  <=> k6_partfun1(sK0) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f94,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f81])).

fof(f2126,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_24
    | spl3_33
    | ~ spl3_81 ),
    inference(avatar_contradiction_clause,[],[f2125])).

fof(f2125,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_24
    | spl3_33
    | ~ spl3_81 ),
    inference(subsumption_resolution,[],[f2066,f310])).

fof(f310,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl3_16
  <=> sK0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f2066,plain,
    ( sK0 != k2_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_17
    | ~ spl3_24
    | spl3_33
    | ~ spl3_81 ),
    inference(subsumption_resolution,[],[f1992,f2014])).

fof(f2014,plain,
    ( k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_24
    | spl3_33
    | ~ spl3_81 ),
    inference(subsumption_resolution,[],[f2013,f401])).

fof(f401,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f250,f271])).

fof(f271,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK2) ),
    inference(subsumption_resolution,[],[f270,f89])).

fof(f270,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f261,f90])).

fof(f261,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f91,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f250,plain,(
    k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f91,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f2013,plain,
    ( sK0 != k1_relat_1(sK2)
    | k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_24
    | spl3_33
    | ~ spl3_81 ),
    inference(forward_demodulation,[],[f2012,f1581])).

fof(f1581,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f1457,f401])).

fof(f1457,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1456,f175])).

fof(f175,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1456,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1444,f89])).

fof(f1444,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_24 ),
    inference(resolution,[],[f409,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f409,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f408])).

fof(f2012,plain,
    ( k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_24
    | spl3_33
    | ~ spl3_81 ),
    inference(subsumption_resolution,[],[f2011,f570])).

fof(f570,plain,
    ( k6_partfun1(sK0) != sK2
    | spl3_33 ),
    inference(avatar_component_clause,[],[f569])).

fof(f2011,plain,
    ( k6_partfun1(sK0) = sK2
    | k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_24
    | ~ spl3_81 ),
    inference(forward_demodulation,[],[f2010,f401])).

fof(f2010,plain,
    ( k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2))
    | sK2 = k6_partfun1(k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_24
    | ~ spl3_81 ),
    inference(subsumption_resolution,[],[f2009,f180])).

fof(f180,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_4
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f2009,plain,
    ( k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2))
    | sK2 = k6_partfun1(k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_24
    | ~ spl3_81 ),
    inference(subsumption_resolution,[],[f2008,f1321])).

fof(f1321,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_81 ),
    inference(avatar_component_clause,[],[f1319])).

fof(f1319,plain,
    ( spl3_81
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).

fof(f2008,plain,
    ( k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2))
    | sK2 = k6_partfun1(k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f2007,f175])).

fof(f2007,plain,
    ( k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2))
    | sK2 = k6_partfun1(k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f2006,f89])).

fof(f2006,plain,
    ( k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2))
    | sK2 = k6_partfun1(k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_24 ),
    inference(superposition,[],[f156,f1453])).

fof(f1453,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1452,f175])).

fof(f1452,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1442,f89])).

fof(f1442,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_24 ),
    inference(resolution,[],[f409,f154])).

fof(f154,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f115,f96])).

fof(f96,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f115,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f156,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != X0
      | k6_partfun1(k1_relat_1(X1)) = X1
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f118,f96])).

fof(f118,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

fof(f1992,plain,
    ( sK0 != k2_relat_1(sK2)
    | k2_funct_1(sK2) = k6_partfun1(k2_relat_1(sK2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_17
    | ~ spl3_24
    | ~ spl3_81 ),
    inference(forward_demodulation,[],[f1991,f359])).

fof(f359,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f214,f358])).

fof(f358,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(forward_demodulation,[],[f217,f242])).

fof(f242,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f241,f86])).

fof(f241,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f228,f87])).

fof(f228,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f88,f125])).

fof(f217,plain,(
    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f88,f130])).

fof(f214,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl3_9
  <=> k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f1991,plain,
    ( k2_relat_1(k2_funct_1(sK1)) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = k6_partfun1(k2_relat_1(sK2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17
    | ~ spl3_24
    | ~ spl3_81 ),
    inference(forward_demodulation,[],[f1990,f1455])).

fof(f1455,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1454,f175])).

fof(f1454,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1443,f89])).

fof(f1443,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_24 ),
    inference(resolution,[],[f409,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1990,plain,
    ( k2_funct_1(sK2) = k6_partfun1(k2_relat_1(sK2))
    | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17
    | ~ spl3_24
    | ~ spl3_81 ),
    inference(forward_demodulation,[],[f1989,f1455])).

fof(f1989,plain,
    ( k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2)))
    | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17
    | ~ spl3_24
    | ~ spl3_81 ),
    inference(subsumption_resolution,[],[f1988,f170])).

fof(f170,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl3_2
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1988,plain,
    ( k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2)))
    | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17
    | ~ spl3_24
    | ~ spl3_81 ),
    inference(subsumption_resolution,[],[f1987,f318])).

fof(f318,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl3_17
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f1987,plain,
    ( k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2)))
    | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_24
    | ~ spl3_81 ),
    inference(subsumption_resolution,[],[f1986,f180])).

fof(f1986,plain,
    ( k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2)))
    | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_24
    | ~ spl3_81 ),
    inference(subsumption_resolution,[],[f1985,f1321])).

fof(f1985,plain,
    ( k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2)))
    | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_24 ),
    inference(trivial_inequality_removal,[],[f1984])).

fof(f1984,plain,
    ( k2_funct_1(sK1) != k2_funct_1(sK1)
    | k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2)))
    | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_24 ),
    inference(superposition,[],[f156,f1447])).

fof(f1447,plain,
    ( k2_funct_1(sK1) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f1446,f1143])).

fof(f1446,plain,
    ( k2_funct_1(k5_relat_1(sK2,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1445,f89])).

fof(f1445,plain,
    ( ~ v1_funct_1(sK2)
    | k2_funct_1(k5_relat_1(sK2,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1439,f175])).

fof(f1439,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_funct_1(k5_relat_1(sK2,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2))
    | ~ spl3_5
    | ~ spl3_24 ),
    inference(resolution,[],[f409,f190])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl3_5
  <=> ! [X0] :
        ( k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f2065,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_9
    | spl3_16
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f2064])).

fof(f2064,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_9
    | spl3_16
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f2063,f309])).

fof(f309,plain,
    ( sK0 != k2_relat_1(sK2)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f308])).

fof(f2063,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f2062,f713])).

fof(f713,plain,
    ( sK0 = k9_relat_1(k2_funct_1(sK1),k2_relat_1(sK1))
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f709,f359])).

fof(f709,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),k2_relat_1(sK1))
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(superposition,[],[f278,f533])).

fof(f533,plain,
    ( k2_funct_1(sK1) = k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1))
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f532,f170])).

fof(f532,plain,
    ( k2_funct_1(sK1) = k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(resolution,[],[f514,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f514,plain,
    ( v4_relat_1(k2_funct_1(sK1),k2_relat_1(sK1))
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(resolution,[],[f379,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f379,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK1),sK0)))
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f378,f208])).

fof(f208,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl3_8
  <=> k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f378,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),sK0)))
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f377,f170])).

fof(f377,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),sK0)))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f372,f318])).

fof(f372,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_9 ),
    inference(superposition,[],[f109,f359])).

fof(f109,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f278,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(k2_funct_1(sK1),X0)) = k9_relat_1(k2_funct_1(sK1),X0)
    | ~ spl3_2 ),
    inference(resolution,[],[f170,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f2062,plain,
    ( k2_relat_1(sK2) = k9_relat_1(k2_funct_1(sK1),k2_relat_1(sK1))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f2055,f1270])).

fof(f1270,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f763,f1143])).

fof(f763,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f248,f175])).

fof(f248,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k5_relat_1(X1,sK1)) = k9_relat_1(sK1,k2_relat_1(X1)) )
    | ~ spl3_1 ),
    inference(resolution,[],[f165,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f165,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl3_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f2055,plain,
    ( k2_relat_1(sK2) = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k2_relat_1(sK2)))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f365,f289])).

fof(f289,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f288,f175])).

fof(f288,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f253,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f253,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f91,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f365,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0 )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f364,f165])).

fof(f364,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f363,f86])).

fof(f363,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f360,f93])).

fof(f360,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f116,f358])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(X0))
      | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

fof(f1437,plain,
    ( spl3_10
    | ~ spl3_58 ),
    inference(avatar_contradiction_clause,[],[f1436])).

fof(f1436,plain,
    ( $false
    | spl3_10
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f1355,f95])).

fof(f95,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1355,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_10
    | ~ spl3_58 ),
    inference(backward_demodulation,[],[f233,f858])).

fof(f858,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f856])).

fof(f233,plain,
    ( ~ v1_xboole_0(sK0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f231])).

fof(f1342,plain,
    ( ~ spl3_24
    | spl3_81
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f1341,f308,f1319,f408])).

fof(f1341,plain,
    ( sK0 != k2_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1340,f89])).

fof(f1340,plain,
    ( sK0 != k2_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1339,f90])).

fof(f1339,plain,
    ( sK0 != k2_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f419,f91])).

fof(f419,plain,
    ( sK0 != k2_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f136,f251])).

fof(f251,plain,(
    k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f91,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
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

fof(f343,plain,
    ( ~ spl3_1
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | ~ spl3_1
    | spl3_17 ),
    inference(subsumption_resolution,[],[f341,f165])).

fof(f341,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_17 ),
    inference(subsumption_resolution,[],[f340,f86])).

fof(f340,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl3_17 ),
    inference(resolution,[],[f319,f111])).

fof(f111,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f319,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f317])).

fof(f274,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f272,f119])).

fof(f119,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f272,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f262,f176])).

fof(f176,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f174])).

fof(f262,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f91,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f245,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f243,f119])).

fof(f243,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f229,f166])).

fof(f166,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f164])).

fof(f229,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f88,f106])).

fof(f215,plain,
    ( ~ spl3_1
    | spl3_9 ),
    inference(avatar_split_clause,[],[f210,f212,f164])).

fof(f210,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f186,f86])).

fof(f186,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f93,f113])).

fof(f209,plain,
    ( ~ spl3_1
    | spl3_8 ),
    inference(avatar_split_clause,[],[f204,f206,f164])).

fof(f204,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f185,f86])).

% (28910)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
fof(f185,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f93,f112])).

fof(f191,plain,
    ( ~ spl3_1
    | spl3_5 ),
    inference(avatar_split_clause,[],[f187,f189,f164])).

fof(f187,plain,(
    ! [X0] :
      ( k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f182,f86])).

fof(f182,plain,(
    ! [X0] :
      ( k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f93,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).

fof(f181,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f172,f178,f174])).

fof(f172,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f89,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f171,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f162,f168,f164])).

fof(f162,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f86,f110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:26:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (28700)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (28701)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (28716)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (28717)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (28699)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (28707)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.57  % (28708)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.57  % (28715)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.57  % (28709)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.57  % (28709)Refutation not found, incomplete strategy% (28709)------------------------------
% 0.21/0.57  % (28709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (28709)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  % (28718)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.58  
% 0.21/0.58  % (28709)Memory used [KB]: 10746
% 0.21/0.58  % (28709)Time elapsed: 0.149 s
% 0.21/0.58  % (28709)------------------------------
% 0.21/0.58  % (28709)------------------------------
% 1.73/0.58  % (28710)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.73/0.59  % (28706)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.73/0.59  % (28705)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.73/0.59  % (28702)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.73/0.60  % (28712)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.73/0.60  % (28722)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.86/0.60  % (28721)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.86/0.60  % (28704)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.86/0.60  % (28698)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.86/0.60  % (28696)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.86/0.60  % (28697)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.86/0.61  % (28694)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.86/0.61  % (28695)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.86/0.61  % (28720)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.86/0.61  % (28714)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.86/0.61  % (28713)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.86/0.62  % (28693)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.86/0.62  % (28703)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.86/0.62  % (28711)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.06/0.63  % (28719)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.06/0.69  % (28724)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.34/0.83  % (28717)Time limit reached!
% 3.34/0.83  % (28717)------------------------------
% 3.34/0.83  % (28717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.34/0.83  % (28717)Termination reason: Time limit
% 3.34/0.83  
% 3.34/0.83  % (28717)Memory used [KB]: 13048
% 3.34/0.83  % (28717)Time elapsed: 0.407 s
% 3.34/0.83  % (28717)------------------------------
% 3.34/0.83  % (28717)------------------------------
% 3.34/0.84  % (28695)Time limit reached!
% 3.34/0.84  % (28695)------------------------------
% 3.34/0.84  % (28695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.34/0.86  % (28695)Termination reason: Time limit
% 3.34/0.86  % (28695)Termination phase: Saturation
% 3.34/0.86  
% 3.34/0.86  % (28695)Memory used [KB]: 6780
% 3.34/0.86  % (28695)Time elapsed: 0.400 s
% 3.34/0.86  % (28695)------------------------------
% 3.34/0.86  % (28695)------------------------------
% 4.09/0.93  % (28722)Time limit reached!
% 4.09/0.93  % (28722)------------------------------
% 4.09/0.93  % (28722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.93  % (28722)Termination reason: Time limit
% 4.09/0.93  % (28722)Termination phase: Saturation
% 4.09/0.93  
% 4.09/0.93  % (28722)Memory used [KB]: 5756
% 4.09/0.93  % (28722)Time elapsed: 0.511 s
% 4.09/0.93  % (28722)------------------------------
% 4.09/0.93  % (28722)------------------------------
% 4.35/0.93  % (28699)Time limit reached!
% 4.35/0.93  % (28699)------------------------------
% 4.35/0.93  % (28699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.93  % (28699)Termination reason: Time limit
% 4.35/0.93  % (28699)Termination phase: Saturation
% 4.35/0.93  
% 4.35/0.93  % (28699)Memory used [KB]: 16502
% 4.35/0.93  % (28699)Time elapsed: 0.500 s
% 4.35/0.93  % (28699)------------------------------
% 4.35/0.93  % (28699)------------------------------
% 4.35/0.96  % (28707)Time limit reached!
% 4.35/0.96  % (28707)------------------------------
% 4.35/0.96  % (28707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.96  % (28707)Termination reason: Time limit
% 4.35/0.96  % (28707)Termination phase: Saturation
% 4.35/0.96  
% 4.35/0.96  % (28707)Memory used [KB]: 7036
% 4.35/0.96  % (28707)Time elapsed: 0.523 s
% 4.35/0.96  % (28707)------------------------------
% 4.35/0.96  % (28707)------------------------------
% 4.35/0.97  % (28845)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.35/0.98  % (28855)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.99/1.03  % (28882)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.99/1.04  % (28700)Time limit reached!
% 4.99/1.04  % (28700)------------------------------
% 4.99/1.04  % (28700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.99/1.04  % (28700)Termination reason: Time limit
% 4.99/1.04  
% 4.99/1.04  % (28700)Memory used [KB]: 6140
% 4.99/1.04  % (28700)Time elapsed: 0.616 s
% 4.99/1.04  % (28700)------------------------------
% 4.99/1.04  % (28700)------------------------------
% 4.99/1.07  % (28884)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.99/1.07  % (28883)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 6.41/1.18  % (28883)Refutation found. Thanks to Tanya!
% 6.41/1.18  % SZS status Theorem for theBenchmark
% 6.41/1.18  % SZS output start Proof for theBenchmark
% 6.41/1.18  fof(f2530,plain,(
% 6.41/1.18    $false),
% 6.41/1.18    inference(avatar_sat_refutation,[],[f171,f181,f191,f209,f215,f245,f274,f343,f1342,f1437,f2065,f2126,f2160,f2192,f2195,f2226,f2451,f2520])).
% 6.41/1.18  fof(f2520,plain,(
% 6.41/1.18    spl3_24 | ~spl3_31),
% 6.41/1.18    inference(avatar_contradiction_clause,[],[f2519])).
% 6.41/1.18  fof(f2519,plain,(
% 6.41/1.18    $false | (spl3_24 | ~spl3_31)),
% 6.41/1.18    inference(subsumption_resolution,[],[f2489,f93])).
% 6.41/1.18  fof(f93,plain,(
% 6.41/1.18    v2_funct_1(sK1)),
% 6.41/1.18    inference(cnf_transformation,[],[f81])).
% 6.41/1.18  fof(f81,plain,(
% 6.41/1.18    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 6.41/1.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f80,f79])).
% 6.41/1.18  fof(f79,plain,(
% 6.41/1.18    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 6.41/1.18    introduced(choice_axiom,[])).
% 6.41/1.18  fof(f80,plain,(
% 6.41/1.18    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 6.41/1.18    introduced(choice_axiom,[])).
% 6.41/1.18  fof(f39,plain,(
% 6.41/1.18    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 6.41/1.18    inference(flattening,[],[f38])).
% 6.41/1.18  fof(f38,plain,(
% 6.41/1.18    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 6.41/1.18    inference(ennf_transformation,[],[f36])).
% 6.41/1.18  fof(f36,negated_conjecture,(
% 6.41/1.18    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 6.41/1.18    inference(negated_conjecture,[],[f35])).
% 6.41/1.18  fof(f35,conjecture,(
% 6.41/1.18    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 6.41/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).
% 6.41/1.18  fof(f2489,plain,(
% 6.41/1.18    ~v2_funct_1(sK1) | (spl3_24 | ~spl3_31)),
% 6.41/1.18    inference(backward_demodulation,[],[f410,f552])).
% 6.41/1.18  fof(f552,plain,(
% 6.41/1.18    sK1 = sK2 | ~spl3_31),
% 6.41/1.18    inference(avatar_component_clause,[],[f550])).
% 6.41/1.18  fof(f550,plain,(
% 6.41/1.18    spl3_31 <=> sK1 = sK2),
% 6.41/1.18    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 6.41/1.18  fof(f410,plain,(
% 6.41/1.18    ~v2_funct_1(sK2) | spl3_24),
% 6.41/1.18    inference(avatar_component_clause,[],[f408])).
% 6.41/1.18  fof(f408,plain,(
% 6.41/1.18    spl3_24 <=> v2_funct_1(sK2)),
% 6.41/1.18    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 6.41/1.18  fof(f2451,plain,(
% 6.41/1.18    ~spl3_11 | ~spl3_12 | spl3_31),
% 6.41/1.18    inference(avatar_contradiction_clause,[],[f2450])).
% 6.41/1.18  fof(f2450,plain,(
% 6.41/1.18    $false | (~spl3_11 | ~spl3_12 | spl3_31)),
% 6.41/1.18    inference(subsumption_resolution,[],[f2449,f551])).
% 6.41/1.18  fof(f551,plain,(
% 6.41/1.18    sK1 != sK2 | spl3_31),
% 6.41/1.18    inference(avatar_component_clause,[],[f550])).
% 6.41/1.18  fof(f2449,plain,(
% 6.41/1.18    sK1 = sK2 | (~spl3_11 | ~spl3_12)),
% 6.41/1.18    inference(resolution,[],[f2241,f266])).
% 6.41/1.18  fof(f266,plain,(
% 6.41/1.18    v1_xboole_0(sK2) | ~spl3_12),
% 6.41/1.18    inference(avatar_component_clause,[],[f264])).
% 6.41/1.18  fof(f264,plain,(
% 6.41/1.18    spl3_12 <=> v1_xboole_0(sK2)),
% 6.41/1.18    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 6.41/1.18  fof(f2241,plain,(
% 6.41/1.18    ( ! [X0] : (~v1_xboole_0(X0) | sK1 = X0) ) | ~spl3_11),
% 6.41/1.18    inference(resolution,[],[f237,f129])).
% 6.41/1.18  fof(f129,plain,(
% 6.41/1.18    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 6.41/1.18    inference(cnf_transformation,[],[f63])).
% 6.41/1.18  fof(f63,plain,(
% 6.41/1.18    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 6.41/1.18    inference(ennf_transformation,[],[f3])).
% 6.41/1.18  fof(f3,axiom,(
% 6.41/1.18    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 6.41/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 6.41/1.18  fof(f237,plain,(
% 6.41/1.18    v1_xboole_0(sK1) | ~spl3_11),
% 6.41/1.18    inference(avatar_component_clause,[],[f235])).
% 6.41/1.18  fof(f235,plain,(
% 6.41/1.18    spl3_11 <=> v1_xboole_0(sK1)),
% 6.41/1.18    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 6.41/1.18  fof(f2226,plain,(
% 6.41/1.18    spl3_24 | spl3_58),
% 6.41/1.18    inference(avatar_split_clause,[],[f2225,f856,f408])).
% 6.41/1.18  fof(f856,plain,(
% 6.41/1.18    spl3_58 <=> k1_xboole_0 = sK0),
% 6.41/1.18    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 6.41/1.18  fof(f2225,plain,(
% 6.41/1.18    k1_xboole_0 = sK0 | v2_funct_1(sK2)),
% 6.41/1.18    inference(subsumption_resolution,[],[f2224,f89])).
% 6.41/1.18  fof(f89,plain,(
% 6.41/1.18    v1_funct_1(sK2)),
% 6.41/1.18    inference(cnf_transformation,[],[f81])).
% 6.41/1.18  fof(f2224,plain,(
% 6.41/1.18    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 6.41/1.18    inference(subsumption_resolution,[],[f2223,f90])).
% 6.41/1.18  fof(f90,plain,(
% 6.41/1.18    v1_funct_2(sK2,sK0,sK0)),
% 6.41/1.18    inference(cnf_transformation,[],[f81])).
% 6.41/1.18  fof(f2223,plain,(
% 6.41/1.18    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 6.41/1.18    inference(subsumption_resolution,[],[f2222,f91])).
% 6.41/1.18  fof(f91,plain,(
% 6.41/1.18    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 6.41/1.18    inference(cnf_transformation,[],[f81])).
% 6.41/1.18  fof(f2222,plain,(
% 6.41/1.18    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 6.41/1.18    inference(subsumption_resolution,[],[f2221,f86])).
% 6.41/1.18  fof(f86,plain,(
% 6.41/1.18    v1_funct_1(sK1)),
% 6.41/1.18    inference(cnf_transformation,[],[f81])).
% 6.41/1.18  fof(f2221,plain,(
% 6.41/1.18    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 6.41/1.18    inference(subsumption_resolution,[],[f2220,f87])).
% 6.41/1.18  fof(f87,plain,(
% 6.41/1.18    v1_funct_2(sK1,sK0,sK0)),
% 6.41/1.18    inference(cnf_transformation,[],[f81])).
% 6.41/1.18  fof(f2220,plain,(
% 6.41/1.18    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 6.41/1.18    inference(subsumption_resolution,[],[f2219,f88])).
% 6.41/1.18  fof(f88,plain,(
% 6.41/1.18    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 6.41/1.18    inference(cnf_transformation,[],[f81])).
% 6.41/1.18  fof(f2219,plain,(
% 6.41/1.18    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 6.41/1.18    inference(subsumption_resolution,[],[f2016,f93])).
% 6.41/1.18  fof(f2016,plain,(
% 6.41/1.18    ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 6.41/1.18    inference(superposition,[],[f140,f1269])).
% 6.41/1.18  fof(f1269,plain,(
% 6.41/1.18    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)),
% 6.41/1.18    inference(backward_demodulation,[],[f679,f1143])).
% 6.41/1.18  fof(f1143,plain,(
% 6.41/1.18    sK1 = k5_relat_1(sK2,sK1)),
% 6.41/1.18    inference(subsumption_resolution,[],[f1115,f845])).
% 6.41/1.18  fof(f845,plain,(
% 6.41/1.18    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK1)),
% 6.41/1.18    inference(backward_demodulation,[],[f92,f679])).
% 6.41/1.18  fof(f92,plain,(
% 6.41/1.18    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)),
% 6.41/1.18    inference(cnf_transformation,[],[f81])).
% 6.41/1.18  fof(f1115,plain,(
% 6.41/1.18    sK1 = k5_relat_1(sK2,sK1) | ~r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK1)),
% 6.41/1.18    inference(resolution,[],[f867,f224])).
% 6.41/1.18  fof(f224,plain,(
% 6.41/1.18    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = X1 | ~r2_relset_1(sK0,sK0,X1,sK1)) )),
% 6.41/1.18    inference(resolution,[],[f88,f142])).
% 6.41/1.18  fof(f142,plain,(
% 6.41/1.18    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.41/1.18    inference(cnf_transformation,[],[f85])).
% 6.41/1.18  fof(f85,plain,(
% 6.41/1.18    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.41/1.18    inference(nnf_transformation,[],[f74])).
% 6.41/1.18  fof(f74,plain,(
% 6.41/1.18    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.41/1.18    inference(flattening,[],[f73])).
% 6.41/1.18  fof(f73,plain,(
% 6.41/1.18    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.41/1.18    inference(ennf_transformation,[],[f25])).
% 6.41/1.18  fof(f25,axiom,(
% 6.41/1.18    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 6.41/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 6.41/1.18  fof(f867,plain,(
% 6.41/1.18    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 6.41/1.18    inference(subsumption_resolution,[],[f866,f89])).
% 6.41/1.18  fof(f866,plain,(
% 6.41/1.18    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 6.41/1.18    inference(subsumption_resolution,[],[f865,f91])).
% 6.41/1.18  fof(f865,plain,(
% 6.41/1.18    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 6.41/1.18    inference(subsumption_resolution,[],[f864,f86])).
% 6.41/1.18  fof(f864,plain,(
% 6.41/1.18    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 6.41/1.18    inference(subsumption_resolution,[],[f847,f88])).
% 6.41/1.18  fof(f847,plain,(
% 6.41/1.18    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 6.41/1.18    inference(superposition,[],[f146,f679])).
% 6.41/1.18  fof(f146,plain,(
% 6.41/1.18    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.41/1.18    inference(cnf_transformation,[],[f78])).
% 6.41/1.18  fof(f78,plain,(
% 6.41/1.18    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.41/1.18    inference(flattening,[],[f77])).
% 6.41/1.18  fof(f77,plain,(
% 6.41/1.18    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.41/1.18    inference(ennf_transformation,[],[f27])).
% 6.41/1.18  fof(f27,axiom,(
% 6.41/1.18    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 6.41/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 6.41/1.18  fof(f679,plain,(
% 6.41/1.18    k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)),
% 6.41/1.18    inference(subsumption_resolution,[],[f670,f89])).
% 6.41/1.18  fof(f670,plain,(
% 6.41/1.18    k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) | ~v1_funct_1(sK2)),
% 6.41/1.18    inference(resolution,[],[f239,f91])).
% 6.41/1.18  fof(f239,plain,(
% 6.41/1.18    ( ! [X4,X2,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X2,X3,sK0,sK0,X4,sK1) = k5_relat_1(X4,sK1) | ~v1_funct_1(X4)) )),
% 6.41/1.18    inference(subsumption_resolution,[],[f225,f86])).
% 6.41/1.18  fof(f225,plain,(
% 6.41/1.18    ( ! [X4,X2,X3] : (k1_partfun1(X2,X3,sK0,sK0,X4,sK1) = k5_relat_1(X4,sK1) | ~v1_funct_1(sK1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 6.41/1.18    inference(resolution,[],[f88,f144])).
% 6.41/1.18  fof(f144,plain,(
% 6.41/1.18    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.41/1.18    inference(cnf_transformation,[],[f76])).
% 6.41/1.18  fof(f76,plain,(
% 6.41/1.18    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.41/1.18    inference(flattening,[],[f75])).
% 6.41/1.18  fof(f75,plain,(
% 6.41/1.18    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.41/1.18    inference(ennf_transformation,[],[f29])).
% 6.41/1.18  fof(f29,axiom,(
% 6.41/1.18    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 6.41/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 6.41/1.18  fof(f140,plain,(
% 6.41/1.18    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 6.41/1.18    inference(cnf_transformation,[],[f72])).
% 6.41/1.18  fof(f72,plain,(
% 6.41/1.18    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 6.41/1.18    inference(flattening,[],[f71])).
% 6.41/1.18  fof(f71,plain,(
% 6.41/1.18    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 6.41/1.18    inference(ennf_transformation,[],[f31])).
% 6.41/1.18  fof(f31,axiom,(
% 6.41/1.18    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 6.41/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 6.41/1.18  fof(f2195,plain,(
% 6.41/1.18    ~spl3_10 | spl3_11),
% 6.41/1.18    inference(avatar_split_clause,[],[f2194,f235,f231])).
% 6.41/1.18  fof(f231,plain,(
% 6.41/1.18    spl3_10 <=> v1_xboole_0(sK0)),
% 6.41/1.18    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 6.41/1.18  fof(f2194,plain,(
% 6.41/1.18    v1_xboole_0(sK1) | ~v1_xboole_0(sK0)),
% 6.41/1.18    inference(forward_demodulation,[],[f1116,f1143])).
% 6.41/1.18  fof(f1116,plain,(
% 6.41/1.18    v1_xboole_0(k5_relat_1(sK2,sK1)) | ~v1_xboole_0(sK0)),
% 6.41/1.18    inference(resolution,[],[f867,f120])).
% 6.41/1.18  fof(f120,plain,(
% 6.41/1.18    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 6.41/1.18    inference(cnf_transformation,[],[f56])).
% 6.41/1.18  fof(f56,plain,(
% 6.41/1.18    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 6.41/1.18    inference(ennf_transformation,[],[f21])).
% 6.41/1.18  fof(f21,axiom,(
% 6.41/1.18    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 6.41/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 6.41/1.18  fof(f2192,plain,(
% 6.41/1.18    ~spl3_10 | spl3_12),
% 6.41/1.18    inference(avatar_split_clause,[],[f1513,f264,f231])).
% 6.41/1.18  fof(f1513,plain,(
% 6.41/1.18    v1_xboole_0(sK2) | ~v1_xboole_0(sK0)),
% 6.41/1.18    inference(resolution,[],[f91,f120])).
% 6.41/1.18  fof(f2160,plain,(
% 6.41/1.18    ~spl3_33),
% 6.41/1.18    inference(avatar_contradiction_clause,[],[f2159])).
% 6.41/1.18  fof(f2159,plain,(
% 6.41/1.18    $false | ~spl3_33),
% 6.41/1.18    inference(subsumption_resolution,[],[f2138,f260])).
% 6.41/1.18  fof(f260,plain,(
% 6.41/1.18    r2_relset_1(sK0,sK0,sK2,sK2)),
% 6.41/1.18    inference(resolution,[],[f91,f161])).
% 6.41/1.18  fof(f161,plain,(
% 6.41/1.18    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 6.41/1.18    inference(duplicate_literal_removal,[],[f160])).
% 6.41/1.18  fof(f160,plain,(
% 6.41/1.18    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.41/1.18    inference(equality_resolution,[],[f143])).
% 6.41/1.18  fof(f143,plain,(
% 6.41/1.18    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.41/1.18    inference(cnf_transformation,[],[f85])).
% 6.41/1.18  fof(f2138,plain,(
% 6.41/1.18    ~r2_relset_1(sK0,sK0,sK2,sK2) | ~spl3_33),
% 6.41/1.18    inference(backward_demodulation,[],[f94,f571])).
% 6.41/1.18  fof(f571,plain,(
% 6.41/1.18    k6_partfun1(sK0) = sK2 | ~spl3_33),
% 6.41/1.18    inference(avatar_component_clause,[],[f569])).
% 6.41/1.18  fof(f569,plain,(
% 6.41/1.18    spl3_33 <=> k6_partfun1(sK0) = sK2),
% 6.41/1.18    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 6.41/1.18  fof(f94,plain,(
% 6.41/1.18    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 6.41/1.18    inference(cnf_transformation,[],[f81])).
% 6.41/1.18  fof(f2126,plain,(
% 6.41/1.18    ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_9 | ~spl3_16 | ~spl3_17 | ~spl3_24 | spl3_33 | ~spl3_81),
% 6.41/1.18    inference(avatar_contradiction_clause,[],[f2125])).
% 6.41/1.18  fof(f2125,plain,(
% 6.41/1.18    $false | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_9 | ~spl3_16 | ~spl3_17 | ~spl3_24 | spl3_33 | ~spl3_81)),
% 6.41/1.18    inference(subsumption_resolution,[],[f2066,f310])).
% 6.41/1.18  fof(f310,plain,(
% 6.41/1.18    sK0 = k2_relat_1(sK2) | ~spl3_16),
% 6.41/1.18    inference(avatar_component_clause,[],[f308])).
% 6.41/1.18  fof(f308,plain,(
% 6.41/1.18    spl3_16 <=> sK0 = k2_relat_1(sK2)),
% 6.41/1.18    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 6.41/1.18  fof(f2066,plain,(
% 6.41/1.18    sK0 != k2_relat_1(sK2) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_9 | ~spl3_17 | ~spl3_24 | spl3_33 | ~spl3_81)),
% 6.41/1.18    inference(subsumption_resolution,[],[f1992,f2014])).
% 6.41/1.18  fof(f2014,plain,(
% 6.41/1.18    k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_24 | spl3_33 | ~spl3_81)),
% 6.41/1.18    inference(subsumption_resolution,[],[f2013,f401])).
% 6.41/1.18  fof(f401,plain,(
% 6.41/1.18    sK0 = k1_relat_1(sK2)),
% 6.41/1.18    inference(forward_demodulation,[],[f250,f271])).
% 6.41/1.18  fof(f271,plain,(
% 6.41/1.18    sK0 = k1_relset_1(sK0,sK0,sK2)),
% 6.41/1.18    inference(subsumption_resolution,[],[f270,f89])).
% 6.41/1.18  fof(f270,plain,(
% 6.41/1.18    sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_1(sK2)),
% 6.41/1.18    inference(subsumption_resolution,[],[f261,f90])).
% 6.41/1.18  fof(f261,plain,(
% 6.41/1.18    sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 6.41/1.18    inference(resolution,[],[f91,f125])).
% 6.41/1.18  fof(f125,plain,(
% 6.41/1.18    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 6.41/1.18    inference(cnf_transformation,[],[f62])).
% 6.41/1.18  fof(f62,plain,(
% 6.41/1.18    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 6.41/1.18    inference(flattening,[],[f61])).
% 6.41/1.18  fof(f61,plain,(
% 6.41/1.18    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 6.41/1.18    inference(ennf_transformation,[],[f34])).
% 6.41/1.18  fof(f34,axiom,(
% 6.41/1.18    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 6.41/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 6.41/1.18  fof(f250,plain,(
% 6.41/1.18    k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)),
% 6.41/1.18    inference(resolution,[],[f91,f130])).
% 6.41/1.18  fof(f130,plain,(
% 6.41/1.18    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 6.41/1.18    inference(cnf_transformation,[],[f64])).
% 6.41/1.18  fof(f64,plain,(
% 6.41/1.18    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.41/1.18    inference(ennf_transformation,[],[f22])).
% 6.41/1.18  fof(f22,axiom,(
% 6.41/1.18    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 6.41/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 6.41/1.18  fof(f2013,plain,(
% 6.41/1.18    sK0 != k1_relat_1(sK2) | k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_24 | spl3_33 | ~spl3_81)),
% 6.41/1.18    inference(forward_demodulation,[],[f2012,f1581])).
% 6.41/1.18  fof(f1581,plain,(
% 6.41/1.18    sK0 = k2_relat_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_24)),
% 6.41/1.18    inference(forward_demodulation,[],[f1457,f401])).
% 6.41/1.18  fof(f1457,plain,(
% 6.41/1.18    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_24)),
% 6.41/1.18    inference(subsumption_resolution,[],[f1456,f175])).
% 6.41/1.18  fof(f175,plain,(
% 6.41/1.18    v1_relat_1(sK2) | ~spl3_3),
% 6.41/1.18    inference(avatar_component_clause,[],[f174])).
% 6.41/1.18  fof(f174,plain,(
% 6.41/1.18    spl3_3 <=> v1_relat_1(sK2)),
% 6.41/1.18    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 6.41/1.18  fof(f1456,plain,(
% 6.41/1.18    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~spl3_24),
% 6.41/1.18    inference(subsumption_resolution,[],[f1444,f89])).
% 6.41/1.18  fof(f1444,plain,(
% 6.41/1.18    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_24),
% 6.41/1.18    inference(resolution,[],[f409,f113])).
% 6.41/1.18  fof(f113,plain,(
% 6.41/1.18    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.41/1.18    inference(cnf_transformation,[],[f47])).
% 6.41/1.18  fof(f47,plain,(
% 6.41/1.18    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.41/1.18    inference(flattening,[],[f46])).
% 6.41/1.18  fof(f46,plain,(
% 6.41/1.18    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.41/1.18    inference(ennf_transformation,[],[f16])).
% 6.41/1.18  fof(f16,axiom,(
% 6.41/1.18    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 6.41/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 6.41/1.18  fof(f409,plain,(
% 6.41/1.18    v2_funct_1(sK2) | ~spl3_24),
% 6.41/1.18    inference(avatar_component_clause,[],[f408])).
% 6.41/1.18  fof(f2012,plain,(
% 6.41/1.18    k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_24 | spl3_33 | ~spl3_81)),
% 6.41/1.18    inference(subsumption_resolution,[],[f2011,f570])).
% 6.41/1.18  fof(f570,plain,(
% 6.41/1.18    k6_partfun1(sK0) != sK2 | spl3_33),
% 6.41/1.18    inference(avatar_component_clause,[],[f569])).
% 6.41/1.18  fof(f2011,plain,(
% 6.41/1.18    k6_partfun1(sK0) = sK2 | k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_24 | ~spl3_81)),
% 6.41/1.18    inference(forward_demodulation,[],[f2010,f401])).
% 6.41/1.18  fof(f2010,plain,(
% 6.41/1.18    k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2)) | sK2 = k6_partfun1(k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_24 | ~spl3_81)),
% 6.41/1.18    inference(subsumption_resolution,[],[f2009,f180])).
% 6.41/1.18  fof(f180,plain,(
% 6.41/1.18    v1_relat_1(k2_funct_1(sK2)) | ~spl3_4),
% 6.41/1.18    inference(avatar_component_clause,[],[f178])).
% 6.41/1.18  fof(f178,plain,(
% 6.41/1.18    spl3_4 <=> v1_relat_1(k2_funct_1(sK2))),
% 6.41/1.18    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 6.41/1.18  fof(f2009,plain,(
% 6.41/1.18    k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2)) | sK2 = k6_partfun1(k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_24 | ~spl3_81)),
% 6.41/1.18    inference(subsumption_resolution,[],[f2008,f1321])).
% 6.41/1.18  fof(f1321,plain,(
% 6.41/1.18    v1_funct_1(k2_funct_1(sK2)) | ~spl3_81),
% 6.41/1.18    inference(avatar_component_clause,[],[f1319])).
% 6.41/1.18  fof(f1319,plain,(
% 6.41/1.18    spl3_81 <=> v1_funct_1(k2_funct_1(sK2))),
% 6.41/1.18    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).
% 6.41/1.18  fof(f2008,plain,(
% 6.41/1.18    k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2)) | sK2 = k6_partfun1(k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_24)),
% 6.41/1.18    inference(subsumption_resolution,[],[f2007,f175])).
% 6.41/1.18  fof(f2007,plain,(
% 6.41/1.18    k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2)) | sK2 = k6_partfun1(k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_24)),
% 6.41/1.18    inference(subsumption_resolution,[],[f2006,f89])).
% 6.41/1.18  fof(f2006,plain,(
% 6.41/1.18    k2_funct_1(sK2) != k6_partfun1(k2_relat_1(sK2)) | sK2 = k6_partfun1(k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_24)),
% 6.41/1.18    inference(superposition,[],[f156,f1453])).
% 6.41/1.18  fof(f1453,plain,(
% 6.41/1.18    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) | (~spl3_3 | ~spl3_24)),
% 6.41/1.18    inference(subsumption_resolution,[],[f1452,f175])).
% 6.41/1.18  fof(f1452,plain,(
% 6.41/1.18    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl3_24),
% 6.41/1.18    inference(subsumption_resolution,[],[f1442,f89])).
% 6.41/1.18  fof(f1442,plain,(
% 6.41/1.18    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_24),
% 6.41/1.18    inference(resolution,[],[f409,f154])).
% 6.41/1.18  fof(f154,plain,(
% 6.41/1.18    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.41/1.18    inference(definition_unfolding,[],[f115,f96])).
% 6.41/1.18  fof(f96,plain,(
% 6.41/1.18    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 6.41/1.18    inference(cnf_transformation,[],[f30])).
% 6.41/1.18  fof(f30,axiom,(
% 6.41/1.18    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 6.41/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 6.41/1.18  fof(f115,plain,(
% 6.41/1.18    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.41/1.18    inference(cnf_transformation,[],[f49])).
% 6.41/1.18  fof(f49,plain,(
% 6.41/1.18    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.41/1.18    inference(flattening,[],[f48])).
% 6.41/1.18  fof(f48,plain,(
% 6.41/1.18    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.41/1.18    inference(ennf_transformation,[],[f17])).
% 6.41/1.18  fof(f17,axiom,(
% 6.41/1.18    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 6.41/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 6.41/1.18  fof(f156,plain,(
% 6.41/1.18    ( ! [X0,X1] : (k5_relat_1(X0,X1) != X0 | k6_partfun1(k1_relat_1(X1)) = X1 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.41/1.18    inference(definition_unfolding,[],[f118,f96])).
% 6.41/1.18  fof(f118,plain,(
% 6.41/1.18    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.41/1.18    inference(cnf_transformation,[],[f55])).
% 6.41/1.18  fof(f55,plain,(
% 6.41/1.18    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.41/1.18    inference(flattening,[],[f54])).
% 6.41/1.18  fof(f54,plain,(
% 6.41/1.18    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.41/1.18    inference(ennf_transformation,[],[f15])).
% 6.41/1.18  fof(f15,axiom,(
% 6.41/1.18    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 6.41/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).
% 6.41/1.18  fof(f1992,plain,(
% 6.41/1.18    sK0 != k2_relat_1(sK2) | k2_funct_1(sK2) = k6_partfun1(k2_relat_1(sK2)) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_9 | ~spl3_17 | ~spl3_24 | ~spl3_81)),
% 6.41/1.18    inference(forward_demodulation,[],[f1991,f359])).
% 6.41/1.18  fof(f359,plain,(
% 6.41/1.18    sK0 = k2_relat_1(k2_funct_1(sK1)) | ~spl3_9),
% 6.41/1.18    inference(backward_demodulation,[],[f214,f358])).
% 6.41/1.18  fof(f358,plain,(
% 6.41/1.18    sK0 = k1_relat_1(sK1)),
% 6.41/1.18    inference(forward_demodulation,[],[f217,f242])).
% 6.41/1.18  fof(f242,plain,(
% 6.41/1.18    sK0 = k1_relset_1(sK0,sK0,sK1)),
% 6.41/1.18    inference(subsumption_resolution,[],[f241,f86])).
% 6.41/1.18  fof(f241,plain,(
% 6.41/1.18    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1)),
% 6.41/1.18    inference(subsumption_resolution,[],[f228,f87])).
% 6.41/1.18  fof(f228,plain,(
% 6.41/1.18    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 6.41/1.18    inference(resolution,[],[f88,f125])).
% 6.41/1.18  fof(f217,plain,(
% 6.41/1.18    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 6.41/1.18    inference(resolution,[],[f88,f130])).
% 6.41/1.18  fof(f214,plain,(
% 6.41/1.18    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~spl3_9),
% 6.41/1.18    inference(avatar_component_clause,[],[f212])).
% 6.41/1.18  fof(f212,plain,(
% 6.41/1.18    spl3_9 <=> k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))),
% 6.41/1.18    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 6.41/1.18  fof(f1991,plain,(
% 6.41/1.18    k2_relat_1(k2_funct_1(sK1)) != k2_relat_1(sK2) | k2_funct_1(sK2) = k6_partfun1(k2_relat_1(sK2)) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_17 | ~spl3_24 | ~spl3_81)),
% 6.41/1.18    inference(forward_demodulation,[],[f1990,f1455])).
% 6.41/1.18  fof(f1455,plain,(
% 6.41/1.18    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_24)),
% 6.41/1.18    inference(subsumption_resolution,[],[f1454,f175])).
% 6.41/1.18  fof(f1454,plain,(
% 6.41/1.18    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~spl3_24),
% 6.41/1.18    inference(subsumption_resolution,[],[f1443,f89])).
% 6.41/1.18  fof(f1443,plain,(
% 6.41/1.18    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_24),
% 6.41/1.18    inference(resolution,[],[f409,f112])).
% 6.48/1.18  fof(f112,plain,(
% 6.48/1.18    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.48/1.18    inference(cnf_transformation,[],[f47])).
% 6.48/1.18  fof(f1990,plain,(
% 6.48/1.18    k2_funct_1(sK2) = k6_partfun1(k2_relat_1(sK2)) | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2)) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_17 | ~spl3_24 | ~spl3_81)),
% 6.48/1.18    inference(forward_demodulation,[],[f1989,f1455])).
% 6.48/1.18  fof(f1989,plain,(
% 6.48/1.18    k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2))) | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2)) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_17 | ~spl3_24 | ~spl3_81)),
% 6.48/1.18    inference(subsumption_resolution,[],[f1988,f170])).
% 6.48/1.18  fof(f170,plain,(
% 6.48/1.18    v1_relat_1(k2_funct_1(sK1)) | ~spl3_2),
% 6.48/1.18    inference(avatar_component_clause,[],[f168])).
% 6.48/1.18  fof(f168,plain,(
% 6.48/1.18    spl3_2 <=> v1_relat_1(k2_funct_1(sK1))),
% 6.48/1.18    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 6.48/1.18  fof(f1988,plain,(
% 6.48/1.18    k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2))) | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_17 | ~spl3_24 | ~spl3_81)),
% 6.48/1.18    inference(subsumption_resolution,[],[f1987,f318])).
% 6.48/1.18  fof(f318,plain,(
% 6.48/1.18    v1_funct_1(k2_funct_1(sK1)) | ~spl3_17),
% 6.48/1.18    inference(avatar_component_clause,[],[f317])).
% 6.48/1.18  fof(f317,plain,(
% 6.48/1.18    spl3_17 <=> v1_funct_1(k2_funct_1(sK1))),
% 6.48/1.18    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 6.48/1.18  fof(f1987,plain,(
% 6.48/1.18    k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2))) | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_24 | ~spl3_81)),
% 6.48/1.18    inference(subsumption_resolution,[],[f1986,f180])).
% 6.48/1.18  fof(f1986,plain,(
% 6.48/1.18    k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2))) | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl3_3 | ~spl3_5 | ~spl3_24 | ~spl3_81)),
% 6.48/1.18    inference(subsumption_resolution,[],[f1985,f1321])).
% 6.48/1.18  fof(f1985,plain,(
% 6.48/1.18    k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2))) | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl3_3 | ~spl3_5 | ~spl3_24)),
% 6.48/1.18    inference(trivial_inequality_removal,[],[f1984])).
% 6.48/1.18  fof(f1984,plain,(
% 6.48/1.18    k2_funct_1(sK1) != k2_funct_1(sK1) | k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2))) | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl3_3 | ~spl3_5 | ~spl3_24)),
% 6.48/1.18    inference(superposition,[],[f156,f1447])).
% 6.48/1.18  fof(f1447,plain,(
% 6.48/1.18    k2_funct_1(sK1) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) | (~spl3_3 | ~spl3_5 | ~spl3_24)),
% 6.48/1.18    inference(forward_demodulation,[],[f1446,f1143])).
% 6.48/1.18  fof(f1446,plain,(
% 6.48/1.18    k2_funct_1(k5_relat_1(sK2,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) | (~spl3_3 | ~spl3_5 | ~spl3_24)),
% 6.48/1.18    inference(subsumption_resolution,[],[f1445,f89])).
% 6.48/1.18  fof(f1445,plain,(
% 6.48/1.18    ~v1_funct_1(sK2) | k2_funct_1(k5_relat_1(sK2,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) | (~spl3_3 | ~spl3_5 | ~spl3_24)),
% 6.48/1.18    inference(subsumption_resolution,[],[f1439,f175])).
% 6.48/1.18  fof(f1439,plain,(
% 6.48/1.18    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k2_funct_1(k5_relat_1(sK2,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) | (~spl3_5 | ~spl3_24)),
% 6.48/1.18    inference(resolution,[],[f409,f190])).
% 6.48/1.18  fof(f190,plain,(
% 6.48/1.18    ( ! [X0] : (~v2_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0))) ) | ~spl3_5),
% 6.48/1.18    inference(avatar_component_clause,[],[f189])).
% 6.48/1.18  fof(f189,plain,(
% 6.48/1.18    spl3_5 <=> ! [X0] : (k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0))),
% 6.48/1.18    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 6.48/1.18  fof(f2065,plain,(
% 6.48/1.18    ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_8 | ~spl3_9 | spl3_16 | ~spl3_17),
% 6.48/1.18    inference(avatar_contradiction_clause,[],[f2064])).
% 6.48/1.18  fof(f2064,plain,(
% 6.48/1.18    $false | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_8 | ~spl3_9 | spl3_16 | ~spl3_17)),
% 6.48/1.18    inference(subsumption_resolution,[],[f2063,f309])).
% 6.48/1.18  fof(f309,plain,(
% 6.48/1.18    sK0 != k2_relat_1(sK2) | spl3_16),
% 6.48/1.18    inference(avatar_component_clause,[],[f308])).
% 6.48/1.18  fof(f2063,plain,(
% 6.48/1.18    sK0 = k2_relat_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_8 | ~spl3_9 | ~spl3_17)),
% 6.48/1.18    inference(forward_demodulation,[],[f2062,f713])).
% 6.48/1.18  fof(f713,plain,(
% 6.48/1.18    sK0 = k9_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) | (~spl3_2 | ~spl3_8 | ~spl3_9 | ~spl3_17)),
% 6.48/1.18    inference(forward_demodulation,[],[f709,f359])).
% 6.48/1.18  fof(f709,plain,(
% 6.48/1.18    k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) | (~spl3_2 | ~spl3_8 | ~spl3_9 | ~spl3_17)),
% 6.48/1.18    inference(superposition,[],[f278,f533])).
% 6.48/1.18  fof(f533,plain,(
% 6.48/1.18    k2_funct_1(sK1) = k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) | (~spl3_2 | ~spl3_8 | ~spl3_9 | ~spl3_17)),
% 6.48/1.18    inference(subsumption_resolution,[],[f532,f170])).
% 6.48/1.18  fof(f532,plain,(
% 6.48/1.18    k2_funct_1(sK1) = k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl3_2 | ~spl3_8 | ~spl3_9 | ~spl3_17)),
% 6.48/1.18    inference(resolution,[],[f514,f124])).
% 6.48/1.18  fof(f124,plain,(
% 6.48/1.18    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 6.48/1.18    inference(cnf_transformation,[],[f60])).
% 6.48/1.18  fof(f60,plain,(
% 6.48/1.18    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.48/1.18    inference(flattening,[],[f59])).
% 6.48/1.18  fof(f59,plain,(
% 6.48/1.18    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 6.48/1.18    inference(ennf_transformation,[],[f9])).
% 6.48/1.18  fof(f9,axiom,(
% 6.48/1.18    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 6.48/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 6.48/1.18  fof(f514,plain,(
% 6.48/1.18    v4_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) | (~spl3_2 | ~spl3_8 | ~spl3_9 | ~spl3_17)),
% 6.48/1.18    inference(resolution,[],[f379,f132])).
% 6.48/1.18  fof(f132,plain,(
% 6.48/1.18    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 6.48/1.18    inference(cnf_transformation,[],[f66])).
% 6.48/1.18  fof(f66,plain,(
% 6.48/1.18    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.48/1.18    inference(ennf_transformation,[],[f20])).
% 6.48/1.18  fof(f20,axiom,(
% 6.48/1.18    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.48/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 6.48/1.18  fof(f379,plain,(
% 6.48/1.18    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK1),sK0))) | (~spl3_2 | ~spl3_8 | ~spl3_9 | ~spl3_17)),
% 6.48/1.18    inference(forward_demodulation,[],[f378,f208])).
% 6.48/1.18  fof(f208,plain,(
% 6.48/1.18    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | ~spl3_8),
% 6.48/1.18    inference(avatar_component_clause,[],[f206])).
% 6.48/1.18  fof(f206,plain,(
% 6.48/1.18    spl3_8 <=> k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))),
% 6.48/1.18    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 6.48/1.18  fof(f378,plain,(
% 6.48/1.18    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),sK0))) | (~spl3_2 | ~spl3_9 | ~spl3_17)),
% 6.48/1.18    inference(subsumption_resolution,[],[f377,f170])).
% 6.48/1.18  fof(f377,plain,(
% 6.48/1.18    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),sK0))) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl3_9 | ~spl3_17)),
% 6.48/1.18    inference(subsumption_resolution,[],[f372,f318])).
% 6.48/1.18  fof(f372,plain,(
% 6.48/1.18    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~spl3_9),
% 6.48/1.18    inference(superposition,[],[f109,f359])).
% 6.48/1.18  fof(f109,plain,(
% 6.48/1.18    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.48/1.18    inference(cnf_transformation,[],[f43])).
% 6.48/1.18  fof(f43,plain,(
% 6.48/1.18    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.48/1.18    inference(flattening,[],[f42])).
% 6.48/1.18  fof(f42,plain,(
% 6.48/1.18    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.48/1.18    inference(ennf_transformation,[],[f33])).
% 6.48/1.18  fof(f33,axiom,(
% 6.48/1.18    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 6.48/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 6.48/1.18  fof(f278,plain,(
% 6.48/1.18    ( ! [X0] : (k2_relat_1(k7_relat_1(k2_funct_1(sK1),X0)) = k9_relat_1(k2_funct_1(sK1),X0)) ) | ~spl3_2),
% 6.48/1.18    inference(resolution,[],[f170,f121])).
% 6.48/1.18  fof(f121,plain,(
% 6.48/1.18    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 6.48/1.18    inference(cnf_transformation,[],[f57])).
% 6.48/1.18  fof(f57,plain,(
% 6.48/1.18    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.48/1.18    inference(ennf_transformation,[],[f7])).
% 6.48/1.18  fof(f7,axiom,(
% 6.48/1.18    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 6.48/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 6.48/1.18  fof(f2062,plain,(
% 6.48/1.18    k2_relat_1(sK2) = k9_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) | (~spl3_1 | ~spl3_3)),
% 6.48/1.18    inference(forward_demodulation,[],[f2055,f1270])).
% 6.48/1.18  fof(f1270,plain,(
% 6.48/1.18    k2_relat_1(sK1) = k9_relat_1(sK1,k2_relat_1(sK2)) | (~spl3_1 | ~spl3_3)),
% 6.48/1.18    inference(backward_demodulation,[],[f763,f1143])).
% 6.48/1.18  fof(f763,plain,(
% 6.48/1.18    k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2)) | (~spl3_1 | ~spl3_3)),
% 6.48/1.18    inference(resolution,[],[f248,f175])).
% 6.48/1.18  fof(f248,plain,(
% 6.48/1.18    ( ! [X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X1,sK1)) = k9_relat_1(sK1,k2_relat_1(X1))) ) | ~spl3_1),
% 6.48/1.18    inference(resolution,[],[f165,f105])).
% 6.48/1.18  fof(f105,plain,(
% 6.48/1.18    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 6.48/1.18    inference(cnf_transformation,[],[f40])).
% 6.48/1.18  fof(f40,plain,(
% 6.48/1.18    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 6.48/1.18    inference(ennf_transformation,[],[f8])).
% 6.48/1.18  fof(f8,axiom,(
% 6.48/1.18    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 6.48/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 6.48/1.18  fof(f165,plain,(
% 6.48/1.18    v1_relat_1(sK1) | ~spl3_1),
% 6.48/1.18    inference(avatar_component_clause,[],[f164])).
% 6.48/1.18  fof(f164,plain,(
% 6.48/1.18    spl3_1 <=> v1_relat_1(sK1)),
% 6.48/1.18    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 6.48/1.18  fof(f2055,plain,(
% 6.48/1.18    k2_relat_1(sK2) = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k2_relat_1(sK2))) | (~spl3_1 | ~spl3_3)),
% 6.48/1.18    inference(resolution,[],[f365,f289])).
% 6.48/1.18  fof(f289,plain,(
% 6.48/1.18    r1_tarski(k2_relat_1(sK2),sK0) | ~spl3_3),
% 6.48/1.18    inference(subsumption_resolution,[],[f288,f175])).
% 6.48/1.18  fof(f288,plain,(
% 6.48/1.18    r1_tarski(k2_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 6.48/1.18    inference(resolution,[],[f253,f122])).
% 6.48/1.18  fof(f122,plain,(
% 6.48/1.18    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 6.48/1.18    inference(cnf_transformation,[],[f82])).
% 6.48/1.18  fof(f82,plain,(
% 6.48/1.18    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.48/1.18    inference(nnf_transformation,[],[f58])).
% 6.48/1.18  fof(f58,plain,(
% 6.48/1.18    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.48/1.18    inference(ennf_transformation,[],[f5])).
% 6.48/1.18  fof(f5,axiom,(
% 6.48/1.18    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 6.48/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 6.48/1.18  fof(f253,plain,(
% 6.48/1.18    v5_relat_1(sK2,sK0)),
% 6.48/1.18    inference(resolution,[],[f91,f133])).
% 6.48/1.18  fof(f133,plain,(
% 6.48/1.18    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 6.48/1.18    inference(cnf_transformation,[],[f66])).
% 6.48/1.18  fof(f365,plain,(
% 6.48/1.18    ( ! [X0] : (~r1_tarski(X0,sK0) | k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0) ) | ~spl3_1),
% 6.48/1.18    inference(subsumption_resolution,[],[f364,f165])).
% 6.48/1.18  fof(f364,plain,(
% 6.48/1.18    ( ! [X0] : (~r1_tarski(X0,sK0) | k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0 | ~v1_relat_1(sK1)) )),
% 6.48/1.18    inference(subsumption_resolution,[],[f363,f86])).
% 6.48/1.18  fof(f363,plain,(
% 6.48/1.18    ( ! [X0] : (~r1_tarski(X0,sK0) | k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 6.48/1.18    inference(subsumption_resolution,[],[f360,f93])).
% 6.48/1.18  fof(f360,plain,(
% 6.48/1.18    ( ! [X0] : (~r1_tarski(X0,sK0) | k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0 | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 6.48/1.18    inference(superposition,[],[f116,f358])).
% 6.48/1.18  fof(f116,plain,(
% 6.48/1.18    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(X0)) | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.48/1.18    inference(cnf_transformation,[],[f51])).
% 6.48/1.18  fof(f51,plain,(
% 6.48/1.18    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.48/1.18    inference(flattening,[],[f50])).
% 6.48/1.18  fof(f50,plain,(
% 6.48/1.18    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.48/1.18    inference(ennf_transformation,[],[f14])).
% 6.48/1.18  fof(f14,axiom,(
% 6.48/1.18    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 6.48/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).
% 6.48/1.18  fof(f1437,plain,(
% 6.48/1.18    spl3_10 | ~spl3_58),
% 6.48/1.18    inference(avatar_contradiction_clause,[],[f1436])).
% 6.48/1.18  fof(f1436,plain,(
% 6.48/1.18    $false | (spl3_10 | ~spl3_58)),
% 6.48/1.18    inference(subsumption_resolution,[],[f1355,f95])).
% 6.48/1.18  fof(f95,plain,(
% 6.48/1.18    v1_xboole_0(k1_xboole_0)),
% 6.48/1.18    inference(cnf_transformation,[],[f1])).
% 6.48/1.18  fof(f1,axiom,(
% 6.48/1.18    v1_xboole_0(k1_xboole_0)),
% 6.48/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 6.48/1.18  fof(f1355,plain,(
% 6.48/1.18    ~v1_xboole_0(k1_xboole_0) | (spl3_10 | ~spl3_58)),
% 6.48/1.18    inference(backward_demodulation,[],[f233,f858])).
% 6.48/1.18  fof(f858,plain,(
% 6.48/1.18    k1_xboole_0 = sK0 | ~spl3_58),
% 6.48/1.18    inference(avatar_component_clause,[],[f856])).
% 6.48/1.18  fof(f233,plain,(
% 6.48/1.18    ~v1_xboole_0(sK0) | spl3_10),
% 6.48/1.18    inference(avatar_component_clause,[],[f231])).
% 6.48/1.18  fof(f1342,plain,(
% 6.48/1.18    ~spl3_24 | spl3_81 | ~spl3_16),
% 6.48/1.18    inference(avatar_split_clause,[],[f1341,f308,f1319,f408])).
% 6.48/1.18  fof(f1341,plain,(
% 6.48/1.18    sK0 != k2_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2)),
% 6.48/1.18    inference(subsumption_resolution,[],[f1340,f89])).
% 6.48/1.18  fof(f1340,plain,(
% 6.48/1.18    sK0 != k2_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 6.48/1.18    inference(subsumption_resolution,[],[f1339,f90])).
% 6.48/1.18  fof(f1339,plain,(
% 6.48/1.18    sK0 != k2_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 6.48/1.18    inference(subsumption_resolution,[],[f419,f91])).
% 6.48/1.18  fof(f419,plain,(
% 6.48/1.18    sK0 != k2_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 6.48/1.18    inference(superposition,[],[f136,f251])).
% 6.48/1.18  fof(f251,plain,(
% 6.48/1.18    k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2)),
% 6.48/1.18    inference(resolution,[],[f91,f131])).
% 6.48/1.18  fof(f131,plain,(
% 6.48/1.18    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 6.48/1.18    inference(cnf_transformation,[],[f65])).
% 6.48/1.18  fof(f65,plain,(
% 6.48/1.18    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.48/1.18    inference(ennf_transformation,[],[f23])).
% 6.48/1.18  fof(f23,axiom,(
% 6.48/1.18    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 6.48/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 6.48/1.18  fof(f136,plain,(
% 6.48/1.18    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.48/1.18    inference(cnf_transformation,[],[f69])).
% 6.48/1.18  fof(f69,plain,(
% 6.48/1.18    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.48/1.18    inference(flattening,[],[f68])).
% 6.48/1.18  fof(f68,plain,(
% 6.48/1.18    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.48/1.18    inference(ennf_transformation,[],[f32])).
% 6.48/1.18  fof(f32,axiom,(
% 6.48/1.18    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 6.48/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 6.48/1.18  fof(f343,plain,(
% 6.48/1.18    ~spl3_1 | spl3_17),
% 6.48/1.18    inference(avatar_contradiction_clause,[],[f342])).
% 6.48/1.18  fof(f342,plain,(
% 6.48/1.18    $false | (~spl3_1 | spl3_17)),
% 6.48/1.18    inference(subsumption_resolution,[],[f341,f165])).
% 6.48/1.18  fof(f341,plain,(
% 6.48/1.18    ~v1_relat_1(sK1) | spl3_17),
% 6.48/1.18    inference(subsumption_resolution,[],[f340,f86])).
% 6.48/1.18  fof(f340,plain,(
% 6.48/1.18    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl3_17),
% 6.48/1.18    inference(resolution,[],[f319,f111])).
% 6.48/1.18  fof(f111,plain,(
% 6.48/1.18    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.48/1.18    inference(cnf_transformation,[],[f45])).
% 6.48/1.18  fof(f45,plain,(
% 6.48/1.18    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.48/1.18    inference(flattening,[],[f44])).
% 6.48/1.18  fof(f44,plain,(
% 6.48/1.18    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.48/1.18    inference(ennf_transformation,[],[f11])).
% 6.48/1.18  fof(f11,axiom,(
% 6.48/1.18    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 6.48/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 6.48/1.18  fof(f319,plain,(
% 6.48/1.18    ~v1_funct_1(k2_funct_1(sK1)) | spl3_17),
% 6.48/1.18    inference(avatar_component_clause,[],[f317])).
% 6.48/1.18  fof(f274,plain,(
% 6.48/1.18    spl3_3),
% 6.48/1.18    inference(avatar_contradiction_clause,[],[f273])).
% 6.48/1.18  fof(f273,plain,(
% 6.48/1.18    $false | spl3_3),
% 6.48/1.18    inference(subsumption_resolution,[],[f272,f119])).
% 6.48/1.18  fof(f119,plain,(
% 6.48/1.18    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 6.48/1.18    inference(cnf_transformation,[],[f6])).
% 6.48/1.18  fof(f6,axiom,(
% 6.48/1.18    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 6.48/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 6.48/1.18  fof(f272,plain,(
% 6.48/1.18    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl3_3),
% 6.48/1.18    inference(subsumption_resolution,[],[f262,f176])).
% 6.48/1.18  fof(f176,plain,(
% 6.48/1.18    ~v1_relat_1(sK2) | spl3_3),
% 6.48/1.18    inference(avatar_component_clause,[],[f174])).
% 6.48/1.18  fof(f262,plain,(
% 6.48/1.18    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 6.48/1.18    inference(resolution,[],[f91,f106])).
% 6.48/1.18  fof(f106,plain,(
% 6.48/1.18    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 6.48/1.18    inference(cnf_transformation,[],[f41])).
% 6.48/1.18  fof(f41,plain,(
% 6.48/1.18    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 6.48/1.18    inference(ennf_transformation,[],[f4])).
% 6.48/1.18  fof(f4,axiom,(
% 6.48/1.18    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 6.48/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 6.48/1.18  fof(f245,plain,(
% 6.48/1.18    spl3_1),
% 6.48/1.18    inference(avatar_contradiction_clause,[],[f244])).
% 6.48/1.18  fof(f244,plain,(
% 6.48/1.18    $false | spl3_1),
% 6.48/1.18    inference(subsumption_resolution,[],[f243,f119])).
% 6.48/1.18  fof(f243,plain,(
% 6.48/1.18    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl3_1),
% 6.48/1.18    inference(subsumption_resolution,[],[f229,f166])).
% 6.48/1.18  fof(f166,plain,(
% 6.48/1.18    ~v1_relat_1(sK1) | spl3_1),
% 6.48/1.18    inference(avatar_component_clause,[],[f164])).
% 6.48/1.18  fof(f229,plain,(
% 6.48/1.18    v1_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 6.48/1.18    inference(resolution,[],[f88,f106])).
% 6.48/1.18  fof(f215,plain,(
% 6.48/1.18    ~spl3_1 | spl3_9),
% 6.48/1.18    inference(avatar_split_clause,[],[f210,f212,f164])).
% 6.48/1.18  fof(f210,plain,(
% 6.48/1.18    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 6.48/1.18    inference(subsumption_resolution,[],[f186,f86])).
% 6.48/1.18  fof(f186,plain,(
% 6.48/1.18    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 6.48/1.18    inference(resolution,[],[f93,f113])).
% 6.48/1.18  fof(f209,plain,(
% 6.48/1.18    ~spl3_1 | spl3_8),
% 6.48/1.18    inference(avatar_split_clause,[],[f204,f206,f164])).
% 6.48/1.18  fof(f204,plain,(
% 6.48/1.18    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 6.48/1.18    inference(subsumption_resolution,[],[f185,f86])).
% 6.48/1.19  % (28910)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 6.48/1.19  fof(f185,plain,(
% 6.48/1.19    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 6.48/1.19    inference(resolution,[],[f93,f112])).
% 6.48/1.19  fof(f191,plain,(
% 6.48/1.19    ~spl3_1 | spl3_5),
% 6.48/1.19    inference(avatar_split_clause,[],[f187,f189,f164])).
% 6.48/1.19  fof(f187,plain,(
% 6.48/1.19    ( ! [X0] : (k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.48/1.19    inference(subsumption_resolution,[],[f182,f86])).
% 6.48/1.19  fof(f182,plain,(
% 6.48/1.19    ( ! [X0] : (k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.48/1.19    inference(resolution,[],[f93,f117])).
% 6.48/1.19  fof(f117,plain,(
% 6.48/1.19    ( ! [X0,X1] : (~v2_funct_1(X1) | k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.48/1.19    inference(cnf_transformation,[],[f53])).
% 6.48/1.19  fof(f53,plain,(
% 6.48/1.19    ! [X0] : (! [X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.48/1.19    inference(flattening,[],[f52])).
% 6.48/1.19  fof(f52,plain,(
% 6.48/1.19    ! [X0] : (! [X1] : ((k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.48/1.19    inference(ennf_transformation,[],[f18])).
% 6.48/1.19  fof(f18,axiom,(
% 6.48/1.19    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 6.48/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).
% 6.48/1.19  fof(f181,plain,(
% 6.48/1.19    ~spl3_3 | spl3_4),
% 6.48/1.19    inference(avatar_split_clause,[],[f172,f178,f174])).
% 6.48/1.19  fof(f172,plain,(
% 6.48/1.19    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 6.48/1.19    inference(resolution,[],[f89,f110])).
% 6.48/1.19  fof(f110,plain,(
% 6.48/1.19    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 6.48/1.19    inference(cnf_transformation,[],[f45])).
% 6.48/1.19  fof(f171,plain,(
% 6.48/1.19    ~spl3_1 | spl3_2),
% 6.48/1.19    inference(avatar_split_clause,[],[f162,f168,f164])).
% 6.48/1.19  fof(f162,plain,(
% 6.48/1.19    v1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 6.48/1.19    inference(resolution,[],[f86,f110])).
% 6.48/1.19  % SZS output end Proof for theBenchmark
% 6.48/1.19  % (28883)------------------------------
% 6.48/1.19  % (28883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.48/1.19  % (28883)Termination reason: Refutation
% 6.48/1.19  
% 6.48/1.19  % (28883)Memory used [KB]: 11769
% 6.48/1.19  % (28883)Time elapsed: 0.233 s
% 6.48/1.19  % (28883)------------------------------
% 6.48/1.19  % (28883)------------------------------
% 6.48/1.19  % (28692)Success in time 0.826 s
%------------------------------------------------------------------------------
