%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 703 expanded)
%              Number of leaves         :   36 ( 228 expanded)
%              Depth                    :   20
%              Number of atoms          :  690 (4742 expanded)
%              Number of equality atoms :   93 ( 167 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f702,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f167,f211,f214,f232,f278,f289,f296,f298,f323,f332,f526,f630,f699])).

fof(f699,plain,
    ( spl4_1
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f698])).

fof(f698,plain,
    ( $false
    | spl4_1
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f693,f614])).

fof(f614,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl4_1
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f113,f607])).

fof(f607,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f604,f283])).

fof(f283,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl4_13
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f604,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(trivial_inequality_removal,[],[f603])).

fof(f603,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(superposition,[],[f84,f575])).

fof(f575,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f318,f162])).

fof(f162,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f318,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl4_15
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f84,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f113,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f693,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(superposition,[],[f98,f683])).

fof(f683,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(resolution,[],[f639,f91])).

fof(f91,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f639,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k6_partfun1(k1_xboole_0) = X0 )
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(resolution,[],[f633,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f633,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f277,f162])).

fof(f277,plain,
    ( v1_xboole_0(k6_partfun1(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl4_12
  <=> v1_xboole_0(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f98,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f70,f74])).

fof(f74,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f70,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f630,plain,
    ( ~ spl4_5
    | spl4_11
    | ~ spl4_13
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f629])).

fof(f629,plain,
    ( $false
    | ~ spl4_5
    | spl4_11
    | ~ spl4_13
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f618,f91])).

fof(f618,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_5
    | spl4_11
    | ~ spl4_13
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f273,f607])).

fof(f273,plain,
    ( ~ v1_xboole_0(sK2)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl4_11
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f526,plain,
    ( spl4_1
    | spl4_5
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f525])).

fof(f525,plain,
    ( $false
    | spl4_1
    | spl4_5
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f524,f98])).

fof(f524,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_1
    | spl4_5
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f523,f231])).

fof(f231,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl4_10
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f523,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | spl4_1
    | spl4_5 ),
    inference(subsumption_resolution,[],[f522,f59])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f50,f49])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f522,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | spl4_1
    | spl4_5 ),
    inference(resolution,[],[f350,f58])).

fof(f58,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f350,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,X1,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
        | ~ v2_funct_1(k1_partfun1(X1,sK1,sK1,sK0,sK2,sK3)) )
    | spl4_1
    | spl4_5 ),
    inference(subsumption_resolution,[],[f349,f60])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f349,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,X1,sK1)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
        | ~ v2_funct_1(k1_partfun1(X1,sK1,sK1,sK0,sK2,sK3)) )
    | spl4_1
    | spl4_5 ),
    inference(subsumption_resolution,[],[f348,f163])).

fof(f163,plain,
    ( k1_xboole_0 != sK0
    | spl4_5 ),
    inference(avatar_component_clause,[],[f161])).

fof(f348,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,X1,sK1)
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
        | ~ v2_funct_1(k1_partfun1(X1,sK1,sK1,sK0,sK2,sK3)) )
    | spl4_1 ),
    inference(subsumption_resolution,[],[f342,f62])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f342,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,X1,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
        | ~ v2_funct_1(k1_partfun1(X1,sK1,sK1,sK0,sK2,sK3)) )
    | spl4_1 ),
    inference(resolution,[],[f121,f61])).

fof(f61,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f121,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(X3,X2,X0)
        | ~ v1_funct_2(sK2,X1,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | k1_xboole_0 = X0
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3)) )
    | spl4_1 ),
    inference(subsumption_resolution,[],[f119,f57])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f119,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_xboole_0 = X0
        | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_2(X3,X2,X0)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_2(sK2,X1,X2)
        | ~ v1_funct_1(sK2) )
    | spl4_1 ),
    inference(resolution,[],[f113,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f332,plain,
    ( ~ spl4_13
    | spl4_16 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl4_13
    | spl4_16 ),
    inference(resolution,[],[f327,f59])).

fof(f327,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ spl4_13
    | spl4_16 ),
    inference(resolution,[],[f325,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f325,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ spl4_13
    | spl4_16 ),
    inference(subsumption_resolution,[],[f324,f283])).

fof(f324,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl4_16 ),
    inference(resolution,[],[f322,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f322,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl4_16
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f323,plain,
    ( spl4_15
    | ~ spl4_16
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f300,f286,f320,f316])).

fof(f286,plain,
    ( spl4_14
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f300,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | sK0 = k1_relat_1(sK2)
    | ~ spl4_14 ),
    inference(resolution,[],[f288,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f288,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f286])).

fof(f298,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl4_13 ),
    inference(resolution,[],[f290,f59])).

fof(f290,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_13 ),
    inference(resolution,[],[f284,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f284,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f282])).

fof(f296,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f294,f57])).

fof(f294,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_9 ),
    inference(subsumption_resolution,[],[f293,f59])).

fof(f293,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_9 ),
    inference(subsumption_resolution,[],[f292,f60])).

fof(f292,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_9 ),
    inference(subsumption_resolution,[],[f291,f62])).

fof(f291,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_9 ),
    inference(resolution,[],[f227,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f227,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl4_9
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f289,plain,
    ( ~ spl4_13
    | spl4_14
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f268,f153,f286,f282])).

fof(f153,plain,
    ( spl4_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f268,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f267,f103])).

fof(f103,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f81,f74])).

fof(f81,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f267,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f264,f154])).

fof(f154,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f153])).

fof(f264,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f90,f260])).

fof(f260,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f257,f259])).

fof(f259,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f258,f100])).

fof(f100,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f79,f74])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f258,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f246,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f246,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f63,f151])).

fof(f151,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f148,f60])).

fof(f148,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f126,f62])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f124,f57])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f59,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f63,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f257,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f256,f57])).

fof(f256,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f255,f59])).

fof(f255,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f254,f60])).

fof(f254,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f249,f62])).

fof(f249,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f76,f151])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f278,plain,
    ( ~ spl4_11
    | spl4_12
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f269,f153,f275,f271])).

fof(f269,plain,
    ( v1_xboole_0(k6_partfun1(sK0))
    | ~ v1_xboole_0(sK2)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f265,f154])).

fof(f265,plain,
    ( v1_xboole_0(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3)
    | ~ v1_xboole_0(sK2) ),
    inference(superposition,[],[f88,f260])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k5_relat_1(X0,X1))
        & v1_xboole_0(k5_relat_1(X0,X1)) )
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k5_relat_1(X0,X1))
        & v1_xboole_0(k5_relat_1(X0,X1)) )
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_xboole_0(X0) )
     => ( v1_relat_1(k5_relat_1(X0,X1))
        & v1_xboole_0(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_relat_1)).

fof(f232,plain,
    ( ~ spl4_9
    | spl4_10 ),
    inference(avatar_split_clause,[],[f135,f229,f225])).

fof(f135,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f133,f100])).

fof(f133,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f63,f71])).

fof(f214,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | spl4_8 ),
    inference(resolution,[],[f212,f62])).

fof(f212,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl4_8 ),
    inference(resolution,[],[f210,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f210,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl4_8
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f211,plain,
    ( ~ spl4_8
    | spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f199,f153,f115,f208])).

fof(f115,plain,
    ( spl4_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f199,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v5_relat_1(sK3,sK0)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f144,f154])).

fof(f144,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f104,f142])).

fof(f142,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f128,f141])).

fof(f141,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f140,f60])).

fof(f140,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f139,f61])).

fof(f139,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f138,f62])).

fof(f138,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f137,f57])).

fof(f137,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f136,f58])).

fof(f136,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f134,f59])).

fof(f134,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f63,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f128,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f62,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f104,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f167,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl4_3 ),
    inference(resolution,[],[f165,f62])).

fof(f165,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_3 ),
    inference(resolution,[],[f155,f78])).

fof(f155,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f153])).

fof(f118,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f64,f115,f111])).

fof(f64,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (5405)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.51  % (5399)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (5391)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (5397)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (5381)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (5389)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (5384)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (5383)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (5382)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (5404)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (5403)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (5385)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (5380)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (5386)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (5377)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (5405)Refutation not found, incomplete strategy% (5405)------------------------------
% 0.20/0.54  % (5405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5405)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5405)Memory used [KB]: 11001
% 0.20/0.54  % (5405)Time elapsed: 0.123 s
% 0.20/0.54  % (5405)------------------------------
% 0.20/0.54  % (5405)------------------------------
% 0.20/0.54  % (5406)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (5395)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (5396)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (5401)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (5402)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (5398)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (5379)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.55  % (5400)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (5378)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.55  % (5387)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (5388)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.56  % (5390)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.56  % (5387)Refutation not found, incomplete strategy% (5387)------------------------------
% 0.20/0.56  % (5387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (5387)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (5387)Memory used [KB]: 11001
% 0.20/0.56  % (5387)Time elapsed: 0.151 s
% 0.20/0.56  % (5387)------------------------------
% 0.20/0.56  % (5387)------------------------------
% 0.20/0.56  % (5394)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.56  % (5393)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.56  % (5393)Refutation not found, incomplete strategy% (5393)------------------------------
% 0.20/0.56  % (5393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (5392)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.57  % (5393)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (5393)Memory used [KB]: 10746
% 0.20/0.57  % (5393)Time elapsed: 0.159 s
% 0.20/0.57  % (5393)------------------------------
% 0.20/0.57  % (5393)------------------------------
% 0.20/0.58  % (5401)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 1.72/0.60  % SZS output start Proof for theBenchmark
% 1.72/0.60  fof(f702,plain,(
% 1.72/0.60    $false),
% 1.72/0.60    inference(avatar_sat_refutation,[],[f118,f167,f211,f214,f232,f278,f289,f296,f298,f323,f332,f526,f630,f699])).
% 1.89/0.60  fof(f699,plain,(
% 1.89/0.60    spl4_1 | ~spl4_5 | ~spl4_12 | ~spl4_13 | ~spl4_15),
% 1.89/0.60    inference(avatar_contradiction_clause,[],[f698])).
% 1.89/0.60  fof(f698,plain,(
% 1.89/0.60    $false | (spl4_1 | ~spl4_5 | ~spl4_12 | ~spl4_13 | ~spl4_15)),
% 1.89/0.60    inference(subsumption_resolution,[],[f693,f614])).
% 1.89/0.60  fof(f614,plain,(
% 1.89/0.60    ~v2_funct_1(k1_xboole_0) | (spl4_1 | ~spl4_5 | ~spl4_13 | ~spl4_15)),
% 1.89/0.60    inference(backward_demodulation,[],[f113,f607])).
% 1.89/0.60  fof(f607,plain,(
% 1.89/0.60    k1_xboole_0 = sK2 | (~spl4_5 | ~spl4_13 | ~spl4_15)),
% 1.89/0.60    inference(subsumption_resolution,[],[f604,f283])).
% 1.89/0.60  fof(f283,plain,(
% 1.89/0.60    v1_relat_1(sK2) | ~spl4_13),
% 1.89/0.60    inference(avatar_component_clause,[],[f282])).
% 1.89/0.60  fof(f282,plain,(
% 1.89/0.60    spl4_13 <=> v1_relat_1(sK2)),
% 1.89/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.89/0.60  fof(f604,plain,(
% 1.89/0.60    k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | (~spl4_5 | ~spl4_15)),
% 1.89/0.60    inference(trivial_inequality_removal,[],[f603])).
% 1.89/0.60  fof(f603,plain,(
% 1.89/0.60    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | (~spl4_5 | ~spl4_15)),
% 1.89/0.60    inference(superposition,[],[f84,f575])).
% 1.89/0.60  fof(f575,plain,(
% 1.89/0.60    k1_xboole_0 = k1_relat_1(sK2) | (~spl4_5 | ~spl4_15)),
% 1.89/0.60    inference(backward_demodulation,[],[f318,f162])).
% 1.89/0.60  fof(f162,plain,(
% 1.89/0.60    k1_xboole_0 = sK0 | ~spl4_5),
% 1.89/0.60    inference(avatar_component_clause,[],[f161])).
% 1.89/0.60  fof(f161,plain,(
% 1.89/0.60    spl4_5 <=> k1_xboole_0 = sK0),
% 1.89/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.89/0.60  fof(f318,plain,(
% 1.89/0.60    sK0 = k1_relat_1(sK2) | ~spl4_15),
% 1.89/0.60    inference(avatar_component_clause,[],[f316])).
% 1.89/0.60  fof(f316,plain,(
% 1.89/0.60    spl4_15 <=> sK0 = k1_relat_1(sK2)),
% 1.89/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.89/0.60  fof(f84,plain,(
% 1.89/0.60    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.89/0.60    inference(cnf_transformation,[],[f42])).
% 1.89/0.60  fof(f42,plain,(
% 1.89/0.60    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.89/0.60    inference(flattening,[],[f41])).
% 1.89/0.60  fof(f41,plain,(
% 1.89/0.60    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.89/0.60    inference(ennf_transformation,[],[f7])).
% 1.89/0.60  fof(f7,axiom,(
% 1.89/0.60    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.89/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.89/0.60  fof(f113,plain,(
% 1.89/0.60    ~v2_funct_1(sK2) | spl4_1),
% 1.89/0.60    inference(avatar_component_clause,[],[f111])).
% 1.89/0.60  fof(f111,plain,(
% 1.89/0.60    spl4_1 <=> v2_funct_1(sK2)),
% 1.89/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.89/0.60  fof(f693,plain,(
% 1.89/0.60    v2_funct_1(k1_xboole_0) | (~spl4_5 | ~spl4_12)),
% 1.89/0.60    inference(superposition,[],[f98,f683])).
% 1.89/0.60  fof(f683,plain,(
% 1.89/0.60    k1_xboole_0 = k6_partfun1(k1_xboole_0) | (~spl4_5 | ~spl4_12)),
% 1.89/0.60    inference(resolution,[],[f639,f91])).
% 1.89/0.60  fof(f91,plain,(
% 1.89/0.60    v1_xboole_0(k1_xboole_0)),
% 1.89/0.60    inference(cnf_transformation,[],[f1])).
% 1.89/0.60  fof(f1,axiom,(
% 1.89/0.60    v1_xboole_0(k1_xboole_0)),
% 1.89/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.89/0.60  fof(f639,plain,(
% 1.89/0.60    ( ! [X0] : (~v1_xboole_0(X0) | k6_partfun1(k1_xboole_0) = X0) ) | (~spl4_5 | ~spl4_12)),
% 1.89/0.60    inference(resolution,[],[f633,f94])).
% 1.89/0.60  fof(f94,plain,(
% 1.89/0.60    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~v1_xboole_0(X0) | X0 = X1) )),
% 1.89/0.60    inference(cnf_transformation,[],[f48])).
% 1.89/0.60  fof(f48,plain,(
% 1.89/0.60    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.89/0.60    inference(ennf_transformation,[],[f3])).
% 1.89/0.60  fof(f3,axiom,(
% 1.89/0.60    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.89/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.89/0.60  fof(f633,plain,(
% 1.89/0.60    v1_xboole_0(k6_partfun1(k1_xboole_0)) | (~spl4_5 | ~spl4_12)),
% 1.89/0.60    inference(forward_demodulation,[],[f277,f162])).
% 1.89/0.60  fof(f277,plain,(
% 1.89/0.60    v1_xboole_0(k6_partfun1(sK0)) | ~spl4_12),
% 1.89/0.60    inference(avatar_component_clause,[],[f275])).
% 1.89/0.60  fof(f275,plain,(
% 1.89/0.60    spl4_12 <=> v1_xboole_0(k6_partfun1(sK0))),
% 1.89/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.89/0.60  fof(f98,plain,(
% 1.89/0.60    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.89/0.60    inference(definition_unfolding,[],[f70,f74])).
% 1.89/0.60  fof(f74,plain,(
% 1.89/0.60    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.89/0.60    inference(cnf_transformation,[],[f19])).
% 1.89/0.60  fof(f19,axiom,(
% 1.89/0.60    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.89/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.89/0.60  fof(f70,plain,(
% 1.89/0.60    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.89/0.60    inference(cnf_transformation,[],[f10])).
% 1.89/0.60  fof(f10,axiom,(
% 1.89/0.60    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.89/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.89/0.60  fof(f630,plain,(
% 1.89/0.60    ~spl4_5 | spl4_11 | ~spl4_13 | ~spl4_15),
% 1.89/0.60    inference(avatar_contradiction_clause,[],[f629])).
% 1.89/0.60  fof(f629,plain,(
% 1.89/0.60    $false | (~spl4_5 | spl4_11 | ~spl4_13 | ~spl4_15)),
% 1.89/0.60    inference(subsumption_resolution,[],[f618,f91])).
% 1.89/0.60  fof(f618,plain,(
% 1.89/0.60    ~v1_xboole_0(k1_xboole_0) | (~spl4_5 | spl4_11 | ~spl4_13 | ~spl4_15)),
% 1.89/0.60    inference(backward_demodulation,[],[f273,f607])).
% 1.89/0.60  fof(f273,plain,(
% 1.89/0.60    ~v1_xboole_0(sK2) | spl4_11),
% 1.89/0.60    inference(avatar_component_clause,[],[f271])).
% 1.89/0.60  fof(f271,plain,(
% 1.89/0.60    spl4_11 <=> v1_xboole_0(sK2)),
% 1.89/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.89/0.60  fof(f526,plain,(
% 1.89/0.60    spl4_1 | spl4_5 | ~spl4_10),
% 1.89/0.60    inference(avatar_contradiction_clause,[],[f525])).
% 1.89/0.60  fof(f525,plain,(
% 1.89/0.60    $false | (spl4_1 | spl4_5 | ~spl4_10)),
% 1.89/0.60    inference(subsumption_resolution,[],[f524,f98])).
% 1.89/0.60  fof(f524,plain,(
% 1.89/0.60    ~v2_funct_1(k6_partfun1(sK0)) | (spl4_1 | spl4_5 | ~spl4_10)),
% 1.89/0.60    inference(forward_demodulation,[],[f523,f231])).
% 1.89/0.60  fof(f231,plain,(
% 1.89/0.60    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl4_10),
% 1.89/0.60    inference(avatar_component_clause,[],[f229])).
% 1.89/0.60  fof(f229,plain,(
% 1.89/0.60    spl4_10 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.89/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.89/0.60  fof(f523,plain,(
% 1.89/0.60    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | (spl4_1 | spl4_5)),
% 1.89/0.60    inference(subsumption_resolution,[],[f522,f59])).
% 1.89/0.60  fof(f59,plain,(
% 1.89/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.89/0.60    inference(cnf_transformation,[],[f51])).
% 1.89/0.60  fof(f51,plain,(
% 1.89/0.60    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.89/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f50,f49])).
% 1.89/0.60  fof(f49,plain,(
% 1.89/0.60    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.89/0.60    introduced(choice_axiom,[])).
% 1.89/0.60  fof(f50,plain,(
% 1.89/0.60    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.89/0.60    introduced(choice_axiom,[])).
% 1.89/0.60  fof(f25,plain,(
% 1.89/0.60    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.89/0.60    inference(flattening,[],[f24])).
% 1.89/0.60  fof(f24,plain,(
% 1.89/0.60    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.89/0.60    inference(ennf_transformation,[],[f23])).
% 1.89/0.60  fof(f23,negated_conjecture,(
% 1.89/0.60    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.89/0.60    inference(negated_conjecture,[],[f22])).
% 1.89/0.60  fof(f22,conjecture,(
% 1.89/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.89/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.89/0.60  fof(f522,plain,(
% 1.89/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | (spl4_1 | spl4_5)),
% 1.89/0.60    inference(resolution,[],[f350,f58])).
% 1.89/0.60  fof(f58,plain,(
% 1.89/0.60    v1_funct_2(sK2,sK0,sK1)),
% 1.89/0.60    inference(cnf_transformation,[],[f51])).
% 1.89/0.60  fof(f350,plain,(
% 1.89/0.60    ( ! [X1] : (~v1_funct_2(sK2,X1,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v2_funct_1(k1_partfun1(X1,sK1,sK1,sK0,sK2,sK3))) ) | (spl4_1 | spl4_5)),
% 1.89/0.60    inference(subsumption_resolution,[],[f349,f60])).
% 1.89/0.60  fof(f60,plain,(
% 1.89/0.60    v1_funct_1(sK3)),
% 1.89/0.60    inference(cnf_transformation,[],[f51])).
% 1.89/0.60  fof(f349,plain,(
% 1.89/0.60    ( ! [X1] : (~v1_funct_2(sK2,X1,sK1) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v2_funct_1(k1_partfun1(X1,sK1,sK1,sK0,sK2,sK3))) ) | (spl4_1 | spl4_5)),
% 1.89/0.60    inference(subsumption_resolution,[],[f348,f163])).
% 1.89/0.60  fof(f163,plain,(
% 1.89/0.60    k1_xboole_0 != sK0 | spl4_5),
% 1.89/0.60    inference(avatar_component_clause,[],[f161])).
% 1.89/0.61  fof(f348,plain,(
% 1.89/0.61    ( ! [X1] : (~v1_funct_2(sK2,X1,sK1) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v2_funct_1(k1_partfun1(X1,sK1,sK1,sK0,sK2,sK3))) ) | spl4_1),
% 1.89/0.61    inference(subsumption_resolution,[],[f342,f62])).
% 1.89/0.61  fof(f62,plain,(
% 1.89/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.89/0.61    inference(cnf_transformation,[],[f51])).
% 1.89/0.61  fof(f342,plain,(
% 1.89/0.61    ( ! [X1] : (~v1_funct_2(sK2,X1,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v2_funct_1(k1_partfun1(X1,sK1,sK1,sK0,sK2,sK3))) ) | spl4_1),
% 1.89/0.61    inference(resolution,[],[f121,f61])).
% 1.89/0.61  fof(f61,plain,(
% 1.89/0.61    v1_funct_2(sK3,sK1,sK0)),
% 1.89/0.61    inference(cnf_transformation,[],[f51])).
% 1.89/0.61  fof(f121,plain,(
% 1.89/0.61    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X2,X0) | ~v1_funct_2(sK2,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0 | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3))) ) | spl4_1),
% 1.89/0.61    inference(subsumption_resolution,[],[f119,f57])).
% 1.89/0.61  fof(f57,plain,(
% 1.89/0.61    v1_funct_1(sK2)),
% 1.89/0.61    inference(cnf_transformation,[],[f51])).
% 1.89/0.61  fof(f119,plain,(
% 1.89/0.61    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X3,X2,X0) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(sK2,X1,X2) | ~v1_funct_1(sK2)) ) | spl4_1),
% 1.89/0.61    inference(resolution,[],[f113,f67])).
% 1.89/0.61  fof(f67,plain,(
% 1.89/0.61    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f29])).
% 1.89/0.61  fof(f29,plain,(
% 1.89/0.61    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.89/0.61    inference(flattening,[],[f28])).
% 1.89/0.61  fof(f28,plain,(
% 1.89/0.61    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.89/0.61    inference(ennf_transformation,[],[f21])).
% 1.89/0.61  fof(f21,axiom,(
% 1.89/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 1.89/0.61  fof(f332,plain,(
% 1.89/0.61    ~spl4_13 | spl4_16),
% 1.89/0.61    inference(avatar_contradiction_clause,[],[f331])).
% 1.89/0.61  fof(f331,plain,(
% 1.89/0.61    $false | (~spl4_13 | spl4_16)),
% 1.89/0.61    inference(resolution,[],[f327,f59])).
% 1.89/0.61  fof(f327,plain,(
% 1.89/0.61    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | (~spl4_13 | spl4_16)),
% 1.89/0.61    inference(resolution,[],[f325,f86])).
% 1.89/0.61  fof(f86,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f43])).
% 1.89/0.61  fof(f43,plain,(
% 1.89/0.61    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.89/0.61    inference(ennf_transformation,[],[f12])).
% 1.89/0.61  fof(f12,axiom,(
% 1.89/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.89/0.61  fof(f325,plain,(
% 1.89/0.61    ~v4_relat_1(sK2,sK0) | (~spl4_13 | spl4_16)),
% 1.89/0.61    inference(subsumption_resolution,[],[f324,f283])).
% 1.89/0.61  fof(f324,plain,(
% 1.89/0.61    ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl4_16),
% 1.89/0.61    inference(resolution,[],[f322,f92])).
% 1.89/0.61  fof(f92,plain,(
% 1.89/0.61    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f54])).
% 1.89/0.61  fof(f54,plain,(
% 1.89/0.61    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.89/0.61    inference(nnf_transformation,[],[f47])).
% 1.89/0.61  fof(f47,plain,(
% 1.89/0.61    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.89/0.61    inference(ennf_transformation,[],[f4])).
% 1.89/0.61  fof(f4,axiom,(
% 1.89/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.89/0.61  fof(f322,plain,(
% 1.89/0.61    ~r1_tarski(k1_relat_1(sK2),sK0) | spl4_16),
% 1.89/0.61    inference(avatar_component_clause,[],[f320])).
% 1.89/0.61  fof(f320,plain,(
% 1.89/0.61    spl4_16 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.89/0.61  fof(f323,plain,(
% 1.89/0.61    spl4_15 | ~spl4_16 | ~spl4_14),
% 1.89/0.61    inference(avatar_split_clause,[],[f300,f286,f320,f316])).
% 1.89/0.61  fof(f286,plain,(
% 1.89/0.61    spl4_14 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.89/0.61  fof(f300,plain,(
% 1.89/0.61    ~r1_tarski(k1_relat_1(sK2),sK0) | sK0 = k1_relat_1(sK2) | ~spl4_14),
% 1.89/0.61    inference(resolution,[],[f288,f97])).
% 1.89/0.61  fof(f97,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.89/0.61    inference(cnf_transformation,[],[f56])).
% 1.89/0.61  fof(f56,plain,(
% 1.89/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.89/0.61    inference(flattening,[],[f55])).
% 1.89/0.61  fof(f55,plain,(
% 1.89/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.89/0.61    inference(nnf_transformation,[],[f2])).
% 1.89/0.61  fof(f2,axiom,(
% 1.89/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.89/0.61  fof(f288,plain,(
% 1.89/0.61    r1_tarski(sK0,k1_relat_1(sK2)) | ~spl4_14),
% 1.89/0.61    inference(avatar_component_clause,[],[f286])).
% 1.89/0.61  fof(f298,plain,(
% 1.89/0.61    spl4_13),
% 1.89/0.61    inference(avatar_contradiction_clause,[],[f297])).
% 1.89/0.61  fof(f297,plain,(
% 1.89/0.61    $false | spl4_13),
% 1.89/0.61    inference(resolution,[],[f290,f59])).
% 1.89/0.61  fof(f290,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_13),
% 1.89/0.61    inference(resolution,[],[f284,f78])).
% 1.89/0.61  fof(f78,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f38])).
% 1.89/0.61  fof(f38,plain,(
% 1.89/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.89/0.61    inference(ennf_transformation,[],[f11])).
% 1.89/0.61  fof(f11,axiom,(
% 1.89/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.89/0.61  fof(f284,plain,(
% 1.89/0.61    ~v1_relat_1(sK2) | spl4_13),
% 1.89/0.61    inference(avatar_component_clause,[],[f282])).
% 1.89/0.61  fof(f296,plain,(
% 1.89/0.61    spl4_9),
% 1.89/0.61    inference(avatar_contradiction_clause,[],[f295])).
% 1.89/0.61  fof(f295,plain,(
% 1.89/0.61    $false | spl4_9),
% 1.89/0.61    inference(subsumption_resolution,[],[f294,f57])).
% 1.89/0.61  fof(f294,plain,(
% 1.89/0.61    ~v1_funct_1(sK2) | spl4_9),
% 1.89/0.61    inference(subsumption_resolution,[],[f293,f59])).
% 1.89/0.61  fof(f293,plain,(
% 1.89/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_9),
% 1.89/0.61    inference(subsumption_resolution,[],[f292,f60])).
% 1.89/0.61  fof(f292,plain,(
% 1.89/0.61    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_9),
% 1.89/0.61    inference(subsumption_resolution,[],[f291,f62])).
% 1.89/0.61  fof(f291,plain,(
% 1.89/0.61    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_9),
% 1.89/0.61    inference(resolution,[],[f227,f76])).
% 1.89/0.61  fof(f76,plain,(
% 1.89/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f35])).
% 1.89/0.61  fof(f35,plain,(
% 1.89/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.89/0.61    inference(flattening,[],[f34])).
% 1.89/0.61  fof(f34,plain,(
% 1.89/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.89/0.61    inference(ennf_transformation,[],[f17])).
% 1.89/0.61  fof(f17,axiom,(
% 1.89/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.89/0.61  fof(f227,plain,(
% 1.89/0.61    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_9),
% 1.89/0.61    inference(avatar_component_clause,[],[f225])).
% 1.89/0.61  fof(f225,plain,(
% 1.89/0.61    spl4_9 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.89/0.61  fof(f289,plain,(
% 1.89/0.61    ~spl4_13 | spl4_14 | ~spl4_3),
% 1.89/0.61    inference(avatar_split_clause,[],[f268,f153,f286,f282])).
% 1.89/0.61  fof(f153,plain,(
% 1.89/0.61    spl4_3 <=> v1_relat_1(sK3)),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.89/0.61  fof(f268,plain,(
% 1.89/0.61    r1_tarski(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_3),
% 1.89/0.61    inference(forward_demodulation,[],[f267,f103])).
% 1.89/0.61  fof(f103,plain,(
% 1.89/0.61    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.89/0.61    inference(definition_unfolding,[],[f81,f74])).
% 1.89/0.61  fof(f81,plain,(
% 1.89/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.89/0.61    inference(cnf_transformation,[],[f8])).
% 1.89/0.61  fof(f8,axiom,(
% 1.89/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.89/0.61  fof(f267,plain,(
% 1.89/0.61    r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_3),
% 1.89/0.61    inference(subsumption_resolution,[],[f264,f154])).
% 1.89/0.61  fof(f154,plain,(
% 1.89/0.61    v1_relat_1(sK3) | ~spl4_3),
% 1.89/0.61    inference(avatar_component_clause,[],[f153])).
% 1.89/0.61  fof(f264,plain,(
% 1.89/0.61    r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2)),
% 1.89/0.61    inference(superposition,[],[f90,f260])).
% 1.89/0.61  fof(f260,plain,(
% 1.89/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.89/0.61    inference(global_subsumption,[],[f257,f259])).
% 1.89/0.61  fof(f259,plain,(
% 1.89/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.89/0.61    inference(subsumption_resolution,[],[f258,f100])).
% 1.89/0.61  fof(f100,plain,(
% 1.89/0.61    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.89/0.61    inference(definition_unfolding,[],[f79,f74])).
% 1.89/0.61  fof(f79,plain,(
% 1.89/0.61    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f15])).
% 1.89/0.61  fof(f15,axiom,(
% 1.89/0.61    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.89/0.61  fof(f258,plain,(
% 1.89/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.89/0.61    inference(resolution,[],[f246,f71])).
% 1.89/0.61  fof(f71,plain,(
% 1.89/0.61    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f53])).
% 1.89/0.61  fof(f53,plain,(
% 1.89/0.61    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.89/0.61    inference(nnf_transformation,[],[f31])).
% 1.89/0.61  fof(f31,plain,(
% 1.89/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.89/0.61    inference(flattening,[],[f30])).
% 1.89/0.61  fof(f30,plain,(
% 1.89/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.89/0.61    inference(ennf_transformation,[],[f14])).
% 1.89/0.61  fof(f14,axiom,(
% 1.89/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.89/0.61  fof(f246,plain,(
% 1.89/0.61    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.89/0.61    inference(backward_demodulation,[],[f63,f151])).
% 1.89/0.61  fof(f151,plain,(
% 1.89/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.89/0.61    inference(subsumption_resolution,[],[f148,f60])).
% 1.89/0.61  fof(f148,plain,(
% 1.89/0.61    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.89/0.61    inference(resolution,[],[f126,f62])).
% 1.89/0.61  fof(f126,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)) )),
% 1.89/0.61    inference(subsumption_resolution,[],[f124,f57])).
% 1.89/0.61  fof(f124,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) | ~v1_funct_1(sK2)) )),
% 1.89/0.61    inference(resolution,[],[f59,f77])).
% 1.89/0.61  fof(f77,plain,(
% 1.89/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f37])).
% 1.89/0.61  fof(f37,plain,(
% 1.89/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.89/0.61    inference(flattening,[],[f36])).
% 1.89/0.61  fof(f36,plain,(
% 1.89/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.89/0.61    inference(ennf_transformation,[],[f18])).
% 1.89/0.61  fof(f18,axiom,(
% 1.89/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.89/0.61  fof(f63,plain,(
% 1.89/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.89/0.61    inference(cnf_transformation,[],[f51])).
% 1.89/0.61  fof(f257,plain,(
% 1.89/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.89/0.61    inference(subsumption_resolution,[],[f256,f57])).
% 1.89/0.61  fof(f256,plain,(
% 1.89/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.89/0.61    inference(subsumption_resolution,[],[f255,f59])).
% 1.89/0.61  fof(f255,plain,(
% 1.89/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.89/0.61    inference(subsumption_resolution,[],[f254,f60])).
% 1.89/0.61  fof(f254,plain,(
% 1.89/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.89/0.61    inference(subsumption_resolution,[],[f249,f62])).
% 1.89/0.61  fof(f249,plain,(
% 1.89/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.89/0.61    inference(superposition,[],[f76,f151])).
% 1.89/0.61  fof(f90,plain,(
% 1.89/0.61    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f46])).
% 1.89/0.61  fof(f46,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.89/0.61    inference(ennf_transformation,[],[f6])).
% 1.89/0.61  fof(f6,axiom,(
% 1.89/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 1.89/0.61  fof(f278,plain,(
% 1.89/0.61    ~spl4_11 | spl4_12 | ~spl4_3),
% 1.89/0.61    inference(avatar_split_clause,[],[f269,f153,f275,f271])).
% 1.89/0.61  fof(f269,plain,(
% 1.89/0.61    v1_xboole_0(k6_partfun1(sK0)) | ~v1_xboole_0(sK2) | ~spl4_3),
% 1.89/0.61    inference(subsumption_resolution,[],[f265,f154])).
% 1.89/0.61  fof(f265,plain,(
% 1.89/0.61    v1_xboole_0(k6_partfun1(sK0)) | ~v1_relat_1(sK3) | ~v1_xboole_0(sK2)),
% 1.89/0.61    inference(superposition,[],[f88,f260])).
% 1.89/0.61  fof(f88,plain,(
% 1.89/0.61    ( ! [X0,X1] : (v1_xboole_0(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_xboole_0(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f45])).
% 1.89/0.61  fof(f45,plain,(
% 1.89/0.61    ! [X0,X1] : ((v1_relat_1(k5_relat_1(X0,X1)) & v1_xboole_0(k5_relat_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_xboole_0(X0))),
% 1.89/0.61    inference(flattening,[],[f44])).
% 1.89/0.61  fof(f44,plain,(
% 1.89/0.61    ! [X0,X1] : ((v1_relat_1(k5_relat_1(X0,X1)) & v1_xboole_0(k5_relat_1(X0,X1))) | (~v1_relat_1(X1) | ~v1_xboole_0(X0)))),
% 1.89/0.61    inference(ennf_transformation,[],[f5])).
% 1.89/0.61  fof(f5,axiom,(
% 1.89/0.61    ! [X0,X1] : ((v1_relat_1(X1) & v1_xboole_0(X0)) => (v1_relat_1(k5_relat_1(X0,X1)) & v1_xboole_0(k5_relat_1(X0,X1))))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_relat_1)).
% 1.89/0.61  fof(f232,plain,(
% 1.89/0.61    ~spl4_9 | spl4_10),
% 1.89/0.61    inference(avatar_split_clause,[],[f135,f229,f225])).
% 1.89/0.61  fof(f135,plain,(
% 1.89/0.61    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.89/0.61    inference(subsumption_resolution,[],[f133,f100])).
% 1.89/0.61  fof(f133,plain,(
% 1.89/0.61    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.89/0.61    inference(resolution,[],[f63,f71])).
% 1.89/0.61  fof(f214,plain,(
% 1.89/0.61    spl4_8),
% 1.89/0.61    inference(avatar_contradiction_clause,[],[f213])).
% 1.89/0.61  fof(f213,plain,(
% 1.89/0.61    $false | spl4_8),
% 1.89/0.61    inference(resolution,[],[f212,f62])).
% 1.89/0.61  fof(f212,plain,(
% 1.89/0.61    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | spl4_8),
% 1.89/0.61    inference(resolution,[],[f210,f87])).
% 1.89/0.61  fof(f87,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f43])).
% 1.89/0.61  fof(f210,plain,(
% 1.89/0.61    ~v5_relat_1(sK3,sK0) | spl4_8),
% 1.89/0.61    inference(avatar_component_clause,[],[f208])).
% 1.89/0.61  fof(f208,plain,(
% 1.89/0.61    spl4_8 <=> v5_relat_1(sK3,sK0)),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.89/0.61  fof(f211,plain,(
% 1.89/0.61    ~spl4_8 | spl4_2 | ~spl4_3),
% 1.89/0.61    inference(avatar_split_clause,[],[f199,f153,f115,f208])).
% 1.89/0.61  fof(f115,plain,(
% 1.89/0.61    spl4_2 <=> v2_funct_2(sK3,sK0)),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.89/0.61  fof(f199,plain,(
% 1.89/0.61    v2_funct_2(sK3,sK0) | ~v5_relat_1(sK3,sK0) | ~spl4_3),
% 1.89/0.61    inference(subsumption_resolution,[],[f144,f154])).
% 1.89/0.61  fof(f144,plain,(
% 1.89/0.61    v2_funct_2(sK3,sK0) | ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3)),
% 1.89/0.61    inference(superposition,[],[f104,f142])).
% 1.89/0.61  fof(f142,plain,(
% 1.89/0.61    sK0 = k2_relat_1(sK3)),
% 1.89/0.61    inference(forward_demodulation,[],[f128,f141])).
% 1.89/0.61  fof(f141,plain,(
% 1.89/0.61    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.89/0.61    inference(subsumption_resolution,[],[f140,f60])).
% 1.89/0.61  fof(f140,plain,(
% 1.89/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.89/0.61    inference(subsumption_resolution,[],[f139,f61])).
% 1.89/0.61  fof(f139,plain,(
% 1.89/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.89/0.61    inference(subsumption_resolution,[],[f138,f62])).
% 1.89/0.61  fof(f138,plain,(
% 1.89/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.89/0.61    inference(subsumption_resolution,[],[f137,f57])).
% 1.89/0.61  fof(f137,plain,(
% 1.89/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.89/0.61    inference(subsumption_resolution,[],[f136,f58])).
% 1.89/0.61  fof(f136,plain,(
% 1.89/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.89/0.61    inference(subsumption_resolution,[],[f134,f59])).
% 1.89/0.61  fof(f134,plain,(
% 1.89/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.89/0.61    inference(resolution,[],[f63,f73])).
% 1.89/0.61  fof(f73,plain,(
% 1.89/0.61    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f33])).
% 1.89/0.61  fof(f33,plain,(
% 1.89/0.61    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.89/0.61    inference(flattening,[],[f32])).
% 1.89/0.61  fof(f32,plain,(
% 1.89/0.61    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.89/0.61    inference(ennf_transformation,[],[f20])).
% 1.89/0.61  fof(f20,axiom,(
% 1.89/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.89/0.61  fof(f128,plain,(
% 1.89/0.61    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 1.89/0.61    inference(resolution,[],[f62,f83])).
% 1.89/0.61  fof(f83,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f40])).
% 1.89/0.61  fof(f40,plain,(
% 1.89/0.61    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.89/0.61    inference(ennf_transformation,[],[f13])).
% 1.89/0.61  fof(f13,axiom,(
% 1.89/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.89/0.61  fof(f104,plain,(
% 1.89/0.61    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.89/0.61    inference(equality_resolution,[],[f66])).
% 1.89/0.61  fof(f66,plain,(
% 1.89/0.61    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f52])).
% 1.89/0.61  fof(f52,plain,(
% 1.89/0.61    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.89/0.61    inference(nnf_transformation,[],[f27])).
% 1.89/0.61  fof(f27,plain,(
% 1.89/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.89/0.61    inference(flattening,[],[f26])).
% 1.89/0.61  fof(f26,plain,(
% 1.89/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.89/0.61    inference(ennf_transformation,[],[f16])).
% 1.89/0.61  fof(f16,axiom,(
% 1.89/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.89/0.61  fof(f167,plain,(
% 1.89/0.61    spl4_3),
% 1.89/0.61    inference(avatar_contradiction_clause,[],[f166])).
% 1.89/0.61  fof(f166,plain,(
% 1.89/0.61    $false | spl4_3),
% 1.89/0.61    inference(resolution,[],[f165,f62])).
% 1.89/0.61  fof(f165,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_3),
% 1.89/0.61    inference(resolution,[],[f155,f78])).
% 1.89/0.61  fof(f155,plain,(
% 1.89/0.61    ~v1_relat_1(sK3) | spl4_3),
% 1.89/0.61    inference(avatar_component_clause,[],[f153])).
% 1.89/0.61  fof(f118,plain,(
% 1.89/0.61    ~spl4_1 | ~spl4_2),
% 1.89/0.61    inference(avatar_split_clause,[],[f64,f115,f111])).
% 1.89/0.61  fof(f64,plain,(
% 1.89/0.61    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.89/0.61    inference(cnf_transformation,[],[f51])).
% 1.89/0.61  % SZS output end Proof for theBenchmark
% 1.89/0.61  % (5401)------------------------------
% 1.89/0.61  % (5401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.61  % (5401)Termination reason: Refutation
% 1.89/0.61  
% 1.89/0.61  % (5401)Memory used [KB]: 11001
% 1.89/0.61  % (5401)Time elapsed: 0.180 s
% 1.89/0.61  % (5401)------------------------------
% 1.89/0.61  % (5401)------------------------------
% 1.89/0.61  % (5375)Success in time 0.25 s
%------------------------------------------------------------------------------
