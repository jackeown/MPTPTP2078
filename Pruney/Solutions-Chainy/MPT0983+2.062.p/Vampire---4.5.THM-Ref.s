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
% DateTime   : Thu Dec  3 13:01:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  212 ( 709 expanded)
%              Number of leaves         :   37 ( 221 expanded)
%              Depth                    :   22
%              Number of atoms          :  738 (4221 expanded)
%              Number of equality atoms :  122 ( 289 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f842,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f143,f167,f169,f300,f415,f603,f610,f629,f745,f841])).

fof(f841,plain,
    ( spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_14
    | ~ spl9_15 ),
    inference(avatar_contradiction_clause,[],[f840])).

fof(f840,plain,
    ( $false
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_14
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f834,f218])).

fof(f218,plain,(
    sP0(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f216,f75])).

fof(f75,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f216,plain,
    ( sP0(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f156,f203])).

fof(f203,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(equality_resolution,[],[f178])).

fof(f178,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_partfun1(X0) ) ),
    inference(global_subsumption,[],[f165,f175])).

fof(f175,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_partfun1(X0)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f82,f117])).

fof(f117,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f80,f77])).

fof(f77,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f80,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f165,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(resolution,[],[f103,f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f156,plain,(
    ! [X0] :
      ( sP0(k6_partfun1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f154,f117])).

fof(f154,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(resolution,[],[f87,f92])).

fof(f92,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK8(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f59,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f87,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK6(X0) != sK7(X0)
          & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))
          & r2_hidden(sK7(X0),k1_relat_1(X0))
          & r2_hidden(sK6(X0),k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f55,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK6(X0) != sK7(X0)
        & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))
        & r2_hidden(sK7(X0),k1_relat_1(X0))
        & r2_hidden(sK6(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          | ~ r2_hidden(X2,k1_relat_1(X0))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f834,plain,
    ( ~ sP0(k1_xboole_0)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_14
    | ~ spl9_15 ),
    inference(backward_demodulation,[],[f172,f802])).

fof(f802,plain,
    ( k1_xboole_0 = sK4
    | ~ spl9_3
    | ~ spl9_14
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f799,f137])).

fof(f137,plain,
    ( v1_relat_1(sK4)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl9_3
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f799,plain,
    ( ~ v1_relat_1(sK4)
    | k1_xboole_0 = sK4
    | ~ spl9_14
    | ~ spl9_15 ),
    inference(resolution,[],[f719,f517])).

fof(f517,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = X0 )
    | ~ spl9_14 ),
    inference(duplicate_literal_removal,[],[f514])).

fof(f514,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_relat_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl9_14 ),
    inference(resolution,[],[f513,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f513,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_relat_1(X2),k1_xboole_0)
        | k1_xboole_0 = X2
        | ~ v1_relat_1(X2) )
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f221,f386])).

fof(f386,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl9_14 ),
    inference(resolution,[],[f385,f273])).

fof(f273,plain,(
    ! [X1] :
      ( ~ v4_relat_1(k1_xboole_0,X1)
      | r1_tarski(k1_xboole_0,X1) ) ),
    inference(subsumption_resolution,[],[f267,f217])).

fof(f217,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f165,f203])).

fof(f267,plain,(
    ! [X1] :
      ( r1_tarski(k1_xboole_0,X1)
      | ~ v4_relat_1(k1_xboole_0,X1)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f94,f215])).

fof(f215,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f117,f203])).

fof(f385,plain,
    ( ! [X0] : v4_relat_1(k1_xboole_0,X0)
    | ~ spl9_14 ),
    inference(resolution,[],[f377,f312])).

fof(f312,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_14 ),
    inference(backward_demodulation,[],[f212,f303])).

fof(f303,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl9_14 ),
    inference(resolution,[],[f293,f161])).

fof(f161,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f102,f75])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f293,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl9_14
  <=> v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f212,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f79,f203])).

fof(f377,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X6,X5) ) ),
    inference(superposition,[],[f105,f371])).

fof(f371,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f200,f75])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(resolution,[],[f161,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f221,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | k1_xboole_0 = X2
      | ~ v1_relat_1(X2) ) ),
    inference(extensionality_resolution,[],[f101,f82])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f719,plain,
    ( v4_relat_1(sK4,k1_xboole_0)
    | ~ spl9_15 ),
    inference(backward_demodulation,[],[f230,f664])).

fof(f664,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_15 ),
    inference(forward_demodulation,[],[f656,f214])).

fof(f214,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f116,f203])).

fof(f116,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f81,f77])).

fof(f81,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f656,plain,
    ( sK2 = k2_relat_1(k1_xboole_0)
    | ~ spl9_15 ),
    inference(backward_demodulation,[],[f401,f410])).

fof(f410,plain,
    ( k1_xboole_0 = sK5
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f408])).

fof(f408,plain,
    ( spl9_15
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f401,plain,(
    sK2 = k2_relat_1(sK5) ),
    inference(backward_demodulation,[],[f308,f399])).

fof(f399,plain,(
    sK2 = k2_relset_1(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f398,f70])).

fof(f70,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( ~ v2_funct_2(sK5,sK2)
      | ~ v2_funct_1(sK4) )
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    & v1_funct_2(sK5,sK3,sK2)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f51,f50])).

fof(f50,plain,
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
          ( ( ~ v2_funct_2(X3,sK2)
            | ~ v2_funct_1(sK4) )
          & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
          & v1_funct_2(X3,sK3,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK2)
          | ~ v2_funct_1(sK4) )
        & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
        & v1_funct_2(X3,sK3,sK2)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK5,sK2)
        | ~ v2_funct_1(sK4) )
      & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      & v1_funct_2(sK5,sK3,sK2)
      & v1_funct_1(sK5) ) ),
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

fof(f398,plain,
    ( sK2 = k2_relset_1(sK3,sK2,sK5)
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f397,f71])).

fof(f71,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f397,plain,
    ( sK2 = k2_relset_1(sK3,sK2,sK5)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f396,f72])).

fof(f72,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f52])).

fof(f396,plain,
    ( sK2 = k2_relset_1(sK3,sK2,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f395,f67])).

fof(f67,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f395,plain,
    ( sK2 = k2_relset_1(sK3,sK2,sK5)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f394,f68])).

fof(f68,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f394,plain,
    ( sK2 = k2_relset_1(sK3,sK2,sK5)
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f392,f69])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f52])).

fof(f392,plain,
    ( sK2 = k2_relset_1(sK3,sK2,sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f107,f73])).

fof(f73,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f308,plain,(
    k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5) ),
    inference(resolution,[],[f104,f72])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f230,plain,(
    v4_relat_1(sK4,sK2) ),
    inference(resolution,[],[f105,f69])).

fof(f172,plain,
    ( ~ sP0(sK4)
    | spl9_1
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f170,f127])).

fof(f127,plain,
    ( ~ v2_funct_1(sK4)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl9_1
  <=> v2_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f170,plain,
    ( ~ sP0(sK4)
    | v2_funct_1(sK4)
    | ~ spl9_4 ),
    inference(resolution,[],[f142,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f142,plain,
    ( sP1(sK4)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl9_4
  <=> sP1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f745,plain,
    ( spl9_2
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f744])).

fof(f744,plain,
    ( $false
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f405,f131])).

fof(f131,plain,
    ( ~ v2_funct_2(sK5,sK2)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl9_2
  <=> v2_funct_2(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f405,plain,
    ( v2_funct_2(sK5,sK2)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f404,f146])).

fof(f146,plain,
    ( v1_relat_1(sK5)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl9_5
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f404,plain,
    ( v2_funct_2(sK5,sK2)
    | ~ v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f402,f235])).

fof(f235,plain,(
    v5_relat_1(sK5,sK2) ),
    inference(resolution,[],[f106,f72])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f402,plain,
    ( ~ v5_relat_1(sK5,sK2)
    | v2_funct_2(sK5,sK2)
    | ~ v1_relat_1(sK5) ),
    inference(superposition,[],[f118,f401])).

fof(f118,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f629,plain,
    ( spl9_1
    | spl9_16
    | ~ spl9_18 ),
    inference(avatar_contradiction_clause,[],[f628])).

fof(f628,plain,
    ( $false
    | spl9_1
    | spl9_16
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f627,f67])).

fof(f627,plain,
    ( ~ v1_funct_1(sK4)
    | spl9_1
    | spl9_16
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f626,f68])).

fof(f626,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl9_1
    | spl9_16
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f625,f69])).

fof(f625,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl9_1
    | spl9_16
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f624,f70])).

fof(f624,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl9_1
    | spl9_16
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f623,f71])).

fof(f623,plain,
    ( ~ v1_funct_2(sK5,sK3,sK2)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl9_1
    | spl9_16
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f622,f72])).

fof(f622,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl9_1
    | spl9_16
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f621,f127])).

fof(f621,plain,
    ( v2_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl9_16
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f620,f414])).

fof(f414,plain,
    ( k1_xboole_0 != sK2
    | spl9_16 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl9_16
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f620,plain,
    ( k1_xboole_0 = sK2
    | v2_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f614,f115])).

fof(f115,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f76,f77])).

fof(f76,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f614,plain,
    ( ~ v2_funct_1(k6_partfun1(sK2))
    | k1_xboole_0 = sK2
    | v2_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ spl9_18 ),
    inference(superposition,[],[f109,f602])).

fof(f602,plain,
    ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f600])).

fof(f600,plain,
    ( spl9_18
  <=> k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f109,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f610,plain,(
    spl9_17 ),
    inference(avatar_contradiction_clause,[],[f609])).

fof(f609,plain,
    ( $false
    | spl9_17 ),
    inference(subsumption_resolution,[],[f608,f67])).

fof(f608,plain,
    ( ~ v1_funct_1(sK4)
    | spl9_17 ),
    inference(subsumption_resolution,[],[f607,f69])).

fof(f607,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | spl9_17 ),
    inference(subsumption_resolution,[],[f606,f70])).

fof(f606,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | spl9_17 ),
    inference(subsumption_resolution,[],[f605,f72])).

fof(f605,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | spl9_17 ),
    inference(resolution,[],[f598,f114])).

fof(f114,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f598,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | spl9_17 ),
    inference(avatar_component_clause,[],[f596])).

fof(f596,plain,
    ( spl9_17
  <=> m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f603,plain,
    ( ~ spl9_17
    | spl9_18 ),
    inference(avatar_split_clause,[],[f593,f600,f596])).

fof(f593,plain,
    ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
    | ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f338,f73])).

fof(f338,plain,(
    ! [X0,X1] :
      ( ~ r2_relset_1(X0,X0,X1,k6_partfun1(X0))
      | k6_partfun1(X0) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(resolution,[],[f111,f79])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
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
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f415,plain,
    ( spl9_15
    | ~ spl9_16
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f406,f145,f412,f408])).

fof(f406,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK5
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f403,f146])).

fof(f403,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK5
    | ~ v1_relat_1(sK5) ),
    inference(superposition,[],[f83,f401])).

fof(f83,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f300,plain,(
    spl9_14 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | spl9_14 ),
    inference(subsumption_resolution,[],[f298,f75])).

fof(f298,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl9_14 ),
    inference(resolution,[],[f294,f96])).

fof(f294,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | spl9_14 ),
    inference(avatar_component_clause,[],[f292])).

fof(f169,plain,(
    spl9_5 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl9_5 ),
    inference(subsumption_resolution,[],[f164,f147])).

fof(f147,plain,
    ( ~ v1_relat_1(sK5)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f145])).

fof(f164,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f103,f72])).

fof(f167,plain,(
    spl9_3 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl9_3 ),
    inference(subsumption_resolution,[],[f163,f138])).

fof(f138,plain,
    ( ~ v1_relat_1(sK4)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f136])).

fof(f163,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f103,f69])).

fof(f143,plain,
    ( ~ spl9_3
    | spl9_4 ),
    inference(avatar_split_clause,[],[f133,f140,f136])).

fof(f133,plain,
    ( sP1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f91,f67])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f29,f48,f47])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f132,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f74,f129,f125])).

fof(f74,plain,
    ( ~ v2_funct_2(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:04:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (17110)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.50  % (17102)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (17110)Refutation not found, incomplete strategy% (17110)------------------------------
% 0.21/0.52  % (17110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (17110)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (17110)Memory used [KB]: 10874
% 0.21/0.53  % (17110)Time elapsed: 0.106 s
% 0.21/0.53  % (17110)------------------------------
% 0.21/0.53  % (17110)------------------------------
% 0.21/0.53  % (17118)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (17106)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (17100)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (17117)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (17104)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (17115)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (17101)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (17103)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (17124)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (17122)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (17107)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (17128)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (17129)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (17114)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (17109)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (17120)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (17123)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (17116)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (17119)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (17116)Refutation not found, incomplete strategy% (17116)------------------------------
% 0.21/0.55  % (17116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17116)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17116)Memory used [KB]: 10746
% 0.21/0.55  % (17116)Time elapsed: 0.147 s
% 0.21/0.55  % (17116)------------------------------
% 0.21/0.55  % (17116)------------------------------
% 0.21/0.55  % (17108)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (17126)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (17111)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (17112)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (17125)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (17127)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (17105)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.57  % (17128)Refutation not found, incomplete strategy% (17128)------------------------------
% 0.21/0.57  % (17128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (17128)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (17128)Memory used [KB]: 10874
% 0.21/0.57  % (17128)Time elapsed: 0.167 s
% 0.21/0.57  % (17128)------------------------------
% 0.21/0.57  % (17128)------------------------------
% 0.21/0.58  % (17106)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f842,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f132,f143,f167,f169,f300,f415,f603,f610,f629,f745,f841])).
% 0.21/0.58  fof(f841,plain,(
% 0.21/0.58    spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_14 | ~spl9_15),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f840])).
% 0.21/0.58  fof(f840,plain,(
% 0.21/0.58    $false | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_14 | ~spl9_15)),
% 0.21/0.58    inference(subsumption_resolution,[],[f834,f218])).
% 0.21/0.58  fof(f218,plain,(
% 0.21/0.58    sP0(k1_xboole_0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f216,f75])).
% 0.21/0.58  fof(f75,plain,(
% 0.21/0.58    v1_xboole_0(k1_xboole_0)),
% 0.21/0.58    inference(cnf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    v1_xboole_0(k1_xboole_0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.58  fof(f216,plain,(
% 0.21/0.58    sP0(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.58    inference(superposition,[],[f156,f203])).
% 0.21/0.58  fof(f203,plain,(
% 0.21/0.58    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.21/0.58    inference(equality_resolution,[],[f178])).
% 0.21/0.58  fof(f178,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_partfun1(X0)) )),
% 0.21/0.58    inference(global_subsumption,[],[f165,f175])).
% 0.21/0.58  fof(f175,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_partfun1(X0) | ~v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.58    inference(superposition,[],[f82,f117])).
% 0.21/0.58  fof(f117,plain,(
% 0.21/0.58    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f80,f77])).
% 0.21/0.58  fof(f77,plain,(
% 0.21/0.58    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f19,axiom,(
% 0.21/0.58    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.58  fof(f80,plain,(
% 0.21/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.58  fof(f82,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(flattening,[],[f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.58  fof(f165,plain,(
% 0.21/0.58    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.58    inference(resolution,[],[f103,f79])).
% 0.21/0.58  fof(f79,plain,(
% 0.21/0.58    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f18])).
% 0.21/0.58  fof(f18,axiom,(
% 0.21/0.58    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.58  fof(f103,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.58  fof(f156,plain,(
% 0.21/0.58    ( ! [X0] : (sP0(k6_partfun1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.58    inference(superposition,[],[f154,f117])).
% 0.21/0.58  fof(f154,plain,(
% 0.21/0.58    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | sP0(X0)) )),
% 0.21/0.58    inference(resolution,[],[f87,f92])).
% 0.21/0.58  fof(f92,plain,(
% 0.21/0.58    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f61])).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK8(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f59,f60])).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK8(X0),X0))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.58    inference(rectify,[],[f58])).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.58    inference(nnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.58  fof(f87,plain,(
% 0.21/0.58    ( ! [X0] : (r2_hidden(sK6(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f57])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    ! [X0] : ((sP0(X0) | (sK6(X0) != sK7(X0) & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f55,f56])).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK6(X0) != sK7(X0) & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.21/0.58    inference(rectify,[],[f54])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.21/0.58    inference(nnf_transformation,[],[f47])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 0.21/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.58  fof(f834,plain,(
% 0.21/0.58    ~sP0(k1_xboole_0) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_14 | ~spl9_15)),
% 0.21/0.58    inference(backward_demodulation,[],[f172,f802])).
% 0.21/0.58  fof(f802,plain,(
% 0.21/0.58    k1_xboole_0 = sK4 | (~spl9_3 | ~spl9_14 | ~spl9_15)),
% 0.21/0.58    inference(subsumption_resolution,[],[f799,f137])).
% 0.21/0.58  fof(f137,plain,(
% 0.21/0.58    v1_relat_1(sK4) | ~spl9_3),
% 0.21/0.58    inference(avatar_component_clause,[],[f136])).
% 0.21/0.58  fof(f136,plain,(
% 0.21/0.58    spl9_3 <=> v1_relat_1(sK4)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.58  fof(f799,plain,(
% 0.21/0.58    ~v1_relat_1(sK4) | k1_xboole_0 = sK4 | (~spl9_14 | ~spl9_15)),
% 0.21/0.58    inference(resolution,[],[f719,f517])).
% 0.21/0.58  fof(f517,plain,(
% 0.21/0.58    ( ! [X0] : (~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) ) | ~spl9_14),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f514])).
% 0.21/0.58  fof(f514,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_relat_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl9_14),
% 0.21/0.58    inference(resolution,[],[f513,f94])).
% 0.21/0.58  fof(f94,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f62])).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.58    inference(nnf_transformation,[],[f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.58  fof(f513,plain,(
% 0.21/0.58    ( ! [X2] : (~r1_tarski(k1_relat_1(X2),k1_xboole_0) | k1_xboole_0 = X2 | ~v1_relat_1(X2)) ) | ~spl9_14),
% 0.21/0.58    inference(subsumption_resolution,[],[f221,f386])).
% 0.21/0.58  fof(f386,plain,(
% 0.21/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl9_14),
% 0.21/0.58    inference(resolution,[],[f385,f273])).
% 0.21/0.58  fof(f273,plain,(
% 0.21/0.58    ( ! [X1] : (~v4_relat_1(k1_xboole_0,X1) | r1_tarski(k1_xboole_0,X1)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f267,f217])).
% 0.21/0.58  fof(f217,plain,(
% 0.21/0.58    v1_relat_1(k1_xboole_0)),
% 0.21/0.58    inference(superposition,[],[f165,f203])).
% 0.21/0.58  fof(f267,plain,(
% 0.21/0.58    ( ! [X1] : (r1_tarski(k1_xboole_0,X1) | ~v4_relat_1(k1_xboole_0,X1) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.58    inference(superposition,[],[f94,f215])).
% 0.21/0.58  fof(f215,plain,(
% 0.21/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.58    inference(superposition,[],[f117,f203])).
% 0.21/0.58  fof(f385,plain,(
% 0.21/0.58    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) ) | ~spl9_14),
% 0.21/0.58    inference(resolution,[],[f377,f312])).
% 0.21/0.58  fof(f312,plain,(
% 0.21/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl9_14),
% 0.21/0.58    inference(backward_demodulation,[],[f212,f303])).
% 0.21/0.58  fof(f303,plain,(
% 0.21/0.58    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | ~spl9_14),
% 0.21/0.58    inference(resolution,[],[f293,f161])).
% 0.21/0.58  fof(f161,plain,(
% 0.21/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(resolution,[],[f102,f75])).
% 0.21/0.58  fof(f102,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f34])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.58  fof(f293,plain,(
% 0.21/0.58    v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | ~spl9_14),
% 0.21/0.58    inference(avatar_component_clause,[],[f292])).
% 0.21/0.58  fof(f292,plain,(
% 0.21/0.58    spl9_14 <=> v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.21/0.58  fof(f212,plain,(
% 0.21/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.58    inference(superposition,[],[f79,f203])).
% 0.21/0.58  fof(f377,plain,(
% 0.21/0.58    ( ! [X6,X5] : (~m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X6,X5)) )),
% 0.21/0.58    inference(superposition,[],[f105,f371])).
% 0.21/0.58  fof(f371,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.58    inference(resolution,[],[f200,f75])).
% 0.21/0.58  fof(f200,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v1_xboole_0(X1) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.58    inference(resolution,[],[f161,f96])).
% 0.21/0.58  fof(f96,plain,(
% 0.21/0.58    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 0.21/0.58  fof(f105,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.58  fof(f221,plain,(
% 0.21/0.58    ( ! [X2] : (~r1_tarski(k1_relat_1(X2),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | k1_xboole_0 = X2 | ~v1_relat_1(X2)) )),
% 0.21/0.58    inference(extensionality_resolution,[],[f101,f82])).
% 0.21/0.58  fof(f101,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f65])).
% 0.21/0.58  fof(f65,plain,(
% 0.21/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.58    inference(flattening,[],[f64])).
% 0.21/0.58  fof(f64,plain,(
% 0.21/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.58    inference(nnf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.58  fof(f719,plain,(
% 0.21/0.58    v4_relat_1(sK4,k1_xboole_0) | ~spl9_15),
% 0.21/0.58    inference(backward_demodulation,[],[f230,f664])).
% 0.21/0.58  fof(f664,plain,(
% 0.21/0.58    k1_xboole_0 = sK2 | ~spl9_15),
% 0.21/0.58    inference(forward_demodulation,[],[f656,f214])).
% 0.21/0.58  fof(f214,plain,(
% 0.21/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.58    inference(superposition,[],[f116,f203])).
% 0.21/0.58  fof(f116,plain,(
% 0.21/0.58    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f81,f77])).
% 0.21/0.58  fof(f81,plain,(
% 0.21/0.58    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f9])).
% 0.21/0.58  fof(f656,plain,(
% 0.21/0.58    sK2 = k2_relat_1(k1_xboole_0) | ~spl9_15),
% 0.21/0.58    inference(backward_demodulation,[],[f401,f410])).
% 0.21/0.58  fof(f410,plain,(
% 0.21/0.58    k1_xboole_0 = sK5 | ~spl9_15),
% 0.21/0.58    inference(avatar_component_clause,[],[f408])).
% 0.21/0.58  fof(f408,plain,(
% 0.21/0.58    spl9_15 <=> k1_xboole_0 = sK5),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.58  fof(f401,plain,(
% 0.21/0.58    sK2 = k2_relat_1(sK5)),
% 0.21/0.58    inference(backward_demodulation,[],[f308,f399])).
% 0.21/0.58  fof(f399,plain,(
% 0.21/0.58    sK2 = k2_relset_1(sK3,sK2,sK5)),
% 0.21/0.58    inference(subsumption_resolution,[],[f398,f70])).
% 0.21/0.58  fof(f70,plain,(
% 0.21/0.58    v1_funct_1(sK5)),
% 0.21/0.58    inference(cnf_transformation,[],[f52])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    ((~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f51,f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(X3,sK3,sK2) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ? [X3] : ((~v2_funct_2(X3,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(X3,sK3,sK2) & v1_funct_1(X3)) => ((~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.58    inference(flattening,[],[f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.58    inference(ennf_transformation,[],[f23])).
% 0.21/0.58  fof(f23,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.21/0.58    inference(negated_conjecture,[],[f22])).
% 0.21/0.58  fof(f22,conjecture,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 0.21/0.58  fof(f398,plain,(
% 0.21/0.58    sK2 = k2_relset_1(sK3,sK2,sK5) | ~v1_funct_1(sK5)),
% 0.21/0.58    inference(subsumption_resolution,[],[f397,f71])).
% 0.21/0.58  fof(f71,plain,(
% 0.21/0.58    v1_funct_2(sK5,sK3,sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f52])).
% 0.21/0.58  fof(f397,plain,(
% 0.21/0.58    sK2 = k2_relset_1(sK3,sK2,sK5) | ~v1_funct_2(sK5,sK3,sK2) | ~v1_funct_1(sK5)),
% 0.21/0.58    inference(subsumption_resolution,[],[f396,f72])).
% 0.21/0.58  fof(f72,plain,(
% 0.21/0.58    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 0.21/0.58    inference(cnf_transformation,[],[f52])).
% 0.21/0.58  fof(f396,plain,(
% 0.21/0.58    sK2 = k2_relset_1(sK3,sK2,sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(sK5,sK3,sK2) | ~v1_funct_1(sK5)),
% 0.21/0.58    inference(subsumption_resolution,[],[f395,f67])).
% 0.21/0.58  fof(f67,plain,(
% 0.21/0.58    v1_funct_1(sK4)),
% 0.21/0.58    inference(cnf_transformation,[],[f52])).
% 0.21/0.58  fof(f395,plain,(
% 0.21/0.58    sK2 = k2_relset_1(sK3,sK2,sK5) | ~v1_funct_1(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(sK5,sK3,sK2) | ~v1_funct_1(sK5)),
% 0.21/0.58    inference(subsumption_resolution,[],[f394,f68])).
% 0.21/0.58  fof(f68,plain,(
% 0.21/0.58    v1_funct_2(sK4,sK2,sK3)),
% 0.21/0.58    inference(cnf_transformation,[],[f52])).
% 0.21/0.58  fof(f394,plain,(
% 0.21/0.58    sK2 = k2_relset_1(sK3,sK2,sK5) | ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(sK5,sK3,sK2) | ~v1_funct_1(sK5)),
% 0.21/0.58    inference(subsumption_resolution,[],[f392,f69])).
% 0.21/0.58  fof(f69,plain,(
% 0.21/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.58    inference(cnf_transformation,[],[f52])).
% 0.21/0.58  fof(f392,plain,(
% 0.21/0.58    sK2 = k2_relset_1(sK3,sK2,sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(sK5,sK3,sK2) | ~v1_funct_1(sK5)),
% 0.21/0.58    inference(resolution,[],[f107,f73])).
% 0.21/0.58  fof(f73,plain,(
% 0.21/0.58    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))),
% 0.21/0.58    inference(cnf_transformation,[],[f52])).
% 0.21/0.58  fof(f107,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f39])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.58    inference(flattening,[],[f38])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.58    inference(ennf_transformation,[],[f20])).
% 0.21/0.58  fof(f20,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 0.21/0.58  fof(f308,plain,(
% 0.21/0.58    k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5)),
% 0.21/0.58    inference(resolution,[],[f104,f72])).
% 0.21/0.58  fof(f104,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f36])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.58  fof(f230,plain,(
% 0.21/0.58    v4_relat_1(sK4,sK2)),
% 0.21/0.58    inference(resolution,[],[f105,f69])).
% 0.21/0.58  fof(f172,plain,(
% 0.21/0.58    ~sP0(sK4) | (spl9_1 | ~spl9_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f170,f127])).
% 0.21/0.58  fof(f127,plain,(
% 0.21/0.58    ~v2_funct_1(sK4) | spl9_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f125])).
% 0.21/0.58  fof(f125,plain,(
% 0.21/0.58    spl9_1 <=> v2_funct_1(sK4)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.58  fof(f170,plain,(
% 0.21/0.58    ~sP0(sK4) | v2_funct_1(sK4) | ~spl9_4),
% 0.21/0.58    inference(resolution,[],[f142,f85])).
% 0.21/0.58  fof(f85,plain,(
% 0.21/0.58    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_funct_1(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f53])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 0.21/0.58    inference(nnf_transformation,[],[f48])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.21/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.58  fof(f142,plain,(
% 0.21/0.58    sP1(sK4) | ~spl9_4),
% 0.21/0.58    inference(avatar_component_clause,[],[f140])).
% 0.21/0.58  fof(f140,plain,(
% 0.21/0.58    spl9_4 <=> sP1(sK4)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.58  fof(f745,plain,(
% 0.21/0.58    spl9_2 | ~spl9_5),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f744])).
% 0.21/0.58  fof(f744,plain,(
% 0.21/0.58    $false | (spl9_2 | ~spl9_5)),
% 0.21/0.58    inference(subsumption_resolution,[],[f405,f131])).
% 0.21/0.58  fof(f131,plain,(
% 0.21/0.58    ~v2_funct_2(sK5,sK2) | spl9_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f129])).
% 0.21/0.58  fof(f129,plain,(
% 0.21/0.58    spl9_2 <=> v2_funct_2(sK5,sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.58  fof(f405,plain,(
% 0.21/0.58    v2_funct_2(sK5,sK2) | ~spl9_5),
% 0.21/0.58    inference(subsumption_resolution,[],[f404,f146])).
% 0.21/0.58  fof(f146,plain,(
% 0.21/0.59    v1_relat_1(sK5) | ~spl9_5),
% 0.21/0.59    inference(avatar_component_clause,[],[f145])).
% 0.21/0.59  fof(f145,plain,(
% 0.21/0.59    spl9_5 <=> v1_relat_1(sK5)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.59  fof(f404,plain,(
% 0.21/0.59    v2_funct_2(sK5,sK2) | ~v1_relat_1(sK5)),
% 0.21/0.59    inference(subsumption_resolution,[],[f402,f235])).
% 0.21/0.59  fof(f235,plain,(
% 0.21/0.59    v5_relat_1(sK5,sK2)),
% 0.21/0.59    inference(resolution,[],[f106,f72])).
% 0.21/0.59  fof(f106,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f37])).
% 0.21/0.59  fof(f402,plain,(
% 0.21/0.59    ~v5_relat_1(sK5,sK2) | v2_funct_2(sK5,sK2) | ~v1_relat_1(sK5)),
% 0.21/0.59    inference(superposition,[],[f118,f401])).
% 0.21/0.59  fof(f118,plain,(
% 0.21/0.59    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.59    inference(equality_resolution,[],[f98])).
% 0.21/0.59  fof(f98,plain,(
% 0.21/0.59    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f63])).
% 0.21/0.59  fof(f63,plain,(
% 0.21/0.59    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.59    inference(nnf_transformation,[],[f33])).
% 0.21/0.59  fof(f33,plain,(
% 0.21/0.59    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.59    inference(flattening,[],[f32])).
% 0.21/0.59  fof(f32,plain,(
% 0.21/0.59    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.59    inference(ennf_transformation,[],[f16])).
% 0.21/0.59  fof(f16,axiom,(
% 0.21/0.59    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.21/0.59  fof(f629,plain,(
% 0.21/0.59    spl9_1 | spl9_16 | ~spl9_18),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f628])).
% 0.21/0.59  fof(f628,plain,(
% 0.21/0.59    $false | (spl9_1 | spl9_16 | ~spl9_18)),
% 0.21/0.59    inference(subsumption_resolution,[],[f627,f67])).
% 0.21/0.59  fof(f627,plain,(
% 0.21/0.59    ~v1_funct_1(sK4) | (spl9_1 | spl9_16 | ~spl9_18)),
% 0.21/0.59    inference(subsumption_resolution,[],[f626,f68])).
% 0.21/0.59  fof(f626,plain,(
% 0.21/0.59    ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4) | (spl9_1 | spl9_16 | ~spl9_18)),
% 0.21/0.59    inference(subsumption_resolution,[],[f625,f69])).
% 0.21/0.59  fof(f625,plain,(
% 0.21/0.59    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4) | (spl9_1 | spl9_16 | ~spl9_18)),
% 0.21/0.59    inference(subsumption_resolution,[],[f624,f70])).
% 0.21/0.59  fof(f624,plain,(
% 0.21/0.59    ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4) | (spl9_1 | spl9_16 | ~spl9_18)),
% 0.21/0.59    inference(subsumption_resolution,[],[f623,f71])).
% 0.21/0.59  fof(f623,plain,(
% 0.21/0.59    ~v1_funct_2(sK5,sK3,sK2) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4) | (spl9_1 | spl9_16 | ~spl9_18)),
% 0.21/0.59    inference(subsumption_resolution,[],[f622,f72])).
% 0.21/0.59  fof(f622,plain,(
% 0.21/0.59    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(sK5,sK3,sK2) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4) | (spl9_1 | spl9_16 | ~spl9_18)),
% 0.21/0.59    inference(subsumption_resolution,[],[f621,f127])).
% 0.21/0.59  fof(f621,plain,(
% 0.21/0.59    v2_funct_1(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(sK5,sK3,sK2) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4) | (spl9_16 | ~spl9_18)),
% 0.21/0.59    inference(subsumption_resolution,[],[f620,f414])).
% 0.21/0.59  fof(f414,plain,(
% 0.21/0.59    k1_xboole_0 != sK2 | spl9_16),
% 0.21/0.59    inference(avatar_component_clause,[],[f412])).
% 0.21/0.59  fof(f412,plain,(
% 0.21/0.59    spl9_16 <=> k1_xboole_0 = sK2),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.21/0.59  fof(f620,plain,(
% 0.21/0.59    k1_xboole_0 = sK2 | v2_funct_1(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(sK5,sK3,sK2) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4) | ~spl9_18),
% 0.21/0.59    inference(subsumption_resolution,[],[f614,f115])).
% 0.21/0.59  fof(f115,plain,(
% 0.21/0.59    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.21/0.59    inference(definition_unfolding,[],[f76,f77])).
% 0.21/0.59  fof(f76,plain,(
% 0.21/0.59    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f11])).
% 0.21/0.59  fof(f11,axiom,(
% 0.21/0.59    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 0.21/0.59  fof(f614,plain,(
% 0.21/0.59    ~v2_funct_1(k6_partfun1(sK2)) | k1_xboole_0 = sK2 | v2_funct_1(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(sK5,sK3,sK2) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4) | ~spl9_18),
% 0.21/0.59    inference(superposition,[],[f109,f602])).
% 0.21/0.59  fof(f602,plain,(
% 0.21/0.59    k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) | ~spl9_18),
% 0.21/0.59    inference(avatar_component_clause,[],[f600])).
% 0.21/0.59  fof(f600,plain,(
% 0.21/0.59    spl9_18 <=> k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.21/0.59  fof(f109,plain,(
% 0.21/0.59    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f42])).
% 0.21/0.59  fof(f42,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.59    inference(flattening,[],[f41])).
% 0.21/0.59  fof(f41,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.59    inference(ennf_transformation,[],[f21])).
% 0.21/0.59  fof(f21,axiom,(
% 0.21/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 0.21/0.59  fof(f610,plain,(
% 0.21/0.59    spl9_17),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f609])).
% 0.21/0.59  fof(f609,plain,(
% 0.21/0.59    $false | spl9_17),
% 0.21/0.59    inference(subsumption_resolution,[],[f608,f67])).
% 0.21/0.59  fof(f608,plain,(
% 0.21/0.59    ~v1_funct_1(sK4) | spl9_17),
% 0.21/0.59    inference(subsumption_resolution,[],[f607,f69])).
% 0.21/0.59  fof(f607,plain,(
% 0.21/0.59    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_1(sK4) | spl9_17),
% 0.21/0.59    inference(subsumption_resolution,[],[f606,f70])).
% 0.21/0.59  fof(f606,plain,(
% 0.21/0.59    ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_1(sK4) | spl9_17),
% 0.21/0.59    inference(subsumption_resolution,[],[f605,f72])).
% 0.21/0.59  fof(f605,plain,(
% 0.21/0.59    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_1(sK4) | spl9_17),
% 0.21/0.59    inference(resolution,[],[f598,f114])).
% 0.21/0.59  fof(f114,plain,(
% 0.21/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f46])).
% 0.21/0.59  fof(f46,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.59    inference(flattening,[],[f45])).
% 0.21/0.59  fof(f45,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.59    inference(ennf_transformation,[],[f17])).
% 0.21/0.59  fof(f17,axiom,(
% 0.21/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.21/0.59  fof(f598,plain,(
% 0.21/0.59    ~m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | spl9_17),
% 0.21/0.59    inference(avatar_component_clause,[],[f596])).
% 0.21/0.59  fof(f596,plain,(
% 0.21/0.59    spl9_17 <=> m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.21/0.59  fof(f603,plain,(
% 0.21/0.59    ~spl9_17 | spl9_18),
% 0.21/0.59    inference(avatar_split_clause,[],[f593,f600,f596])).
% 0.21/0.59  fof(f593,plain,(
% 0.21/0.59    k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) | ~m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.21/0.59    inference(resolution,[],[f338,f73])).
% 0.21/0.59  fof(f338,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r2_relset_1(X0,X0,X1,k6_partfun1(X0)) | k6_partfun1(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.59    inference(resolution,[],[f111,f79])).
% 0.21/0.59  fof(f111,plain,(
% 0.21/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f66])).
% 0.21/0.59  fof(f66,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.59    inference(nnf_transformation,[],[f44])).
% 0.21/0.59  fof(f44,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.59    inference(flattening,[],[f43])).
% 0.21/0.59  fof(f43,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.59    inference(ennf_transformation,[],[f15])).
% 0.21/0.59  fof(f15,axiom,(
% 0.21/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.59  fof(f415,plain,(
% 0.21/0.59    spl9_15 | ~spl9_16 | ~spl9_5),
% 0.21/0.59    inference(avatar_split_clause,[],[f406,f145,f412,f408])).
% 0.21/0.59  fof(f406,plain,(
% 0.21/0.59    k1_xboole_0 != sK2 | k1_xboole_0 = sK5 | ~spl9_5),
% 0.21/0.59    inference(subsumption_resolution,[],[f403,f146])).
% 0.21/0.59  fof(f403,plain,(
% 0.21/0.59    k1_xboole_0 != sK2 | k1_xboole_0 = sK5 | ~v1_relat_1(sK5)),
% 0.21/0.59    inference(superposition,[],[f83,f401])).
% 0.21/0.59  fof(f83,plain,(
% 0.21/0.59    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f27])).
% 0.21/0.59  fof(f300,plain,(
% 0.21/0.59    spl9_14),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f299])).
% 0.21/0.59  fof(f299,plain,(
% 0.21/0.59    $false | spl9_14),
% 0.21/0.59    inference(subsumption_resolution,[],[f298,f75])).
% 0.21/0.59  fof(f298,plain,(
% 0.21/0.59    ~v1_xboole_0(k1_xboole_0) | spl9_14),
% 0.21/0.59    inference(resolution,[],[f294,f96])).
% 0.21/0.59  fof(f294,plain,(
% 0.21/0.59    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | spl9_14),
% 0.21/0.59    inference(avatar_component_clause,[],[f292])).
% 0.21/0.59  fof(f169,plain,(
% 0.21/0.59    spl9_5),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f168])).
% 0.21/0.59  fof(f168,plain,(
% 0.21/0.59    $false | spl9_5),
% 0.21/0.59    inference(subsumption_resolution,[],[f164,f147])).
% 0.21/0.59  fof(f147,plain,(
% 0.21/0.59    ~v1_relat_1(sK5) | spl9_5),
% 0.21/0.59    inference(avatar_component_clause,[],[f145])).
% 0.21/0.59  fof(f164,plain,(
% 0.21/0.59    v1_relat_1(sK5)),
% 0.21/0.59    inference(resolution,[],[f103,f72])).
% 0.21/0.59  fof(f167,plain,(
% 0.21/0.59    spl9_3),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f166])).
% 0.21/0.59  fof(f166,plain,(
% 0.21/0.59    $false | spl9_3),
% 0.21/0.59    inference(subsumption_resolution,[],[f163,f138])).
% 0.21/0.59  fof(f138,plain,(
% 0.21/0.59    ~v1_relat_1(sK4) | spl9_3),
% 0.21/0.59    inference(avatar_component_clause,[],[f136])).
% 0.21/0.59  fof(f163,plain,(
% 0.21/0.59    v1_relat_1(sK4)),
% 0.21/0.59    inference(resolution,[],[f103,f69])).
% 0.21/0.59  fof(f143,plain,(
% 0.21/0.59    ~spl9_3 | spl9_4),
% 0.21/0.59    inference(avatar_split_clause,[],[f133,f140,f136])).
% 0.21/0.59  fof(f133,plain,(
% 0.21/0.59    sP1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.59    inference(resolution,[],[f91,f67])).
% 0.21/0.59  fof(f91,plain,(
% 0.21/0.59    ( ! [X0] : (~v1_funct_1(X0) | sP1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f49])).
% 0.21/0.59  fof(f49,plain,(
% 0.21/0.59    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(definition_folding,[],[f29,f48,f47])).
% 0.21/0.59  fof(f29,plain,(
% 0.21/0.59    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(flattening,[],[f28])).
% 0.21/0.59  fof(f28,plain,(
% 0.21/0.59    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f10])).
% 0.21/0.59  fof(f10,axiom,(
% 0.21/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.21/0.59  fof(f132,plain,(
% 0.21/0.59    ~spl9_1 | ~spl9_2),
% 0.21/0.59    inference(avatar_split_clause,[],[f74,f129,f125])).
% 0.21/0.59  fof(f74,plain,(
% 0.21/0.59    ~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)),
% 0.21/0.59    inference(cnf_transformation,[],[f52])).
% 0.21/0.59  % SZS output end Proof for theBenchmark
% 0.21/0.59  % (17106)------------------------------
% 0.21/0.59  % (17106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (17106)Termination reason: Refutation
% 0.21/0.59  
% 0.21/0.59  % (17106)Memory used [KB]: 11257
% 0.21/0.59  % (17106)Time elapsed: 0.178 s
% 0.21/0.59  % (17106)------------------------------
% 0.21/0.59  % (17106)------------------------------
% 0.21/0.59  % (17099)Success in time 0.222 s
%------------------------------------------------------------------------------
