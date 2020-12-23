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
% DateTime   : Thu Dec  3 13:05:45 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 614 expanded)
%              Number of leaves         :   24 ( 187 expanded)
%              Depth                    :   27
%              Number of atoms          :  591 (4255 expanded)
%              Number of equality atoms :  152 ( 253 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f492,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f192,f389,f416,f491])).

fof(f491,plain,
    ( ~ spl3_1
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f490])).

fof(f490,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f489,f145])).

fof(f145,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f98,f106])).

fof(f106,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f65,f87])).

fof(f87,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f58,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f489,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f488,f436])).

fof(f436,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f428,f104])).

fof(f104,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f92,f87])).

fof(f92,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f67,f59])).

fof(f67,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f428,plain,
    ( sK0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f175,f187])).

fof(f187,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f175,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f174,f107])).

fof(f107,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f75,f51])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f44,f43])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v3_funct_2(X2,sK0,sK0)
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f174,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f173,f122])).

fof(f122,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f78,f51])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f173,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f170,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f170,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f169,f48])).

fof(f48,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f169,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f165,f50])).

fof(f50,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f165,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(resolution,[],[f81,f51])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f488,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f487,f394])).

fof(f394,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl3_15
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f487,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k1_xboole_0)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f486,f265])).

fof(f265,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f249,f87])).

fof(f249,plain,(
    ! [X0] : k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) ),
    inference(subsumption_resolution,[],[f248,f92])).

fof(f248,plain,(
    ! [X0] :
      ( k2_relat_1(k6_partfun1(X0)) != X0
      | k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) ) ),
    inference(forward_demodulation,[],[f247,f93])).

fof(f93,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f66,f59])).

fof(f66,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f247,plain,(
    ! [X0] :
      ( k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))
      | k2_relat_1(k6_partfun1(X0)) != k1_relat_1(k6_partfun1(X0)) ) ),
    inference(trivial_inequality_removal,[],[f246])).

fof(f246,plain,(
    ! [X0] :
      ( k6_partfun1(X0) != k6_partfun1(X0)
      | k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))
      | k2_relat_1(k6_partfun1(X0)) != k1_relat_1(k6_partfun1(X0)) ) ),
    inference(forward_demodulation,[],[f245,f92])).

fof(f245,plain,(
    ! [X0] :
      ( k6_partfun1(X0) != k6_partfun1(k2_relat_1(k6_partfun1(X0)))
      | k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))
      | k2_relat_1(k6_partfun1(X0)) != k1_relat_1(k6_partfun1(X0)) ) ),
    inference(subsumption_resolution,[],[f244,f89])).

fof(f89,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f60,f59])).

fof(f60,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f244,plain,(
    ! [X0] :
      ( k6_partfun1(X0) != k6_partfun1(k2_relat_1(k6_partfun1(X0)))
      | k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))
      | k2_relat_1(k6_partfun1(X0)) != k1_relat_1(k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(subsumption_resolution,[],[f243,f90])).

fof(f90,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f63,f59])).

fof(f63,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f243,plain,(
    ! [X0] :
      ( k6_partfun1(X0) != k6_partfun1(k2_relat_1(k6_partfun1(X0)))
      | k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))
      | k2_relat_1(k6_partfun1(X0)) != k1_relat_1(k6_partfun1(X0))
      | ~ v1_funct_1(k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(subsumption_resolution,[],[f242,f88])).

fof(f88,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f61,f59])).

fof(f61,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f242,plain,(
    ! [X0] :
      ( k6_partfun1(X0) != k6_partfun1(k2_relat_1(k6_partfun1(X0)))
      | k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))
      | k2_relat_1(k6_partfun1(X0)) != k1_relat_1(k6_partfun1(X0))
      | ~ v2_funct_1(k6_partfun1(X0))
      | ~ v1_funct_1(k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f237])).

% (15514)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% (15512)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f237,plain,(
    ! [X0] :
      ( k6_partfun1(X0) != k6_partfun1(k2_relat_1(k6_partfun1(X0)))
      | k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))
      | k2_relat_1(k6_partfun1(X0)) != k1_relat_1(k6_partfun1(X0))
      | ~ v2_funct_1(k6_partfun1(X0))
      | ~ v1_funct_1(k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0))
      | ~ v1_funct_1(k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f95,f132])).

fof(f132,plain,(
    ! [X0] : k6_partfun1(X0) = k5_relat_1(k6_partfun1(X0),k6_partfun1(X0)) ),
    inference(forward_demodulation,[],[f127,f92])).

fof(f127,plain,(
    ! [X0] : k6_partfun1(X0) = k5_relat_1(k6_partfun1(X0),k6_partfun1(k2_relat_1(k6_partfun1(X0)))) ),
    inference(resolution,[],[f94,f89])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f68,f59])).

fof(f68,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f71,f59])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f486,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(k1_xboole_0))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f234,f187])).

fof(f234,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f57,f215])).

fof(f215,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f214,f48])).

fof(f214,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f213,f49])).

fof(f49,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f213,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f209,f50])).

fof(f209,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f74,f51])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f57,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f416,plain,
    ( spl3_15
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f415,f189,f392])).

fof(f189,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f415,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f208,f108])).

fof(f108,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f75,f55])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f208,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f70,f178])).

fof(f178,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f177,f108])).

fof(f177,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f176,f123])).

fof(f123,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f78,f55])).

fof(f176,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f172,f72])).

fof(f172,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f171,f52])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f171,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f166,f54])).

fof(f54,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f166,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0) ),
    inference(resolution,[],[f81,f55])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f389,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f388])).

fof(f388,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f386,f143])).

fof(f143,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f98,f55])).

fof(f386,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | spl3_2 ),
    inference(backward_demodulation,[],[f234,f379])).

fof(f379,plain,
    ( sK2 = k2_funct_1(sK1)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f378,f52])).

fof(f378,plain,
    ( sK2 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f377,f53])).

fof(f53,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f377,plain,
    ( sK2 = k2_funct_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f376,f55])).

fof(f376,plain,
    ( sK2 = k2_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl3_2 ),
    inference(resolution,[],[f326,f56])).

fof(f56,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f326,plain,
    ( ! [X2] :
        ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        | k2_funct_1(sK1) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ v1_funct_1(X2) )
    | spl3_2 ),
    inference(subsumption_resolution,[],[f325,f48])).

fof(f325,plain,
    ( ! [X2] :
        ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        | k2_funct_1(sK1) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(sK1) )
    | spl3_2 ),
    inference(subsumption_resolution,[],[f324,f49])).

fof(f324,plain,
    ( ! [X2] :
        ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        | k2_funct_1(sK1) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(sK1,sK0,sK0)
        | ~ v1_funct_1(sK1) )
    | spl3_2 ),
    inference(subsumption_resolution,[],[f323,f51])).

fof(f323,plain,
    ( ! [X2] :
        ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        | k2_funct_1(sK1) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(sK1,sK0,sK0)
        | ~ v1_funct_1(sK1) )
    | spl3_2 ),
    inference(subsumption_resolution,[],[f317,f191])).

fof(f191,plain,
    ( k1_xboole_0 != sK0
    | spl3_2 ),
    inference(avatar_component_clause,[],[f189])).

fof(f317,plain,(
    ! [X2] :
      ( k1_xboole_0 = sK0
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
      | k2_funct_1(sK1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X2,sK0,sK0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(trivial_inequality_removal,[],[f316])).

fof(f316,plain,(
    ! [X2] :
      ( sK0 != sK0
      | k1_xboole_0 = sK0
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
      | k2_funct_1(sK1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X2,sK0,sK0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f312])).

fof(f312,plain,(
    ! [X2] :
      ( sK0 != sK0
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK0
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
      | k2_funct_1(sK1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X2,sK0,sK0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(superposition,[],[f99,f179])).

fof(f179,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(backward_demodulation,[],[f150,f175])).

fof(f150,plain,(
    k2_relat_1(sK1) = k2_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f76,f51])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_funct_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(global_subsumption,[],[f82,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | v2_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

% (15491)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f192,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f183,f189,f185])).

fof(f183,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f182,f107])).

fof(f182,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f70,f175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n012.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 10:10:07 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.20/0.50  % (15496)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (15502)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.50  % (15502)Refutation not found, incomplete strategy% (15502)------------------------------
% 0.20/0.50  % (15502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (15502)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (15502)Memory used [KB]: 10746
% 0.20/0.50  % (15502)Time elapsed: 0.110 s
% 0.20/0.50  % (15502)------------------------------
% 0.20/0.50  % (15502)------------------------------
% 0.20/0.53  % (15492)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (15519)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (15519)Refutation not found, incomplete strategy% (15519)------------------------------
% 0.20/0.54  % (15519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (15519)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (15519)Memory used [KB]: 1663
% 0.20/0.54  % (15519)Time elapsed: 0.002 s
% 0.20/0.54  % (15519)------------------------------
% 0.20/0.54  % (15519)------------------------------
% 0.20/0.54  % (15516)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.37/0.55  % (15496)Refutation found. Thanks to Tanya!
% 1.37/0.55  % SZS status Theorem for theBenchmark
% 1.37/0.55  % SZS output start Proof for theBenchmark
% 1.37/0.55  fof(f492,plain,(
% 1.37/0.55    $false),
% 1.37/0.55    inference(avatar_sat_refutation,[],[f192,f389,f416,f491])).
% 1.37/0.55  fof(f491,plain,(
% 1.37/0.55    ~spl3_1 | ~spl3_15),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f490])).
% 1.37/0.55  fof(f490,plain,(
% 1.37/0.55    $false | (~spl3_1 | ~spl3_15)),
% 1.37/0.55    inference(subsumption_resolution,[],[f489,f145])).
% 1.37/0.55  fof(f145,plain,(
% 1.37/0.55    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.37/0.55    inference(resolution,[],[f98,f106])).
% 1.37/0.55  fof(f106,plain,(
% 1.37/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.37/0.55    inference(superposition,[],[f65,f87])).
% 1.37/0.55  fof(f87,plain,(
% 1.37/0.55    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.37/0.55    inference(definition_unfolding,[],[f58,f59])).
% 1.37/0.55  fof(f59,plain,(
% 1.37/0.55    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f16])).
% 1.37/0.55  fof(f16,axiom,(
% 1.37/0.55    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.37/0.55  fof(f58,plain,(
% 1.37/0.55    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.37/0.55    inference(cnf_transformation,[],[f4])).
% 1.37/0.55  fof(f4,axiom,(
% 1.37/0.55    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.37/0.55  fof(f65,plain,(
% 1.37/0.55    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f14])).
% 1.37/0.55  fof(f14,axiom,(
% 1.37/0.55    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.37/0.55  fof(f98,plain,(
% 1.37/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.37/0.55    inference(duplicate_literal_removal,[],[f97])).
% 1.37/0.55  fof(f97,plain,(
% 1.37/0.55    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.37/0.55    inference(equality_resolution,[],[f86])).
% 1.37/0.55  fof(f86,plain,(
% 1.37/0.55    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f47])).
% 1.37/0.55  fof(f47,plain,(
% 1.37/0.55    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.55    inference(nnf_transformation,[],[f42])).
% 1.37/0.55  fof(f42,plain,(
% 1.37/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.55    inference(flattening,[],[f41])).
% 1.37/0.55  fof(f41,plain,(
% 1.37/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.37/0.55    inference(ennf_transformation,[],[f11])).
% 1.37/0.55  fof(f11,axiom,(
% 1.37/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.37/0.55  fof(f489,plain,(
% 1.37/0.55    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_1 | ~spl3_15)),
% 1.37/0.55    inference(forward_demodulation,[],[f488,f436])).
% 1.37/0.55  fof(f436,plain,(
% 1.37/0.55    k1_xboole_0 = sK0 | ~spl3_1),
% 1.37/0.55    inference(forward_demodulation,[],[f428,f104])).
% 1.37/0.55  fof(f104,plain,(
% 1.37/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.37/0.55    inference(superposition,[],[f92,f87])).
% 1.37/0.55  fof(f92,plain,(
% 1.37/0.55    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.37/0.55    inference(definition_unfolding,[],[f67,f59])).
% 1.37/0.55  fof(f67,plain,(
% 1.37/0.55    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.37/0.55    inference(cnf_transformation,[],[f2])).
% 1.37/0.55  fof(f2,axiom,(
% 1.37/0.55    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.37/0.55  fof(f428,plain,(
% 1.37/0.55    sK0 = k2_relat_1(k1_xboole_0) | ~spl3_1),
% 1.37/0.55    inference(backward_demodulation,[],[f175,f187])).
% 1.37/0.55  fof(f187,plain,(
% 1.37/0.55    k1_xboole_0 = sK1 | ~spl3_1),
% 1.37/0.55    inference(avatar_component_clause,[],[f185])).
% 1.37/0.55  fof(f185,plain,(
% 1.37/0.55    spl3_1 <=> k1_xboole_0 = sK1),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.37/0.55  fof(f175,plain,(
% 1.37/0.55    sK0 = k2_relat_1(sK1)),
% 1.37/0.55    inference(subsumption_resolution,[],[f174,f107])).
% 1.37/0.55  fof(f107,plain,(
% 1.37/0.55    v1_relat_1(sK1)),
% 1.37/0.55    inference(resolution,[],[f75,f51])).
% 1.37/0.55  fof(f51,plain,(
% 1.37/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.37/0.55    inference(cnf_transformation,[],[f45])).
% 1.37/0.55  fof(f45,plain,(
% 1.37/0.55    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.37/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f44,f43])).
% 1.37/0.55  fof(f43,plain,(
% 1.37/0.55    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.37/0.55    introduced(choice_axiom,[])).
% 1.37/0.55  fof(f44,plain,(
% 1.37/0.55    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 1.37/0.55    introduced(choice_axiom,[])).
% 1.37/0.55  fof(f22,plain,(
% 1.37/0.55    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.37/0.55    inference(flattening,[],[f21])).
% 1.37/0.55  fof(f21,plain,(
% 1.37/0.55    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.37/0.55    inference(ennf_transformation,[],[f20])).
% 1.37/0.55  fof(f20,negated_conjecture,(
% 1.37/0.55    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.37/0.55    inference(negated_conjecture,[],[f19])).
% 1.37/0.55  fof(f19,conjecture,(
% 1.37/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).
% 1.37/0.55  fof(f75,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f32])).
% 1.37/0.55  fof(f32,plain,(
% 1.37/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.55    inference(ennf_transformation,[],[f8])).
% 1.37/0.55  fof(f8,axiom,(
% 1.37/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.37/0.55  fof(f174,plain,(
% 1.37/0.55    sK0 = k2_relat_1(sK1) | ~v1_relat_1(sK1)),
% 1.37/0.55    inference(subsumption_resolution,[],[f173,f122])).
% 1.37/0.55  fof(f122,plain,(
% 1.37/0.55    v5_relat_1(sK1,sK0)),
% 1.37/0.55    inference(resolution,[],[f78,f51])).
% 1.37/0.55  fof(f78,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f34])).
% 1.37/0.55  fof(f34,plain,(
% 1.37/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.55    inference(ennf_transformation,[],[f9])).
% 1.37/0.55  fof(f9,axiom,(
% 1.37/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.37/0.55  fof(f173,plain,(
% 1.37/0.55    sK0 = k2_relat_1(sK1) | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 1.37/0.55    inference(resolution,[],[f170,f72])).
% 1.37/0.55  fof(f72,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f46])).
% 1.37/0.55  fof(f46,plain,(
% 1.37/0.55    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.37/0.55    inference(nnf_transformation,[],[f29])).
% 1.37/0.55  fof(f29,plain,(
% 1.37/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.37/0.55    inference(flattening,[],[f28])).
% 1.37/0.55  fof(f28,plain,(
% 1.37/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.37/0.55    inference(ennf_transformation,[],[f13])).
% 1.37/0.55  fof(f13,axiom,(
% 1.37/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.37/0.55  fof(f170,plain,(
% 1.37/0.55    v2_funct_2(sK1,sK0)),
% 1.37/0.55    inference(subsumption_resolution,[],[f169,f48])).
% 1.37/0.55  fof(f48,plain,(
% 1.37/0.55    v1_funct_1(sK1)),
% 1.37/0.55    inference(cnf_transformation,[],[f45])).
% 1.37/0.55  fof(f169,plain,(
% 1.37/0.55    ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 1.37/0.55    inference(subsumption_resolution,[],[f165,f50])).
% 1.37/0.55  fof(f50,plain,(
% 1.37/0.55    v3_funct_2(sK1,sK0,sK0)),
% 1.37/0.55    inference(cnf_transformation,[],[f45])).
% 1.37/0.55  fof(f165,plain,(
% 1.37/0.55    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 1.37/0.55    inference(resolution,[],[f81,f51])).
% 1.37/0.55  fof(f81,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f36])).
% 1.37/0.55  fof(f36,plain,(
% 1.37/0.55    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.55    inference(flattening,[],[f35])).
% 1.37/0.55  fof(f35,plain,(
% 1.37/0.55    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.55    inference(ennf_transformation,[],[f12])).
% 1.37/0.55  fof(f12,axiom,(
% 1.37/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.37/0.55  fof(f488,plain,(
% 1.37/0.55    ~r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0) | (~spl3_1 | ~spl3_15)),
% 1.37/0.55    inference(forward_demodulation,[],[f487,f394])).
% 1.37/0.55  fof(f394,plain,(
% 1.37/0.55    k1_xboole_0 = sK2 | ~spl3_15),
% 1.37/0.55    inference(avatar_component_clause,[],[f392])).
% 1.37/0.55  fof(f392,plain,(
% 1.37/0.55    spl3_15 <=> k1_xboole_0 = sK2),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.37/0.55  fof(f487,plain,(
% 1.37/0.55    ~r2_relset_1(sK0,sK0,sK2,k1_xboole_0) | ~spl3_1),
% 1.37/0.55    inference(forward_demodulation,[],[f486,f265])).
% 1.37/0.55  fof(f265,plain,(
% 1.37/0.55    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.37/0.55    inference(superposition,[],[f249,f87])).
% 1.37/0.55  fof(f249,plain,(
% 1.37/0.55    ( ! [X0] : (k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))) )),
% 1.37/0.55    inference(subsumption_resolution,[],[f248,f92])).
% 1.37/0.55  fof(f248,plain,(
% 1.37/0.55    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) != X0 | k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))) )),
% 1.37/0.55    inference(forward_demodulation,[],[f247,f93])).
% 1.37/0.55  fof(f93,plain,(
% 1.37/0.55    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.37/0.55    inference(definition_unfolding,[],[f66,f59])).
% 1.37/0.55  fof(f66,plain,(
% 1.37/0.55    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.37/0.55    inference(cnf_transformation,[],[f2])).
% 1.37/0.55  fof(f247,plain,(
% 1.37/0.55    ( ! [X0] : (k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) | k2_relat_1(k6_partfun1(X0)) != k1_relat_1(k6_partfun1(X0))) )),
% 1.37/0.55    inference(trivial_inequality_removal,[],[f246])).
% 1.37/0.55  fof(f246,plain,(
% 1.37/0.55    ( ! [X0] : (k6_partfun1(X0) != k6_partfun1(X0) | k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) | k2_relat_1(k6_partfun1(X0)) != k1_relat_1(k6_partfun1(X0))) )),
% 1.37/0.55    inference(forward_demodulation,[],[f245,f92])).
% 1.37/0.55  fof(f245,plain,(
% 1.37/0.55    ( ! [X0] : (k6_partfun1(X0) != k6_partfun1(k2_relat_1(k6_partfun1(X0))) | k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) | k2_relat_1(k6_partfun1(X0)) != k1_relat_1(k6_partfun1(X0))) )),
% 1.37/0.55    inference(subsumption_resolution,[],[f244,f89])).
% 1.37/0.55  fof(f89,plain,(
% 1.37/0.55    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 1.37/0.55    inference(definition_unfolding,[],[f60,f59])).
% 1.37/0.55  fof(f60,plain,(
% 1.37/0.55    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f6])).
% 1.37/0.55  fof(f6,axiom,(
% 1.37/0.55    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.37/0.55  fof(f244,plain,(
% 1.37/0.55    ( ! [X0] : (k6_partfun1(X0) != k6_partfun1(k2_relat_1(k6_partfun1(X0))) | k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) | k2_relat_1(k6_partfun1(X0)) != k1_relat_1(k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0))) )),
% 1.37/0.55    inference(subsumption_resolution,[],[f243,f90])).
% 1.37/0.55  fof(f90,plain,(
% 1.37/0.55    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 1.37/0.55    inference(definition_unfolding,[],[f63,f59])).
% 1.37/0.55  fof(f63,plain,(
% 1.37/0.55    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f5])).
% 1.37/0.55  fof(f5,axiom,(
% 1.37/0.55    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.37/0.55  fof(f243,plain,(
% 1.37/0.55    ( ! [X0] : (k6_partfun1(X0) != k6_partfun1(k2_relat_1(k6_partfun1(X0))) | k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) | k2_relat_1(k6_partfun1(X0)) != k1_relat_1(k6_partfun1(X0)) | ~v1_funct_1(k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0))) )),
% 1.37/0.55    inference(subsumption_resolution,[],[f242,f88])).
% 1.37/0.55  fof(f88,plain,(
% 1.37/0.55    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.37/0.55    inference(definition_unfolding,[],[f61,f59])).
% 1.37/0.55  fof(f61,plain,(
% 1.37/0.55    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f6])).
% 1.37/0.55  fof(f242,plain,(
% 1.37/0.55    ( ! [X0] : (k6_partfun1(X0) != k6_partfun1(k2_relat_1(k6_partfun1(X0))) | k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) | k2_relat_1(k6_partfun1(X0)) != k1_relat_1(k6_partfun1(X0)) | ~v2_funct_1(k6_partfun1(X0)) | ~v1_funct_1(k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0))) )),
% 1.37/0.55    inference(duplicate_literal_removal,[],[f237])).
% 1.37/0.56  % (15514)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.37/0.56  % (15512)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.37/0.56  fof(f237,plain,(
% 1.37/0.56    ( ! [X0] : (k6_partfun1(X0) != k6_partfun1(k2_relat_1(k6_partfun1(X0))) | k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) | k2_relat_1(k6_partfun1(X0)) != k1_relat_1(k6_partfun1(X0)) | ~v2_funct_1(k6_partfun1(X0)) | ~v1_funct_1(k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0)) | ~v1_funct_1(k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0))) )),
% 1.37/0.56    inference(superposition,[],[f95,f132])).
% 1.37/0.56  fof(f132,plain,(
% 1.37/0.56    ( ! [X0] : (k6_partfun1(X0) = k5_relat_1(k6_partfun1(X0),k6_partfun1(X0))) )),
% 1.37/0.56    inference(forward_demodulation,[],[f127,f92])).
% 1.37/0.56  fof(f127,plain,(
% 1.37/0.56    ( ! [X0] : (k6_partfun1(X0) = k5_relat_1(k6_partfun1(X0),k6_partfun1(k2_relat_1(k6_partfun1(X0))))) )),
% 1.37/0.56    inference(resolution,[],[f94,f89])).
% 1.37/0.56  fof(f94,plain,(
% 1.37/0.56    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 1.37/0.56    inference(definition_unfolding,[],[f68,f59])).
% 1.37/0.56  fof(f68,plain,(
% 1.37/0.56    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f23])).
% 1.37/0.56  fof(f23,plain,(
% 1.37/0.56    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.37/0.56    inference(ennf_transformation,[],[f3])).
% 1.37/0.56  fof(f3,axiom,(
% 1.37/0.56    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 1.37/0.56  fof(f95,plain,(
% 1.37/0.56    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.37/0.56    inference(definition_unfolding,[],[f71,f59])).
% 1.37/0.56  fof(f71,plain,(
% 1.37/0.56    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f27])).
% 1.37/0.56  fof(f27,plain,(
% 1.37/0.56    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.37/0.56    inference(flattening,[],[f26])).
% 1.37/0.56  fof(f26,plain,(
% 1.37/0.56    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.37/0.56    inference(ennf_transformation,[],[f7])).
% 1.37/0.56  fof(f7,axiom,(
% 1.37/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.37/0.56  fof(f486,plain,(
% 1.37/0.56    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(k1_xboole_0)) | ~spl3_1),
% 1.37/0.56    inference(forward_demodulation,[],[f234,f187])).
% 1.37/0.56  fof(f234,plain,(
% 1.37/0.56    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 1.37/0.56    inference(backward_demodulation,[],[f57,f215])).
% 1.37/0.56  fof(f215,plain,(
% 1.37/0.56    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.37/0.56    inference(subsumption_resolution,[],[f214,f48])).
% 1.37/0.56  fof(f214,plain,(
% 1.37/0.56    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.37/0.56    inference(subsumption_resolution,[],[f213,f49])).
% 1.37/0.56  fof(f49,plain,(
% 1.37/0.56    v1_funct_2(sK1,sK0,sK0)),
% 1.37/0.56    inference(cnf_transformation,[],[f45])).
% 1.37/0.56  fof(f213,plain,(
% 1.37/0.56    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.37/0.56    inference(subsumption_resolution,[],[f209,f50])).
% 1.37/0.56  fof(f209,plain,(
% 1.37/0.56    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.37/0.56    inference(resolution,[],[f74,f51])).
% 1.37/0.56  fof(f74,plain,(
% 1.37/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f31])).
% 1.37/0.56  fof(f31,plain,(
% 1.37/0.56    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.37/0.56    inference(flattening,[],[f30])).
% 1.37/0.56  fof(f30,plain,(
% 1.37/0.56    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.37/0.56    inference(ennf_transformation,[],[f15])).
% 1.37/0.56  fof(f15,axiom,(
% 1.37/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.37/0.56  fof(f57,plain,(
% 1.37/0.56    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.37/0.56    inference(cnf_transformation,[],[f45])).
% 1.37/0.56  fof(f416,plain,(
% 1.37/0.56    spl3_15 | ~spl3_2),
% 1.37/0.56    inference(avatar_split_clause,[],[f415,f189,f392])).
% 1.37/0.56  fof(f189,plain,(
% 1.37/0.56    spl3_2 <=> k1_xboole_0 = sK0),
% 1.37/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.37/0.56  fof(f415,plain,(
% 1.37/0.56    k1_xboole_0 != sK0 | k1_xboole_0 = sK2),
% 1.37/0.56    inference(subsumption_resolution,[],[f208,f108])).
% 1.37/0.56  fof(f108,plain,(
% 1.37/0.56    v1_relat_1(sK2)),
% 1.37/0.56    inference(resolution,[],[f75,f55])).
% 1.37/0.56  fof(f55,plain,(
% 1.37/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.37/0.56    inference(cnf_transformation,[],[f45])).
% 1.37/0.56  fof(f208,plain,(
% 1.37/0.56    k1_xboole_0 != sK0 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 1.37/0.56    inference(superposition,[],[f70,f178])).
% 1.37/0.56  fof(f178,plain,(
% 1.37/0.56    sK0 = k2_relat_1(sK2)),
% 1.37/0.56    inference(subsumption_resolution,[],[f177,f108])).
% 1.37/0.56  fof(f177,plain,(
% 1.37/0.56    sK0 = k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.37/0.56    inference(subsumption_resolution,[],[f176,f123])).
% 1.37/0.56  fof(f123,plain,(
% 1.37/0.56    v5_relat_1(sK2,sK0)),
% 1.37/0.56    inference(resolution,[],[f78,f55])).
% 1.37/0.56  fof(f176,plain,(
% 1.37/0.56    sK0 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 1.37/0.56    inference(resolution,[],[f172,f72])).
% 1.37/0.56  fof(f172,plain,(
% 1.37/0.56    v2_funct_2(sK2,sK0)),
% 1.37/0.56    inference(subsumption_resolution,[],[f171,f52])).
% 1.37/0.56  fof(f52,plain,(
% 1.37/0.56    v1_funct_1(sK2)),
% 1.37/0.56    inference(cnf_transformation,[],[f45])).
% 1.37/0.56  fof(f171,plain,(
% 1.37/0.56    ~v1_funct_1(sK2) | v2_funct_2(sK2,sK0)),
% 1.37/0.56    inference(subsumption_resolution,[],[f166,f54])).
% 1.37/0.56  fof(f54,plain,(
% 1.37/0.56    v3_funct_2(sK2,sK0,sK0)),
% 1.37/0.56    inference(cnf_transformation,[],[f45])).
% 1.37/0.56  fof(f166,plain,(
% 1.37/0.56    ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | v2_funct_2(sK2,sK0)),
% 1.37/0.56    inference(resolution,[],[f81,f55])).
% 1.37/0.56  fof(f70,plain,(
% 1.37/0.56    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f25])).
% 1.37/0.56  fof(f25,plain,(
% 1.37/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 1.37/0.56    inference(flattening,[],[f24])).
% 1.37/0.56  fof(f24,plain,(
% 1.37/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 1.37/0.56    inference(ennf_transformation,[],[f1])).
% 1.37/0.56  fof(f1,axiom,(
% 1.37/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.37/0.56  fof(f389,plain,(
% 1.37/0.56    spl3_2),
% 1.37/0.56    inference(avatar_contradiction_clause,[],[f388])).
% 1.37/0.56  fof(f388,plain,(
% 1.37/0.56    $false | spl3_2),
% 1.37/0.56    inference(subsumption_resolution,[],[f386,f143])).
% 1.37/0.56  fof(f143,plain,(
% 1.37/0.56    r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.37/0.56    inference(resolution,[],[f98,f55])).
% 1.37/0.56  fof(f386,plain,(
% 1.37/0.56    ~r2_relset_1(sK0,sK0,sK2,sK2) | spl3_2),
% 1.37/0.56    inference(backward_demodulation,[],[f234,f379])).
% 1.37/0.56  fof(f379,plain,(
% 1.37/0.56    sK2 = k2_funct_1(sK1) | spl3_2),
% 1.37/0.56    inference(subsumption_resolution,[],[f378,f52])).
% 1.37/0.56  fof(f378,plain,(
% 1.37/0.56    sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK2) | spl3_2),
% 1.37/0.56    inference(subsumption_resolution,[],[f377,f53])).
% 1.37/0.56  fof(f53,plain,(
% 1.37/0.56    v1_funct_2(sK2,sK0,sK0)),
% 1.37/0.56    inference(cnf_transformation,[],[f45])).
% 1.37/0.56  fof(f377,plain,(
% 1.37/0.56    sK2 = k2_funct_1(sK1) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl3_2),
% 1.37/0.56    inference(subsumption_resolution,[],[f376,f55])).
% 1.37/0.56  fof(f376,plain,(
% 1.37/0.56    sK2 = k2_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl3_2),
% 1.37/0.56    inference(resolution,[],[f326,f56])).
% 1.37/0.56  fof(f56,plain,(
% 1.37/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.37/0.56    inference(cnf_transformation,[],[f45])).
% 1.37/0.56  fof(f326,plain,(
% 1.37/0.56    ( ! [X2] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) | k2_funct_1(sK1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X2,sK0,sK0) | ~v1_funct_1(X2)) ) | spl3_2),
% 1.37/0.56    inference(subsumption_resolution,[],[f325,f48])).
% 1.37/0.56  fof(f325,plain,(
% 1.37/0.56    ( ! [X2] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) | k2_funct_1(sK1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X2,sK0,sK0) | ~v1_funct_1(X2) | ~v1_funct_1(sK1)) ) | spl3_2),
% 1.37/0.56    inference(subsumption_resolution,[],[f324,f49])).
% 1.37/0.56  fof(f324,plain,(
% 1.37/0.56    ( ! [X2] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) | k2_funct_1(sK1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X2,sK0,sK0) | ~v1_funct_1(X2) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) ) | spl3_2),
% 1.37/0.56    inference(subsumption_resolution,[],[f323,f51])).
% 1.37/0.56  fof(f323,plain,(
% 1.37/0.56    ( ! [X2] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) | k2_funct_1(sK1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X2,sK0,sK0) | ~v1_funct_1(X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) ) | spl3_2),
% 1.37/0.56    inference(subsumption_resolution,[],[f317,f191])).
% 1.37/0.56  fof(f191,plain,(
% 1.37/0.56    k1_xboole_0 != sK0 | spl3_2),
% 1.37/0.56    inference(avatar_component_clause,[],[f189])).
% 1.37/0.56  fof(f317,plain,(
% 1.37/0.56    ( ! [X2] : (k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) | k2_funct_1(sK1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X2,sK0,sK0) | ~v1_funct_1(X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 1.37/0.56    inference(trivial_inequality_removal,[],[f316])).
% 1.37/0.56  fof(f316,plain,(
% 1.37/0.56    ( ! [X2] : (sK0 != sK0 | k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) | k2_funct_1(sK1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X2,sK0,sK0) | ~v1_funct_1(X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 1.37/0.56    inference(duplicate_literal_removal,[],[f312])).
% 1.37/0.56  fof(f312,plain,(
% 1.37/0.56    ( ! [X2] : (sK0 != sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) | k2_funct_1(sK1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X2,sK0,sK0) | ~v1_funct_1(X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 1.37/0.56    inference(superposition,[],[f99,f179])).
% 1.37/0.56  fof(f179,plain,(
% 1.37/0.56    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.37/0.56    inference(backward_demodulation,[],[f150,f175])).
% 1.37/0.56  fof(f150,plain,(
% 1.37/0.56    k2_relat_1(sK1) = k2_relset_1(sK0,sK0,sK1)),
% 1.37/0.56    inference(resolution,[],[f76,f51])).
% 1.37/0.56  fof(f76,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f33])).
% 1.37/0.56  fof(f33,plain,(
% 1.37/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.56    inference(ennf_transformation,[],[f10])).
% 1.37/0.56  fof(f10,axiom,(
% 1.37/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.37/0.56  fof(f99,plain,(
% 1.37/0.56    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_funct_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.37/0.56    inference(global_subsumption,[],[f82,f84])).
% 1.37/0.56  fof(f84,plain,(
% 1.37/0.56    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f40])).
% 1.37/0.56  fof(f40,plain,(
% 1.37/0.56    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.37/0.56    inference(flattening,[],[f39])).
% 1.37/0.56  fof(f39,plain,(
% 1.37/0.56    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.37/0.56    inference(ennf_transformation,[],[f18])).
% 1.37/0.56  fof(f18,axiom,(
% 1.37/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.37/0.56  fof(f82,plain,(
% 1.37/0.56    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | v2_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f38])).
% 1.37/0.56  fof(f38,plain,(
% 1.37/0.56    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.37/0.56    inference(flattening,[],[f37])).
% 1.37/0.56  % (15491)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.37/0.56  fof(f37,plain,(
% 1.37/0.56    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.37/0.56    inference(ennf_transformation,[],[f17])).
% 1.37/0.56  fof(f17,axiom,(
% 1.37/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.37/0.56  fof(f192,plain,(
% 1.37/0.56    spl3_1 | ~spl3_2),
% 1.37/0.56    inference(avatar_split_clause,[],[f183,f189,f185])).
% 1.37/0.56  fof(f183,plain,(
% 1.37/0.56    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.37/0.56    inference(subsumption_resolution,[],[f182,f107])).
% 1.37/0.56  fof(f182,plain,(
% 1.37/0.56    k1_xboole_0 != sK0 | k1_xboole_0 = sK1 | ~v1_relat_1(sK1)),
% 1.37/0.56    inference(superposition,[],[f70,f175])).
% 1.37/0.56  % SZS output end Proof for theBenchmark
% 1.37/0.56  % (15496)------------------------------
% 1.37/0.56  % (15496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (15496)Termination reason: Refutation
% 1.37/0.56  
% 1.37/0.56  % (15496)Memory used [KB]: 11001
% 1.37/0.56  % (15496)Time elapsed: 0.148 s
% 1.37/0.56  % (15496)------------------------------
% 1.37/0.56  % (15496)------------------------------
% 1.37/0.56  % (15493)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.37/0.56  % (15501)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.37/0.56  % (15505)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.65/0.57  % (15500)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.65/0.57  % (15489)Success in time 0.217 s
%------------------------------------------------------------------------------
