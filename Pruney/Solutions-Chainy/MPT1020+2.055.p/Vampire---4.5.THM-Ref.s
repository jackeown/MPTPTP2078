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
% DateTime   : Thu Dec  3 13:05:48 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 880 expanded)
%              Number of leaves         :   22 ( 269 expanded)
%              Depth                    :   23
%              Number of atoms          :  667 (6504 expanded)
%              Number of equality atoms :  128 ( 231 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f866,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f535,f579,f624,f632,f709,f717,f865])).

fof(f865,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_12
    | ~ spl5_33 ),
    inference(avatar_contradiction_clause,[],[f864])).

fof(f864,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | spl5_12
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f756,f786])).

fof(f786,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl5_3
    | ~ spl5_33 ),
    inference(forward_demodulation,[],[f623,f148])).

fof(f148,plain,
    ( k1_xboole_0 = sK4
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f623,plain,
    ( k1_xboole_0 = k2_funct_1(sK4)
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f621])).

fof(f621,plain,
    ( spl5_33
  <=> k1_xboole_0 = k2_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f756,plain,
    ( k1_xboole_0 != k2_funct_1(k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_12 ),
    inference(forward_demodulation,[],[f755,f148])).

fof(f755,plain,
    ( sK4 != k2_funct_1(k1_xboole_0)
    | ~ spl5_2
    | spl5_12 ),
    inference(forward_demodulation,[],[f256,f140])).

fof(f140,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f256,plain,
    ( sK4 != k2_funct_1(sK3)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl5_12
  <=> sK4 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f717,plain,
    ( spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f716,f134,f146])).

fof(f134,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f716,plain,
    ( k1_xboole_0 = sK4
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f715,f645])).

fof(f645,plain,
    ( v5_relat_1(sK4,k1_xboole_0)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f87,f135])).

fof(f135,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f87,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f69,f52])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v3_funct_2(sK4,sK2,sK2)
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v3_funct_2(sK3,sK2,sK2)
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f38,f37])).

fof(f37,plain,
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
          ( ~ r2_relset_1(sK2,sK2,X2,k2_funct_2(sK2,sK3))
          & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X2),k6_partfun1(sK2))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
          & v3_funct_2(X2,sK2,sK2)
          & v1_funct_2(X2,sK2,sK2)
          & v1_funct_1(X2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v3_funct_2(sK3,sK2,sK2)
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK2,sK2,X2,k2_funct_2(sK2,sK3))
        & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X2),k6_partfun1(sK2))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
        & v3_funct_2(X2,sK2,sK2)
        & v1_funct_2(X2,sK2,sK2)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))
      & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v3_funct_2(sK4,sK2,sK2)
      & v1_funct_2(sK4,sK2,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f715,plain,
    ( k1_xboole_0 = sK4
    | ~ v5_relat_1(sK4,k1_xboole_0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f712,f83])).

fof(f83,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f81,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f81,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(resolution,[],[f57,f52])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f712,plain,
    ( k1_xboole_0 = sK4
    | ~ v1_relat_1(sK4)
    | ~ v5_relat_1(sK4,k1_xboole_0)
    | ~ spl5_1 ),
    inference(trivial_inequality_removal,[],[f711])).

fof(f711,plain,
    ( k1_xboole_0 = sK4
    | ~ v1_relat_1(sK4)
    | k1_xboole_0 != k1_xboole_0
    | ~ v5_relat_1(sK4,k1_xboole_0)
    | ~ spl5_1 ),
    inference(resolution,[],[f653,f98])).

fof(f98,plain,(
    ! [X2,X3] :
      ( ~ v2_funct_2(X2,X3)
      | k1_xboole_0 = X2
      | ~ v1_relat_1(X2)
      | k1_xboole_0 != X3
      | ~ v5_relat_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = X2
      | ~ v1_relat_1(X2)
      | ~ v2_funct_2(X2,X3)
      | ~ v5_relat_1(X2,X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f56,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f653,plain,
    ( v2_funct_2(sK4,k1_xboole_0)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f127,f135])).

fof(f127,plain,(
    v2_funct_2(sK4,sK2) ),
    inference(resolution,[],[f109,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP1(X1,X2) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP1(X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f109,plain,(
    sP1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f108,f49])).

fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f108,plain,
    ( ~ v1_funct_1(sK4)
    | sP1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f104,f51])).

fof(f51,plain,(
    v3_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f104,plain,
    ( ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | sP1(sK2,sK4) ),
    inference(resolution,[],[f73,f52])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | sP1(X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f28,f35])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f709,plain,
    ( spl5_2
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f708,f134,f138])).

fof(f708,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f707,f644])).

fof(f644,plain,
    ( v5_relat_1(sK3,k1_xboole_0)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f86,f135])).

fof(f86,plain,(
    v5_relat_1(sK3,sK2) ),
    inference(resolution,[],[f69,f48])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f707,plain,
    ( k1_xboole_0 = sK3
    | ~ v5_relat_1(sK3,k1_xboole_0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f704,f82])).

fof(f82,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f80,f58])).

fof(f80,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(resolution,[],[f57,f48])).

fof(f704,plain,
    ( k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ v5_relat_1(sK3,k1_xboole_0)
    | ~ spl5_1 ),
    inference(trivial_inequality_removal,[],[f703])).

fof(f703,plain,
    ( k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 != k1_xboole_0
    | ~ v5_relat_1(sK3,k1_xboole_0)
    | ~ spl5_1 ),
    inference(resolution,[],[f650,f98])).

fof(f650,plain,
    ( v2_funct_2(sK3,k1_xboole_0)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f112,f135])).

fof(f112,plain,(
    v2_funct_2(sK3,sK2) ),
    inference(resolution,[],[f107,f72])).

fof(f107,plain,(
    sP1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f106,f45])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f106,plain,
    ( ~ v1_funct_1(sK3)
    | sP1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f103,f47])).

fof(f47,plain,(
    v3_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f103,plain,
    ( ~ v3_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3)
    | sP1(sK2,sK3) ),
    inference(resolution,[],[f73,f48])).

fof(f632,plain,
    ( ~ spl5_11
    | spl5_12
    | spl5_1 ),
    inference(avatar_split_clause,[],[f631,f134,f255,f251])).

fof(f251,plain,
    ( spl5_11
  <=> sK2 = k2_relset_1(sK2,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f631,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3) ),
    inference(subsumption_resolution,[],[f630,f45])).

fof(f630,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f629,f46])).

fof(f46,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f629,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f628,f48])).

fof(f628,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f627,f49])).

fof(f627,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f626,f50])).

fof(f50,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f626,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f625,f52])).

fof(f625,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f241,f113])).

fof(f113,plain,(
    v2_funct_1(sK3) ),
    inference(resolution,[],[f107,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f241,plain,
    ( k1_xboole_0 = sK2
    | ~ v2_funct_1(sK3)
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK2
    | ~ v2_funct_1(sK3)
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f74,f53])).

fof(f53,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = X3
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f624,plain,
    ( ~ spl5_1
    | spl5_33 ),
    inference(avatar_split_clause,[],[f619,f621,f134])).

fof(f619,plain,
    ( k1_xboole_0 = k2_funct_1(sK4)
    | k1_xboole_0 != sK2 ),
    inference(subsumption_resolution,[],[f618,f236])).

fof(f236,plain,(
    v5_relat_1(k2_funct_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f218,f123])).

fof(f123,plain,(
    sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f122,f49])).

fof(f122,plain,
    ( sP0(sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f121,f50])).

fof(f121,plain,
    ( sP0(sK2,sK4)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f116,f51])).

fof(f116,plain,
    ( sP0(sK2,sK4)
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f66,f52])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | sP0(X0,X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(definition_folding,[],[f24,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f218,plain,
    ( v5_relat_1(k2_funct_1(sK4),sK2)
    | ~ sP0(sK2,sK4) ),
    inference(superposition,[],[f88,f181])).

fof(f181,plain,(
    k2_funct_2(sK2,sK4) = k2_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f180,f49])).

fof(f180,plain,
    ( k2_funct_2(sK2,sK4) = k2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f179,f50])).

fof(f179,plain,
    ( k2_funct_2(sK2,sK4) = k2_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f174,f51])).

fof(f174,plain,
    ( k2_funct_2(sK2,sK4) = k2_funct_1(sK4)
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f61,f52])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f88,plain,(
    ! [X0,X1] :
      ( v5_relat_1(k2_funct_2(X0,X1),X0)
      | ~ sP0(X0,X1) ) ),
    inference(resolution,[],[f65,f69])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f618,plain,
    ( k1_xboole_0 = k2_funct_1(sK4)
    | k1_xboole_0 != sK2
    | ~ v5_relat_1(k2_funct_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f299,f238])).

fof(f238,plain,(
    v1_relat_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f220,f123])).

fof(f220,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ sP0(sK2,sK4) ),
    inference(superposition,[],[f91,f181])).

fof(f91,plain,(
    ! [X4,X5] :
      ( v1_relat_1(k2_funct_2(X4,X5))
      | ~ sP0(X4,X5) ) ),
    inference(subsumption_resolution,[],[f90,f58])).

fof(f90,plain,(
    ! [X4,X5] :
      ( ~ sP0(X4,X5)
      | v1_relat_1(k2_funct_2(X4,X5))
      | ~ v1_relat_1(k2_zfmisc_1(X4,X4)) ) ),
    inference(resolution,[],[f65,f57])).

fof(f299,plain,
    ( k1_xboole_0 = k2_funct_1(sK4)
    | ~ v1_relat_1(k2_funct_1(sK4))
    | k1_xboole_0 != sK2
    | ~ v5_relat_1(k2_funct_1(sK4),sK2) ),
    inference(resolution,[],[f296,f98])).

fof(f296,plain,(
    v2_funct_2(k2_funct_1(sK4),sK2) ),
    inference(resolution,[],[f295,f72])).

fof(f295,plain,(
    sP1(sK2,k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f294,f123])).

fof(f294,plain,
    ( sP1(sK2,k2_funct_1(sK4))
    | ~ sP0(sK2,sK4) ),
    inference(superposition,[],[f111,f181])).

fof(f111,plain,(
    ! [X0,X1] :
      ( sP1(X0,k2_funct_2(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f110,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(k2_funct_2(X0,X1))
      | sP1(X0,k2_funct_2(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f105,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ v1_funct_1(k2_funct_2(X0,X1))
      | sP1(X0,k2_funct_2(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(resolution,[],[f73,f65])).

fof(f579,plain,(
    ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f578])).

fof(f578,plain,
    ( $false
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f547,f93])).

fof(f93,plain,(
    r2_relset_1(sK2,sK2,sK4,sK4) ),
    inference(resolution,[],[f79,f52])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f547,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,sK4)
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f185,f257])).

fof(f257,plain,
    ( sK4 = k2_funct_1(sK3)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f255])).

fof(f185,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f54,f178])).

fof(f178,plain,(
    k2_funct_2(sK2,sK3) = k2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f177,f45])).

fof(f177,plain,
    ( k2_funct_2(sK2,sK3) = k2_funct_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f176,f46])).

fof(f176,plain,
    ( k2_funct_2(sK2,sK3) = k2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f173,f47])).

fof(f173,plain,
    ( k2_funct_2(sK2,sK3) = k2_funct_1(sK3)
    | ~ v3_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f61,f48])).

fof(f54,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f535,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f534])).

fof(f534,plain,
    ( $false
    | spl5_11 ),
    inference(subsumption_resolution,[],[f531,f86])).

fof(f531,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | spl5_11 ),
    inference(resolution,[],[f530,f112])).

fof(f530,plain,
    ( ! [X0] :
        ( ~ v2_funct_2(sK3,X0)
        | ~ v5_relat_1(sK3,X0) )
    | spl5_11 ),
    inference(subsumption_resolution,[],[f529,f82])).

fof(f529,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK3,X0)
        | ~ v2_funct_2(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl5_11 ),
    inference(duplicate_literal_removal,[],[f528])).

fof(f528,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK3,X0)
        | ~ v2_funct_2(sK3,X0)
        | ~ v5_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl5_11 ),
    inference(superposition,[],[f521,f59])).

fof(f521,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | spl5_11 ),
    inference(subsumption_resolution,[],[f520,f82])).

fof(f520,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl5_11 ),
    inference(subsumption_resolution,[],[f519,f260])).

fof(f260,plain,
    ( sK2 != k2_relat_1(sK3)
    | spl5_11 ),
    inference(subsumption_resolution,[],[f259,f48])).

fof(f259,plain,
    ( sK2 != k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | spl5_11 ),
    inference(superposition,[],[f253,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f253,plain,
    ( sK2 != k2_relset_1(sK2,sK2,sK3)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f251])).

fof(f519,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f518])).

fof(f518,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f399,f77])).

fof(f77,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f399,plain,(
    ! [X4] :
      ( ~ v2_funct_2(sK3,X4)
      | sK2 = X4
      | ~ v5_relat_1(sK3,X4) ) ),
    inference(subsumption_resolution,[],[f398,f82])).

fof(f398,plain,(
    ! [X4] :
      ( sK2 = X4
      | ~ v1_relat_1(sK3)
      | ~ v2_funct_2(sK3,X4)
      | ~ v5_relat_1(sK3,X4) ) ),
    inference(subsumption_resolution,[],[f391,f86])).

fof(f391,plain,(
    ! [X4] :
      ( sK2 = X4
      | ~ v5_relat_1(sK3,sK2)
      | ~ v1_relat_1(sK3)
      | ~ v2_funct_2(sK3,X4)
      | ~ v5_relat_1(sK3,X4) ) ),
    inference(resolution,[],[f100,f112])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_2(X0,X2)
      | X1 = X2
      | ~ v5_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_2(X0,X1)
      | ~ v5_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ v2_funct_2(X0,X2)
      | ~ v5_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_2(X0,X1)
      | ~ v5_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f59,f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n017.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 13:00:16 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.46  % (14973)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.18/0.47  % (14978)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.18/0.48  % (14977)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.18/0.48  % (14971)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.18/0.48  % (14970)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.18/0.49  % (14987)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.18/0.49  % (14966)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.18/0.49  % (14980)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.18/0.49  % (14984)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.18/0.49  % (14991)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.18/0.49  % (14988)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.18/0.49  % (14972)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.18/0.49  % (14985)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.18/0.50  % (14982)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.18/0.50  % (14979)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.18/0.50  % (14976)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.18/0.50  % (14981)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.18/0.50  % (14969)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.18/0.51  % (14990)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.18/0.51  % (14970)Refutation found. Thanks to Tanya!
% 0.18/0.51  % SZS status Theorem for theBenchmark
% 0.18/0.51  % SZS output start Proof for theBenchmark
% 0.18/0.51  fof(f866,plain,(
% 0.18/0.51    $false),
% 0.18/0.51    inference(avatar_sat_refutation,[],[f535,f579,f624,f632,f709,f717,f865])).
% 0.18/0.51  fof(f865,plain,(
% 0.18/0.51    ~spl5_2 | ~spl5_3 | spl5_12 | ~spl5_33),
% 0.18/0.51    inference(avatar_contradiction_clause,[],[f864])).
% 0.18/0.51  fof(f864,plain,(
% 0.18/0.51    $false | (~spl5_2 | ~spl5_3 | spl5_12 | ~spl5_33)),
% 0.18/0.51    inference(subsumption_resolution,[],[f756,f786])).
% 0.18/0.51  fof(f786,plain,(
% 0.18/0.51    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl5_3 | ~spl5_33)),
% 0.18/0.51    inference(forward_demodulation,[],[f623,f148])).
% 0.18/0.51  fof(f148,plain,(
% 0.18/0.51    k1_xboole_0 = sK4 | ~spl5_3),
% 0.18/0.51    inference(avatar_component_clause,[],[f146])).
% 0.18/0.51  fof(f146,plain,(
% 0.18/0.51    spl5_3 <=> k1_xboole_0 = sK4),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.18/0.51  fof(f623,plain,(
% 0.18/0.51    k1_xboole_0 = k2_funct_1(sK4) | ~spl5_33),
% 0.18/0.51    inference(avatar_component_clause,[],[f621])).
% 0.18/0.51  fof(f621,plain,(
% 0.18/0.51    spl5_33 <=> k1_xboole_0 = k2_funct_1(sK4)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.18/0.51  fof(f756,plain,(
% 0.18/0.51    k1_xboole_0 != k2_funct_1(k1_xboole_0) | (~spl5_2 | ~spl5_3 | spl5_12)),
% 0.18/0.51    inference(forward_demodulation,[],[f755,f148])).
% 0.18/0.51  fof(f755,plain,(
% 0.18/0.51    sK4 != k2_funct_1(k1_xboole_0) | (~spl5_2 | spl5_12)),
% 0.18/0.51    inference(forward_demodulation,[],[f256,f140])).
% 0.18/0.51  fof(f140,plain,(
% 0.18/0.51    k1_xboole_0 = sK3 | ~spl5_2),
% 0.18/0.51    inference(avatar_component_clause,[],[f138])).
% 0.18/0.51  fof(f138,plain,(
% 0.18/0.51    spl5_2 <=> k1_xboole_0 = sK3),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.18/0.51  fof(f256,plain,(
% 0.18/0.51    sK4 != k2_funct_1(sK3) | spl5_12),
% 0.18/0.51    inference(avatar_component_clause,[],[f255])).
% 0.18/0.51  fof(f255,plain,(
% 0.18/0.51    spl5_12 <=> sK4 = k2_funct_1(sK3)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.18/0.51  fof(f717,plain,(
% 0.18/0.51    spl5_3 | ~spl5_1),
% 0.18/0.51    inference(avatar_split_clause,[],[f716,f134,f146])).
% 0.18/0.51  fof(f134,plain,(
% 0.18/0.51    spl5_1 <=> k1_xboole_0 = sK2),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.18/0.51  fof(f716,plain,(
% 0.18/0.51    k1_xboole_0 = sK4 | ~spl5_1),
% 0.18/0.51    inference(subsumption_resolution,[],[f715,f645])).
% 0.18/0.51  fof(f645,plain,(
% 0.18/0.51    v5_relat_1(sK4,k1_xboole_0) | ~spl5_1),
% 0.18/0.51    inference(backward_demodulation,[],[f87,f135])).
% 0.18/0.51  fof(f135,plain,(
% 0.18/0.51    k1_xboole_0 = sK2 | ~spl5_1),
% 0.18/0.51    inference(avatar_component_clause,[],[f134])).
% 0.18/0.51  fof(f87,plain,(
% 0.18/0.51    v5_relat_1(sK4,sK2)),
% 0.18/0.51    inference(resolution,[],[f69,f52])).
% 0.18/0.51  fof(f52,plain,(
% 0.18/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.18/0.51    inference(cnf_transformation,[],[f39])).
% 0.18/0.51  fof(f39,plain,(
% 0.18/0.51    (~r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK4,sK2,sK2) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK3,sK2,sK2) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 0.18/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f38,f37])).
% 0.18/0.51  fof(f37,plain,(
% 0.18/0.51    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK2,sK2,X2,k2_funct_2(sK2,sK3)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X2),k6_partfun1(sK2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(X2,sK2,sK2) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK3,sK2,sK2) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 0.18/0.51    introduced(choice_axiom,[])).
% 0.18/0.51  fof(f38,plain,(
% 0.18/0.51    ? [X2] : (~r2_relset_1(sK2,sK2,X2,k2_funct_2(sK2,sK3)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X2),k6_partfun1(sK2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(X2,sK2,sK2) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) => (~r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK4,sK2,sK2) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4))),
% 0.18/0.51    introduced(choice_axiom,[])).
% 0.18/0.51  fof(f15,plain,(
% 0.18/0.51    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.18/0.51    inference(flattening,[],[f14])).
% 0.18/0.51  fof(f14,plain,(
% 0.18/0.51    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.18/0.51    inference(ennf_transformation,[],[f13])).
% 0.18/0.51  fof(f13,negated_conjecture,(
% 0.18/0.51    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.18/0.51    inference(negated_conjecture,[],[f12])).
% 0.18/0.51  fof(f12,conjecture,(
% 0.18/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).
% 0.18/0.51  fof(f69,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f26])).
% 0.18/0.51  fof(f26,plain,(
% 0.18/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.51    inference(ennf_transformation,[],[f4])).
% 0.18/0.51  fof(f4,axiom,(
% 0.18/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.18/0.51  fof(f715,plain,(
% 0.18/0.51    k1_xboole_0 = sK4 | ~v5_relat_1(sK4,k1_xboole_0) | ~spl5_1),
% 0.18/0.51    inference(subsumption_resolution,[],[f712,f83])).
% 0.18/0.51  fof(f83,plain,(
% 0.18/0.51    v1_relat_1(sK4)),
% 0.18/0.51    inference(subsumption_resolution,[],[f81,f58])).
% 0.18/0.51  fof(f58,plain,(
% 0.18/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f2])).
% 0.18/0.51  fof(f2,axiom,(
% 0.18/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.18/0.51  fof(f81,plain,(
% 0.18/0.51    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))),
% 0.18/0.51    inference(resolution,[],[f57,f52])).
% 0.18/0.51  fof(f57,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f18])).
% 0.18/0.51  fof(f18,plain,(
% 0.18/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.18/0.51    inference(ennf_transformation,[],[f1])).
% 0.18/0.51  fof(f1,axiom,(
% 0.18/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.18/0.51  fof(f712,plain,(
% 0.18/0.51    k1_xboole_0 = sK4 | ~v1_relat_1(sK4) | ~v5_relat_1(sK4,k1_xboole_0) | ~spl5_1),
% 0.18/0.51    inference(trivial_inequality_removal,[],[f711])).
% 0.18/0.51  fof(f711,plain,(
% 0.18/0.51    k1_xboole_0 = sK4 | ~v1_relat_1(sK4) | k1_xboole_0 != k1_xboole_0 | ~v5_relat_1(sK4,k1_xboole_0) | ~spl5_1),
% 0.18/0.51    inference(resolution,[],[f653,f98])).
% 0.18/0.51  fof(f98,plain,(
% 0.18/0.51    ( ! [X2,X3] : (~v2_funct_2(X2,X3) | k1_xboole_0 = X2 | ~v1_relat_1(X2) | k1_xboole_0 != X3 | ~v5_relat_1(X2,X3)) )),
% 0.18/0.51    inference(duplicate_literal_removal,[],[f97])).
% 0.18/0.51  fof(f97,plain,(
% 0.18/0.51    ( ! [X2,X3] : (k1_xboole_0 != X3 | k1_xboole_0 = X2 | ~v1_relat_1(X2) | ~v2_funct_2(X2,X3) | ~v5_relat_1(X2,X3) | ~v1_relat_1(X2)) )),
% 0.18/0.51    inference(superposition,[],[f56,f59])).
% 0.18/0.51  fof(f59,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f40])).
% 0.18/0.51  fof(f40,plain,(
% 0.18/0.51    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.18/0.51    inference(nnf_transformation,[],[f20])).
% 0.18/0.51  fof(f20,plain,(
% 0.18/0.51    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.18/0.51    inference(flattening,[],[f19])).
% 0.18/0.51  fof(f19,plain,(
% 0.18/0.51    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.18/0.51    inference(ennf_transformation,[],[f8])).
% 0.18/0.51  fof(f8,axiom,(
% 0.18/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.18/0.51  fof(f56,plain,(
% 0.18/0.51    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f17])).
% 0.18/0.51  fof(f17,plain,(
% 0.18/0.51    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 0.18/0.51    inference(flattening,[],[f16])).
% 0.18/0.51  fof(f16,plain,(
% 0.18/0.51    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.18/0.51    inference(ennf_transformation,[],[f3])).
% 0.18/0.51  fof(f3,axiom,(
% 0.18/0.51    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.18/0.51  fof(f653,plain,(
% 0.18/0.51    v2_funct_2(sK4,k1_xboole_0) | ~spl5_1),
% 0.18/0.51    inference(backward_demodulation,[],[f127,f135])).
% 0.18/0.51  fof(f127,plain,(
% 0.18/0.51    v2_funct_2(sK4,sK2)),
% 0.18/0.51    inference(resolution,[],[f109,f72])).
% 0.18/0.51  fof(f72,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~sP1(X0,X1) | v2_funct_2(X1,X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f43])).
% 0.18/0.51  fof(f43,plain,(
% 0.18/0.51    ! [X0,X1] : ((v2_funct_2(X1,X0) & v2_funct_1(X1) & v1_funct_1(X1)) | ~sP1(X0,X1))),
% 0.18/0.51    inference(rectify,[],[f42])).
% 0.18/0.51  fof(f42,plain,(
% 0.18/0.51    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP1(X1,X2))),
% 0.18/0.51    inference(nnf_transformation,[],[f35])).
% 0.18/0.51  fof(f35,plain,(
% 0.18/0.51    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP1(X1,X2))),
% 0.18/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.18/0.51  fof(f109,plain,(
% 0.18/0.51    sP1(sK2,sK4)),
% 0.18/0.51    inference(subsumption_resolution,[],[f108,f49])).
% 0.18/0.51  fof(f49,plain,(
% 0.18/0.51    v1_funct_1(sK4)),
% 0.18/0.51    inference(cnf_transformation,[],[f39])).
% 0.18/0.51  fof(f108,plain,(
% 0.18/0.51    ~v1_funct_1(sK4) | sP1(sK2,sK4)),
% 0.18/0.51    inference(subsumption_resolution,[],[f104,f51])).
% 0.18/0.51  fof(f51,plain,(
% 0.18/0.51    v3_funct_2(sK4,sK2,sK2)),
% 0.18/0.51    inference(cnf_transformation,[],[f39])).
% 0.18/0.51  fof(f104,plain,(
% 0.18/0.51    ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | sP1(sK2,sK4)),
% 0.18/0.51    inference(resolution,[],[f73,f52])).
% 0.18/0.51  fof(f73,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | sP1(X1,X2)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f36])).
% 0.18/0.51  fof(f36,plain,(
% 0.18/0.51    ! [X0,X1,X2] : (sP1(X1,X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.51    inference(definition_folding,[],[f28,f35])).
% 0.18/0.51  fof(f28,plain,(
% 0.18/0.51    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.51    inference(flattening,[],[f27])).
% 0.18/0.51  fof(f27,plain,(
% 0.18/0.51    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.51    inference(ennf_transformation,[],[f7])).
% 0.18/0.51  fof(f7,axiom,(
% 0.18/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.18/0.51  fof(f709,plain,(
% 0.18/0.51    spl5_2 | ~spl5_1),
% 0.18/0.51    inference(avatar_split_clause,[],[f708,f134,f138])).
% 0.18/0.51  fof(f708,plain,(
% 0.18/0.51    k1_xboole_0 = sK3 | ~spl5_1),
% 0.18/0.51    inference(subsumption_resolution,[],[f707,f644])).
% 0.18/0.51  fof(f644,plain,(
% 0.18/0.51    v5_relat_1(sK3,k1_xboole_0) | ~spl5_1),
% 0.18/0.51    inference(backward_demodulation,[],[f86,f135])).
% 0.18/0.51  fof(f86,plain,(
% 0.18/0.51    v5_relat_1(sK3,sK2)),
% 0.18/0.51    inference(resolution,[],[f69,f48])).
% 0.18/0.51  fof(f48,plain,(
% 0.18/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.18/0.51    inference(cnf_transformation,[],[f39])).
% 0.18/0.51  fof(f707,plain,(
% 0.18/0.51    k1_xboole_0 = sK3 | ~v5_relat_1(sK3,k1_xboole_0) | ~spl5_1),
% 0.18/0.51    inference(subsumption_resolution,[],[f704,f82])).
% 0.18/0.51  fof(f82,plain,(
% 0.18/0.51    v1_relat_1(sK3)),
% 0.18/0.51    inference(subsumption_resolution,[],[f80,f58])).
% 0.18/0.51  fof(f80,plain,(
% 0.18/0.51    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))),
% 0.18/0.51    inference(resolution,[],[f57,f48])).
% 0.18/0.51  fof(f704,plain,(
% 0.18/0.51    k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~v5_relat_1(sK3,k1_xboole_0) | ~spl5_1),
% 0.18/0.51    inference(trivial_inequality_removal,[],[f703])).
% 0.18/0.51  fof(f703,plain,(
% 0.18/0.51    k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | k1_xboole_0 != k1_xboole_0 | ~v5_relat_1(sK3,k1_xboole_0) | ~spl5_1),
% 0.18/0.51    inference(resolution,[],[f650,f98])).
% 0.18/0.51  fof(f650,plain,(
% 0.18/0.51    v2_funct_2(sK3,k1_xboole_0) | ~spl5_1),
% 0.18/0.51    inference(backward_demodulation,[],[f112,f135])).
% 0.18/0.51  fof(f112,plain,(
% 0.18/0.51    v2_funct_2(sK3,sK2)),
% 0.18/0.51    inference(resolution,[],[f107,f72])).
% 0.18/0.51  fof(f107,plain,(
% 0.18/0.51    sP1(sK2,sK3)),
% 0.18/0.51    inference(subsumption_resolution,[],[f106,f45])).
% 0.18/0.51  fof(f45,plain,(
% 0.18/0.51    v1_funct_1(sK3)),
% 0.18/0.51    inference(cnf_transformation,[],[f39])).
% 0.18/0.51  fof(f106,plain,(
% 0.18/0.51    ~v1_funct_1(sK3) | sP1(sK2,sK3)),
% 0.18/0.51    inference(subsumption_resolution,[],[f103,f47])).
% 0.18/0.51  fof(f47,plain,(
% 0.18/0.51    v3_funct_2(sK3,sK2,sK2)),
% 0.18/0.51    inference(cnf_transformation,[],[f39])).
% 0.18/0.51  fof(f103,plain,(
% 0.18/0.51    ~v3_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3) | sP1(sK2,sK3)),
% 0.18/0.51    inference(resolution,[],[f73,f48])).
% 0.18/0.51  fof(f632,plain,(
% 0.18/0.51    ~spl5_11 | spl5_12 | spl5_1),
% 0.18/0.51    inference(avatar_split_clause,[],[f631,f134,f255,f251])).
% 0.18/0.51  fof(f251,plain,(
% 0.18/0.51    spl5_11 <=> sK2 = k2_relset_1(sK2,sK2,sK3)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.18/0.51  fof(f631,plain,(
% 0.18/0.51    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3)),
% 0.18/0.51    inference(subsumption_resolution,[],[f630,f45])).
% 0.18/0.51  fof(f630,plain,(
% 0.18/0.51    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~v1_funct_1(sK3)),
% 0.18/0.51    inference(subsumption_resolution,[],[f629,f46])).
% 0.18/0.51  fof(f46,plain,(
% 0.18/0.51    v1_funct_2(sK3,sK2,sK2)),
% 0.18/0.51    inference(cnf_transformation,[],[f39])).
% 0.18/0.51  fof(f629,plain,(
% 0.18/0.51    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.18/0.51    inference(subsumption_resolution,[],[f628,f48])).
% 0.18/0.51  fof(f628,plain,(
% 0.18/0.51    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.18/0.51    inference(subsumption_resolution,[],[f627,f49])).
% 0.18/0.51  fof(f627,plain,(
% 0.18/0.51    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.18/0.51    inference(subsumption_resolution,[],[f626,f50])).
% 0.18/0.51  fof(f50,plain,(
% 0.18/0.51    v1_funct_2(sK4,sK2,sK2)),
% 0.18/0.51    inference(cnf_transformation,[],[f39])).
% 0.18/0.51  fof(f626,plain,(
% 0.18/0.51    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.18/0.51    inference(subsumption_resolution,[],[f625,f52])).
% 0.18/0.51  fof(f625,plain,(
% 0.18/0.51    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.18/0.51    inference(subsumption_resolution,[],[f241,f113])).
% 0.18/0.51  fof(f113,plain,(
% 0.18/0.51    v2_funct_1(sK3)),
% 0.18/0.51    inference(resolution,[],[f107,f71])).
% 0.18/0.51  fof(f71,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~sP1(X0,X1) | v2_funct_1(X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f43])).
% 0.18/0.51  fof(f241,plain,(
% 0.18/0.51    k1_xboole_0 = sK2 | ~v2_funct_1(sK3) | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.18/0.51    inference(duplicate_literal_removal,[],[f240])).
% 0.18/0.51  fof(f240,plain,(
% 0.18/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | ~v2_funct_1(sK3) | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.18/0.51    inference(resolution,[],[f74,f53])).
% 0.18/0.51  fof(f53,plain,(
% 0.18/0.51    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2))),
% 0.18/0.51    inference(cnf_transformation,[],[f39])).
% 0.18/0.51  fof(f74,plain,(
% 0.18/0.51    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | k2_funct_1(X2) = X3 | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f30])).
% 0.18/0.51  fof(f30,plain,(
% 0.18/0.51    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.18/0.51    inference(flattening,[],[f29])).
% 0.18/0.51  fof(f29,plain,(
% 0.18/0.51    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.18/0.51    inference(ennf_transformation,[],[f11])).
% 0.18/0.51  fof(f11,axiom,(
% 0.18/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 0.18/0.51  fof(f624,plain,(
% 0.18/0.51    ~spl5_1 | spl5_33),
% 0.18/0.51    inference(avatar_split_clause,[],[f619,f621,f134])).
% 0.18/0.51  fof(f619,plain,(
% 0.18/0.51    k1_xboole_0 = k2_funct_1(sK4) | k1_xboole_0 != sK2),
% 0.18/0.51    inference(subsumption_resolution,[],[f618,f236])).
% 0.18/0.51  fof(f236,plain,(
% 0.18/0.51    v5_relat_1(k2_funct_1(sK4),sK2)),
% 0.18/0.51    inference(subsumption_resolution,[],[f218,f123])).
% 0.18/0.51  fof(f123,plain,(
% 0.18/0.51    sP0(sK2,sK4)),
% 0.18/0.51    inference(subsumption_resolution,[],[f122,f49])).
% 0.18/0.51  fof(f122,plain,(
% 0.18/0.51    sP0(sK2,sK4) | ~v1_funct_1(sK4)),
% 0.18/0.51    inference(subsumption_resolution,[],[f121,f50])).
% 0.18/0.51  fof(f121,plain,(
% 0.18/0.51    sP0(sK2,sK4) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.18/0.51    inference(subsumption_resolution,[],[f116,f51])).
% 0.18/0.51  fof(f116,plain,(
% 0.18/0.51    sP0(sK2,sK4) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.18/0.51    inference(resolution,[],[f66,f52])).
% 0.18/0.51  fof(f66,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | sP0(X0,X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f34])).
% 0.18/0.51  fof(f34,plain,(
% 0.18/0.51    ! [X0,X1] : (sP0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.18/0.51    inference(definition_folding,[],[f24,f33])).
% 0.18/0.51  fof(f33,plain,(
% 0.18/0.51    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~sP0(X0,X1))),
% 0.18/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.18/0.51  fof(f24,plain,(
% 0.18/0.51    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.18/0.51    inference(flattening,[],[f23])).
% 0.18/0.51  fof(f23,plain,(
% 0.18/0.51    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.18/0.51    inference(ennf_transformation,[],[f9])).
% 0.18/0.51  fof(f9,axiom,(
% 0.18/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.18/0.51  fof(f218,plain,(
% 0.18/0.51    v5_relat_1(k2_funct_1(sK4),sK2) | ~sP0(sK2,sK4)),
% 0.18/0.51    inference(superposition,[],[f88,f181])).
% 0.18/0.51  fof(f181,plain,(
% 0.18/0.51    k2_funct_2(sK2,sK4) = k2_funct_1(sK4)),
% 0.18/0.51    inference(subsumption_resolution,[],[f180,f49])).
% 0.18/0.51  fof(f180,plain,(
% 0.18/0.51    k2_funct_2(sK2,sK4) = k2_funct_1(sK4) | ~v1_funct_1(sK4)),
% 0.18/0.51    inference(subsumption_resolution,[],[f179,f50])).
% 0.18/0.51  fof(f179,plain,(
% 0.18/0.51    k2_funct_2(sK2,sK4) = k2_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.18/0.51    inference(subsumption_resolution,[],[f174,f51])).
% 0.18/0.51  fof(f174,plain,(
% 0.18/0.51    k2_funct_2(sK2,sK4) = k2_funct_1(sK4) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.18/0.51    inference(resolution,[],[f61,f52])).
% 0.18/0.51  fof(f61,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f22])).
% 0.18/0.51  fof(f22,plain,(
% 0.18/0.51    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.18/0.51    inference(flattening,[],[f21])).
% 0.18/0.51  fof(f21,plain,(
% 0.18/0.51    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.18/0.51    inference(ennf_transformation,[],[f10])).
% 0.18/0.51  fof(f10,axiom,(
% 0.18/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.18/0.51  fof(f88,plain,(
% 0.18/0.51    ( ! [X0,X1] : (v5_relat_1(k2_funct_2(X0,X1),X0) | ~sP0(X0,X1)) )),
% 0.18/0.51    inference(resolution,[],[f65,f69])).
% 0.18/0.51  fof(f65,plain,(
% 0.18/0.51    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~sP0(X0,X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f41])).
% 0.18/0.51  fof(f41,plain,(
% 0.18/0.51    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~sP0(X0,X1))),
% 0.18/0.51    inference(nnf_transformation,[],[f33])).
% 0.18/0.51  fof(f618,plain,(
% 0.18/0.51    k1_xboole_0 = k2_funct_1(sK4) | k1_xboole_0 != sK2 | ~v5_relat_1(k2_funct_1(sK4),sK2)),
% 0.18/0.51    inference(subsumption_resolution,[],[f299,f238])).
% 0.18/0.51  fof(f238,plain,(
% 0.18/0.51    v1_relat_1(k2_funct_1(sK4))),
% 0.18/0.51    inference(subsumption_resolution,[],[f220,f123])).
% 0.18/0.51  fof(f220,plain,(
% 0.18/0.51    v1_relat_1(k2_funct_1(sK4)) | ~sP0(sK2,sK4)),
% 0.18/0.51    inference(superposition,[],[f91,f181])).
% 0.18/0.51  fof(f91,plain,(
% 0.18/0.51    ( ! [X4,X5] : (v1_relat_1(k2_funct_2(X4,X5)) | ~sP0(X4,X5)) )),
% 0.18/0.51    inference(subsumption_resolution,[],[f90,f58])).
% 0.18/0.51  fof(f90,plain,(
% 0.18/0.51    ( ! [X4,X5] : (~sP0(X4,X5) | v1_relat_1(k2_funct_2(X4,X5)) | ~v1_relat_1(k2_zfmisc_1(X4,X4))) )),
% 0.18/0.51    inference(resolution,[],[f65,f57])).
% 0.18/0.51  fof(f299,plain,(
% 0.18/0.51    k1_xboole_0 = k2_funct_1(sK4) | ~v1_relat_1(k2_funct_1(sK4)) | k1_xboole_0 != sK2 | ~v5_relat_1(k2_funct_1(sK4),sK2)),
% 0.18/0.51    inference(resolution,[],[f296,f98])).
% 0.18/0.51  fof(f296,plain,(
% 0.18/0.51    v2_funct_2(k2_funct_1(sK4),sK2)),
% 0.18/0.51    inference(resolution,[],[f295,f72])).
% 0.18/0.51  fof(f295,plain,(
% 0.18/0.51    sP1(sK2,k2_funct_1(sK4))),
% 0.18/0.51    inference(subsumption_resolution,[],[f294,f123])).
% 0.18/0.51  fof(f294,plain,(
% 0.18/0.51    sP1(sK2,k2_funct_1(sK4)) | ~sP0(sK2,sK4)),
% 0.18/0.51    inference(superposition,[],[f111,f181])).
% 0.18/0.51  fof(f111,plain,(
% 0.18/0.51    ( ! [X0,X1] : (sP1(X0,k2_funct_2(X0,X1)) | ~sP0(X0,X1)) )),
% 0.18/0.51    inference(subsumption_resolution,[],[f110,f62])).
% 0.18/0.51  fof(f62,plain,(
% 0.18/0.51    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~sP0(X0,X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f41])).
% 0.18/0.51  fof(f110,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~v1_funct_1(k2_funct_2(X0,X1)) | sP1(X0,k2_funct_2(X0,X1)) | ~sP0(X0,X1)) )),
% 0.18/0.51    inference(subsumption_resolution,[],[f105,f64])).
% 0.18/0.51  fof(f64,plain,(
% 0.18/0.51    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~sP0(X0,X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f41])).
% 0.18/0.51  fof(f105,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~v1_funct_1(k2_funct_2(X0,X1)) | sP1(X0,k2_funct_2(X0,X1)) | ~sP0(X0,X1)) )),
% 0.18/0.51    inference(resolution,[],[f73,f65])).
% 0.18/0.51  fof(f579,plain,(
% 0.18/0.51    ~spl5_12),
% 0.18/0.51    inference(avatar_contradiction_clause,[],[f578])).
% 0.18/0.51  fof(f578,plain,(
% 0.18/0.51    $false | ~spl5_12),
% 0.18/0.51    inference(subsumption_resolution,[],[f547,f93])).
% 0.18/0.51  fof(f93,plain,(
% 0.18/0.51    r2_relset_1(sK2,sK2,sK4,sK4)),
% 0.18/0.51    inference(resolution,[],[f79,f52])).
% 0.18/0.51  fof(f79,plain,(
% 0.18/0.51    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.18/0.51    inference(duplicate_literal_removal,[],[f78])).
% 0.18/0.51  fof(f78,plain,(
% 0.18/0.51    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.51    inference(equality_resolution,[],[f76])).
% 0.18/0.51  fof(f76,plain,(
% 0.18/0.51    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f44])).
% 0.18/0.51  fof(f44,plain,(
% 0.18/0.51    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.51    inference(nnf_transformation,[],[f32])).
% 0.18/0.51  fof(f32,plain,(
% 0.18/0.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.51    inference(flattening,[],[f31])).
% 0.18/0.51  fof(f31,plain,(
% 0.18/0.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.18/0.51    inference(ennf_transformation,[],[f6])).
% 0.18/0.51  fof(f6,axiom,(
% 0.18/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.18/0.51  fof(f547,plain,(
% 0.18/0.51    ~r2_relset_1(sK2,sK2,sK4,sK4) | ~spl5_12),
% 0.18/0.51    inference(backward_demodulation,[],[f185,f257])).
% 0.18/0.51  fof(f257,plain,(
% 0.18/0.51    sK4 = k2_funct_1(sK3) | ~spl5_12),
% 0.18/0.51    inference(avatar_component_clause,[],[f255])).
% 0.18/0.51  fof(f185,plain,(
% 0.18/0.51    ~r2_relset_1(sK2,sK2,sK4,k2_funct_1(sK3))),
% 0.18/0.51    inference(backward_demodulation,[],[f54,f178])).
% 0.18/0.51  fof(f178,plain,(
% 0.18/0.51    k2_funct_2(sK2,sK3) = k2_funct_1(sK3)),
% 0.18/0.51    inference(subsumption_resolution,[],[f177,f45])).
% 0.18/0.51  fof(f177,plain,(
% 0.18/0.51    k2_funct_2(sK2,sK3) = k2_funct_1(sK3) | ~v1_funct_1(sK3)),
% 0.18/0.51    inference(subsumption_resolution,[],[f176,f46])).
% 0.18/0.51  fof(f176,plain,(
% 0.18/0.51    k2_funct_2(sK2,sK3) = k2_funct_1(sK3) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.18/0.51    inference(subsumption_resolution,[],[f173,f47])).
% 0.18/0.51  fof(f173,plain,(
% 0.18/0.51    k2_funct_2(sK2,sK3) = k2_funct_1(sK3) | ~v3_funct_2(sK3,sK2,sK2) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.18/0.51    inference(resolution,[],[f61,f48])).
% 0.18/0.51  fof(f54,plain,(
% 0.18/0.51    ~r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))),
% 0.18/0.51    inference(cnf_transformation,[],[f39])).
% 0.18/0.51  fof(f535,plain,(
% 0.18/0.51    spl5_11),
% 0.18/0.51    inference(avatar_contradiction_clause,[],[f534])).
% 0.18/0.51  fof(f534,plain,(
% 0.18/0.51    $false | spl5_11),
% 0.18/0.51    inference(subsumption_resolution,[],[f531,f86])).
% 0.18/0.51  fof(f531,plain,(
% 0.18/0.51    ~v5_relat_1(sK3,sK2) | spl5_11),
% 0.18/0.51    inference(resolution,[],[f530,f112])).
% 0.18/0.51  fof(f530,plain,(
% 0.18/0.51    ( ! [X0] : (~v2_funct_2(sK3,X0) | ~v5_relat_1(sK3,X0)) ) | spl5_11),
% 0.18/0.51    inference(subsumption_resolution,[],[f529,f82])).
% 0.18/0.51  fof(f529,plain,(
% 0.18/0.51    ( ! [X0] : (~v5_relat_1(sK3,X0) | ~v2_funct_2(sK3,X0) | ~v1_relat_1(sK3)) ) | spl5_11),
% 0.18/0.51    inference(duplicate_literal_removal,[],[f528])).
% 0.18/0.51  fof(f528,plain,(
% 0.18/0.51    ( ! [X0] : (~v5_relat_1(sK3,X0) | ~v2_funct_2(sK3,X0) | ~v5_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | spl5_11),
% 0.18/0.51    inference(superposition,[],[f521,f59])).
% 0.18/0.51  fof(f521,plain,(
% 0.18/0.51    ~v5_relat_1(sK3,k2_relat_1(sK3)) | spl5_11),
% 0.18/0.51    inference(subsumption_resolution,[],[f520,f82])).
% 0.18/0.51  fof(f520,plain,(
% 0.18/0.51    ~v5_relat_1(sK3,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | spl5_11),
% 0.18/0.51    inference(subsumption_resolution,[],[f519,f260])).
% 0.18/0.51  fof(f260,plain,(
% 0.18/0.51    sK2 != k2_relat_1(sK3) | spl5_11),
% 0.18/0.51    inference(subsumption_resolution,[],[f259,f48])).
% 0.18/0.51  fof(f259,plain,(
% 0.18/0.51    sK2 != k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | spl5_11),
% 0.18/0.51    inference(superposition,[],[f253,f67])).
% 0.18/0.51  fof(f67,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f25])).
% 0.18/0.51  fof(f25,plain,(
% 0.18/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.51    inference(ennf_transformation,[],[f5])).
% 0.18/0.51  fof(f5,axiom,(
% 0.18/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.18/0.51  fof(f253,plain,(
% 0.18/0.51    sK2 != k2_relset_1(sK2,sK2,sK3) | spl5_11),
% 0.18/0.51    inference(avatar_component_clause,[],[f251])).
% 0.18/0.51  fof(f519,plain,(
% 0.18/0.51    sK2 = k2_relat_1(sK3) | ~v5_relat_1(sK3,k2_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.18/0.51    inference(duplicate_literal_removal,[],[f518])).
% 0.18/0.51  fof(f518,plain,(
% 0.18/0.51    sK2 = k2_relat_1(sK3) | ~v5_relat_1(sK3,k2_relat_1(sK3)) | ~v5_relat_1(sK3,k2_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.18/0.51    inference(resolution,[],[f399,f77])).
% 0.18/0.51  fof(f77,plain,(
% 0.18/0.51    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.18/0.51    inference(equality_resolution,[],[f60])).
% 0.18/0.51  fof(f60,plain,(
% 0.18/0.51    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f40])).
% 0.18/0.51  fof(f399,plain,(
% 0.18/0.51    ( ! [X4] : (~v2_funct_2(sK3,X4) | sK2 = X4 | ~v5_relat_1(sK3,X4)) )),
% 0.18/0.51    inference(subsumption_resolution,[],[f398,f82])).
% 0.18/0.51  fof(f398,plain,(
% 0.18/0.51    ( ! [X4] : (sK2 = X4 | ~v1_relat_1(sK3) | ~v2_funct_2(sK3,X4) | ~v5_relat_1(sK3,X4)) )),
% 0.18/0.51    inference(subsumption_resolution,[],[f391,f86])).
% 0.18/0.51  fof(f391,plain,(
% 0.18/0.51    ( ! [X4] : (sK2 = X4 | ~v5_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | ~v2_funct_2(sK3,X4) | ~v5_relat_1(sK3,X4)) )),
% 0.18/0.51    inference(resolution,[],[f100,f112])).
% 0.18/0.51  fof(f100,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (~v2_funct_2(X0,X2) | X1 = X2 | ~v5_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v2_funct_2(X0,X1) | ~v5_relat_1(X0,X1)) )),
% 0.18/0.51    inference(duplicate_literal_removal,[],[f95])).
% 0.18/0.51  fof(f95,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (X1 = X2 | ~v2_funct_2(X0,X2) | ~v5_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v2_funct_2(X0,X1) | ~v5_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.18/0.51    inference(superposition,[],[f59,f59])).
% 0.18/0.51  % SZS output end Proof for theBenchmark
% 0.18/0.51  % (14970)------------------------------
% 0.18/0.51  % (14970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (14970)Termination reason: Refutation
% 0.18/0.51  
% 0.18/0.51  % (14970)Memory used [KB]: 6396
% 0.18/0.51  % (14970)Time elapsed: 0.104 s
% 0.18/0.51  % (14970)------------------------------
% 0.18/0.51  % (14970)------------------------------
% 0.18/0.51  % (14968)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.18/0.51  % (14963)Success in time 0.167 s
%------------------------------------------------------------------------------
