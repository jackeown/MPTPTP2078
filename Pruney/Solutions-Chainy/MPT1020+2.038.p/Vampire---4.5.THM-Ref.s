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
% DateTime   : Thu Dec  3 13:05:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  179 (1079 expanded)
%              Number of leaves         :   25 ( 326 expanded)
%              Depth                    :   27
%              Number of atoms          :  656 (7148 expanded)
%              Number of equality atoms :  162 ( 484 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f531,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f181,f250,f385,f405,f470,f475,f530])).

fof(f530,plain,
    ( ~ spl3_1
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(avatar_contradiction_clause,[],[f529])).

fof(f529,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f528,f133])).

fof(f133,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f90,f98])).

fof(f98,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f60,f97])).

fof(f97,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_partfun1(X0) ) ),
    inference(subsumption_resolution,[],[f95,f83])).

fof(f83,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f56,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f95,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_partfun1(X0)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f64,f85])).

fof(f85,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f61,f56])).

fof(f61,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f64,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f60,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

% (20241)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f39,plain,(
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

fof(f528,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f497,f482])).

fof(f482,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f481,f97])).

fof(f481,plain,
    ( k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f480,f427])).

fof(f427,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f417,f100])).

fof(f100,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f84,f97])).

fof(f84,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f62,f56])).

fof(f62,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f417,plain,
    ( sK0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f164,f176])).

fof(f176,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f164,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f163,f92])).

fof(f92,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f70,f49])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f42,f41])).

fof(f41,plain,
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

fof(f42,plain,
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f163,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f162,f109])).

fof(f109,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f73,f49])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f162,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f159,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f159,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f158,f46])).

fof(f46,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f158,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f154,f48])).

fof(f48,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f154,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(resolution,[],[f76,f49])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f480,plain,
    ( k6_partfun1(sK0) = k2_funct_1(k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f245,f176])).

fof(f245,plain,
    ( k6_partfun1(sK0) = k2_funct_1(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl3_8
  <=> k6_partfun1(sK0) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f497,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0))
    | ~ spl3_1
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f496,f427])).

fof(f496,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_xboole_0,k2_funct_1(k1_xboole_0))
    | ~ spl3_1
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f495,f404])).

fof(f404,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl3_23
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f495,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(k1_xboole_0))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f225,f176])).

fof(f225,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f55,f204])).

fof(f204,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f203,f46])).

fof(f203,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f202,f47])).

fof(f47,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f202,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f198,f48])).

fof(f198,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f69,f49])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f55,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f475,plain,
    ( ~ spl3_1
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | ~ spl3_1
    | spl3_9 ),
    inference(subsumption_resolution,[],[f473,f97])).

fof(f473,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | ~ spl3_1
    | spl3_9 ),
    inference(forward_demodulation,[],[f472,f99])).

fof(f99,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f85,f97])).

fof(f472,plain,
    ( k1_xboole_0 != k6_partfun1(k1_relat_1(k1_xboole_0))
    | ~ spl3_1
    | spl3_9 ),
    inference(forward_demodulation,[],[f249,f176])).

fof(f249,plain,
    ( sK1 != k6_partfun1(k1_relat_1(sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl3_9
  <=> sK1 = k6_partfun1(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f470,plain,
    ( ~ spl3_1
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | ~ spl3_1
    | spl3_7 ),
    inference(subsumption_resolution,[],[f468,f406])).

fof(f406,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f46,f176])).

fof(f468,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_1
    | spl3_7 ),
    inference(forward_demodulation,[],[f460,f97])).

fof(f460,plain,
    ( ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl3_1
    | spl3_7 ),
    inference(backward_demodulation,[],[f241,f427])).

fof(f241,plain,
    ( ~ v1_funct_1(k6_partfun1(sK0))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl3_7
  <=> v1_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f405,plain,
    ( spl3_23
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f400,f178,f402])).

fof(f178,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f400,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f197,f93])).

fof(f93,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f70,f53])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f197,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f65,f167])).

fof(f167,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f166,f93])).

fof(f166,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f165,f110])).

fof(f110,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f73,f53])).

fof(f165,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f161,f67])).

fof(f161,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f160,f50])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f160,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f155,f52])).

fof(f52,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f155,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0) ),
    inference(resolution,[],[f76,f53])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f385,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f382,f131])).

fof(f131,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f90,f53])).

fof(f382,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | spl3_2 ),
    inference(backward_demodulation,[],[f225,f380])).

fof(f380,plain,
    ( sK2 = k2_funct_1(sK1)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f379,f50])).

fof(f379,plain,
    ( sK2 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f378,f51])).

fof(f51,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f378,plain,
    ( sK2 = k2_funct_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f377,f53])).

fof(f377,plain,
    ( sK2 = k2_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl3_2 ),
    inference(resolution,[],[f337,f54])).

fof(f54,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f337,plain,
    ( ! [X2] :
        ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        | k2_funct_1(sK1) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ v1_funct_1(X2) )
    | spl3_2 ),
    inference(subsumption_resolution,[],[f336,f46])).

fof(f336,plain,
    ( ! [X2] :
        ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        | k2_funct_1(sK1) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(sK1) )
    | spl3_2 ),
    inference(subsumption_resolution,[],[f335,f47])).

fof(f335,plain,
    ( ! [X2] :
        ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        | k2_funct_1(sK1) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(sK1,sK0,sK0)
        | ~ v1_funct_1(sK1) )
    | spl3_2 ),
    inference(subsumption_resolution,[],[f334,f49])).

fof(f334,plain,
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
    inference(subsumption_resolution,[],[f330,f180])).

fof(f180,plain,
    ( k1_xboole_0 != sK0
    | spl3_2 ),
    inference(avatar_component_clause,[],[f178])).

fof(f330,plain,(
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
    inference(trivial_inequality_removal,[],[f329])).

fof(f329,plain,(
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
    inference(duplicate_literal_removal,[],[f325])).

fof(f325,plain,(
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
    inference(superposition,[],[f91,f168])).

fof(f168,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(backward_demodulation,[],[f139,f164])).

fof(f139,plain,(
    k2_relat_1(sK1) = k2_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f71,f49])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f91,plain,(
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
    inference(global_subsumption,[],[f77,f79])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | v2_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f250,plain,
    ( ~ spl3_7
    | spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f237,f247,f243,f239])).

fof(f237,plain,
    ( sK1 != k6_partfun1(k1_relat_1(sK1))
    | k6_partfun1(sK0) = k2_funct_1(sK1)
    | ~ v1_funct_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f236,f164])).

fof(f236,plain,
    ( sK0 != k2_relat_1(sK1)
    | sK1 != k6_partfun1(k1_relat_1(sK1))
    | k6_partfun1(sK0) = k2_funct_1(sK1)
    | ~ v1_funct_1(k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f235,f85])).

fof(f235,plain,
    ( sK1 != k6_partfun1(k1_relat_1(sK1))
    | k6_partfun1(sK0) = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(k6_partfun1(sK0))
    | ~ v1_funct_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f234,f92])).

fof(f234,plain,
    ( sK1 != k6_partfun1(k1_relat_1(sK1))
    | k6_partfun1(sK0) = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(k6_partfun1(sK0))
    | ~ v1_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f233,f46])).

fof(f233,plain,
    ( sK1 != k6_partfun1(k1_relat_1(sK1))
    | k6_partfun1(sK0) = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(k6_partfun1(sK0))
    | ~ v1_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f232,f83])).

fof(f232,plain,
    ( sK1 != k6_partfun1(k1_relat_1(sK1))
    | k6_partfun1(sK0) = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(k6_partfun1(sK0))
    | ~ v1_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f228,f150])).

fof(f150,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f149,f46])).

fof(f149,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f145,f48])).

fof(f145,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f75,f49])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f228,plain,
    ( sK1 != k6_partfun1(k1_relat_1(sK1))
    | k6_partfun1(sK0) = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(k6_partfun1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f87,f169])).

fof(f169,plain,(
    sK1 = k5_relat_1(sK1,k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f114,f164])).

fof(f114,plain,(
    sK1 = k5_relat_1(sK1,k6_partfun1(k2_relat_1(sK1))) ),
    inference(resolution,[],[f86,f92])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f63,f56])).

fof(f63,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f87,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f66,f56])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
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
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f181,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f172,f178,f174])).

fof(f172,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f171,f92])).

fof(f171,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f65,f164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:45:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (20236)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (20260)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (20238)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (20244)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (20247)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (20240)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (20260)Refutation not found, incomplete strategy% (20260)------------------------------
% 0.21/0.52  % (20260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20259)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (20262)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (20251)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (20242)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (20246)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (20260)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20260)Memory used [KB]: 10746
% 0.21/0.53  % (20260)Time elapsed: 0.115 s
% 0.21/0.53  % (20260)------------------------------
% 0.21/0.53  % (20260)------------------------------
% 0.21/0.53  % (20237)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (20264)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (20237)Refutation not found, incomplete strategy% (20237)------------------------------
% 0.21/0.53  % (20237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20237)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20237)Memory used [KB]: 1791
% 0.21/0.53  % (20237)Time elapsed: 0.128 s
% 0.21/0.53  % (20237)------------------------------
% 0.21/0.53  % (20237)------------------------------
% 0.21/0.54  % (20239)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (20265)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (20265)Refutation not found, incomplete strategy% (20265)------------------------------
% 0.21/0.54  % (20265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20265)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20265)Memory used [KB]: 1663
% 0.21/0.54  % (20265)Time elapsed: 0.002 s
% 0.21/0.54  % (20265)------------------------------
% 0.21/0.54  % (20265)------------------------------
% 0.21/0.54  % (20252)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (20254)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (20243)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (20252)Refutation not found, incomplete strategy% (20252)------------------------------
% 0.21/0.54  % (20252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20261)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (20257)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (20254)Refutation not found, incomplete strategy% (20254)------------------------------
% 0.21/0.54  % (20254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20253)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (20249)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (20262)Refutation not found, incomplete strategy% (20262)------------------------------
% 0.21/0.55  % (20262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (20245)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (20263)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (20255)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (20258)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (20262)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (20262)Memory used [KB]: 6396
% 0.21/0.55  % (20262)Time elapsed: 0.154 s
% 0.21/0.55  % (20262)------------------------------
% 0.21/0.55  % (20262)------------------------------
% 0.21/0.55  % (20254)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (20254)Memory used [KB]: 1791
% 0.21/0.55  % (20254)Time elapsed: 0.147 s
% 0.21/0.55  % (20254)------------------------------
% 0.21/0.55  % (20254)------------------------------
% 0.21/0.56  % (20247)Refutation not found, incomplete strategy% (20247)------------------------------
% 0.21/0.56  % (20247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20247)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (20247)Memory used [KB]: 6524
% 0.21/0.56  % (20247)Time elapsed: 0.144 s
% 0.21/0.56  % (20247)------------------------------
% 0.21/0.56  % (20247)------------------------------
% 0.21/0.56  % (20250)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (20246)Refutation not found, incomplete strategy% (20246)------------------------------
% 0.21/0.56  % (20246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20255)Refutation not found, incomplete strategy% (20255)------------------------------
% 0.21/0.56  % (20255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20250)Refutation not found, incomplete strategy% (20250)------------------------------
% 0.21/0.56  % (20250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20250)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (20250)Memory used [KB]: 1791
% 0.21/0.56  % (20250)Time elapsed: 0.159 s
% 0.21/0.56  % (20250)------------------------------
% 0.21/0.56  % (20250)------------------------------
% 0.21/0.56  % (20263)Refutation not found, incomplete strategy% (20263)------------------------------
% 0.21/0.56  % (20263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20248)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (20248)Refutation not found, incomplete strategy% (20248)------------------------------
% 0.21/0.56  % (20248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20252)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  % (20246)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  
% 0.21/0.56  % (20252)Memory used [KB]: 10746
% 0.21/0.56  % (20252)Time elapsed: 0.138 s
% 0.21/0.56  % (20252)------------------------------
% 0.21/0.56  % (20252)------------------------------
% 0.21/0.56  % (20246)Memory used [KB]: 11129
% 0.21/0.56  % (20246)Time elapsed: 0.161 s
% 0.21/0.56  % (20246)------------------------------
% 0.21/0.56  % (20246)------------------------------
% 0.21/0.57  % (20264)Refutation not found, incomplete strategy% (20264)------------------------------
% 0.21/0.57  % (20264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (20264)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (20264)Memory used [KB]: 11129
% 0.21/0.57  % (20264)Time elapsed: 0.132 s
% 0.21/0.57  % (20264)------------------------------
% 0.21/0.57  % (20264)------------------------------
% 0.21/0.57  % (20248)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  % (20263)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (20263)Memory used [KB]: 6268
% 0.21/0.57  % (20263)Time elapsed: 0.152 s
% 0.21/0.57  % (20263)------------------------------
% 0.21/0.57  % (20263)------------------------------
% 0.21/0.57  
% 0.21/0.57  % (20248)Memory used [KB]: 10746
% 0.21/0.57  % (20248)Time elapsed: 0.134 s
% 0.21/0.57  % (20248)------------------------------
% 0.21/0.57  % (20248)------------------------------
% 0.21/0.57  % (20255)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (20255)Memory used [KB]: 1791
% 0.21/0.57  % (20255)Time elapsed: 0.154 s
% 0.21/0.57  % (20255)------------------------------
% 0.21/0.57  % (20255)------------------------------
% 0.21/0.57  % (20242)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f531,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f181,f250,f385,f405,f470,f475,f530])).
% 0.21/0.57  fof(f530,plain,(
% 0.21/0.57    ~spl3_1 | ~spl3_8 | ~spl3_23),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f529])).
% 0.21/0.57  fof(f529,plain,(
% 0.21/0.57    $false | (~spl3_1 | ~spl3_8 | ~spl3_23)),
% 0.21/0.57    inference(subsumption_resolution,[],[f528,f133])).
% 0.21/0.57  fof(f133,plain,(
% 0.21/0.57    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.57    inference(resolution,[],[f90,f98])).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.57    inference(superposition,[],[f60,f97])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.21/0.57    inference(equality_resolution,[],[f96])).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_partfun1(X0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f95,f83])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f57,f56])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.57  fof(f95,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_partfun1(X0) | ~v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.57    inference(superposition,[],[f64,f85])).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.57    inference(definition_unfolding,[],[f61,f56])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X0] : (k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f89])).
% 0.21/0.57  fof(f89,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.57    inference(equality_resolution,[],[f81])).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(nnf_transformation,[],[f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(flattening,[],[f39])).
% 0.21/0.57  % (20241)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.57  fof(f528,plain,(
% 0.21/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_1 | ~spl3_8 | ~spl3_23)),
% 0.21/0.57    inference(forward_demodulation,[],[f497,f482])).
% 0.21/0.57  fof(f482,plain,(
% 0.21/0.57    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_1 | ~spl3_8)),
% 0.21/0.57    inference(forward_demodulation,[],[f481,f97])).
% 0.21/0.57  fof(f481,plain,(
% 0.21/0.57    k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0) | (~spl3_1 | ~spl3_8)),
% 0.21/0.57    inference(forward_demodulation,[],[f480,f427])).
% 0.21/0.57  fof(f427,plain,(
% 0.21/0.57    k1_xboole_0 = sK0 | ~spl3_1),
% 0.21/0.57    inference(forward_demodulation,[],[f417,f100])).
% 0.21/0.57  fof(f100,plain,(
% 0.21/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(superposition,[],[f84,f97])).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.57    inference(definition_unfolding,[],[f62,f56])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f417,plain,(
% 0.21/0.57    sK0 = k2_relat_1(k1_xboole_0) | ~spl3_1),
% 0.21/0.57    inference(backward_demodulation,[],[f164,f176])).
% 0.21/0.57  fof(f176,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | ~spl3_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f174])).
% 0.21/0.57  fof(f174,plain,(
% 0.21/0.57    spl3_1 <=> k1_xboole_0 = sK1),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.57  fof(f164,plain,(
% 0.21/0.57    sK0 = k2_relat_1(sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f163,f92])).
% 0.21/0.57  fof(f92,plain,(
% 0.21/0.57    v1_relat_1(sK1)),
% 0.21/0.57    inference(resolution,[],[f70,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f42,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.57    inference(flattening,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.21/0.57    inference(negated_conjecture,[],[f17])).
% 0.21/0.57  fof(f17,conjecture,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.57  fof(f163,plain,(
% 0.21/0.57    sK0 = k2_relat_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f162,f109])).
% 0.21/0.57  fof(f109,plain,(
% 0.21/0.57    v5_relat_1(sK1,sK0)),
% 0.21/0.57    inference(resolution,[],[f73,f49])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.57  fof(f162,plain,(
% 0.21/0.57    sK0 = k2_relat_1(sK1) | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 0.21/0.57    inference(resolution,[],[f159,f67])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.21/0.57  fof(f159,plain,(
% 0.21/0.57    v2_funct_2(sK1,sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f158,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    v1_funct_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f43])).
% 0.21/0.57  fof(f158,plain,(
% 0.21/0.57    ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f154,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    v3_funct_2(sK1,sK0,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f43])).
% 0.21/0.57  fof(f154,plain,(
% 0.21/0.57    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 0.21/0.57    inference(resolution,[],[f76,f49])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(flattening,[],[f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.21/0.57  fof(f480,plain,(
% 0.21/0.57    k6_partfun1(sK0) = k2_funct_1(k1_xboole_0) | (~spl3_1 | ~spl3_8)),
% 0.21/0.57    inference(forward_demodulation,[],[f245,f176])).
% 0.21/0.57  fof(f245,plain,(
% 0.21/0.57    k6_partfun1(sK0) = k2_funct_1(sK1) | ~spl3_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f243])).
% 0.21/0.57  fof(f243,plain,(
% 0.21/0.57    spl3_8 <=> k6_partfun1(sK0) = k2_funct_1(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.57  fof(f497,plain,(
% 0.21/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) | (~spl3_1 | ~spl3_23)),
% 0.21/0.57    inference(forward_demodulation,[],[f496,f427])).
% 0.21/0.57  fof(f496,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,k1_xboole_0,k2_funct_1(k1_xboole_0)) | (~spl3_1 | ~spl3_23)),
% 0.21/0.57    inference(forward_demodulation,[],[f495,f404])).
% 0.21/0.57  fof(f404,plain,(
% 0.21/0.57    k1_xboole_0 = sK2 | ~spl3_23),
% 0.21/0.57    inference(avatar_component_clause,[],[f402])).
% 0.21/0.57  fof(f402,plain,(
% 0.21/0.57    spl3_23 <=> k1_xboole_0 = sK2),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.57  fof(f495,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(k1_xboole_0)) | ~spl3_1),
% 0.21/0.57    inference(forward_demodulation,[],[f225,f176])).
% 0.21/0.57  fof(f225,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 0.21/0.57    inference(backward_demodulation,[],[f55,f204])).
% 0.21/0.57  fof(f204,plain,(
% 0.21/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f203,f46])).
% 0.21/0.57  fof(f203,plain,(
% 0.21/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f202,f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f43])).
% 0.21/0.57  fof(f202,plain,(
% 0.21/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f198,f48])).
% 0.21/0.57  fof(f198,plain,(
% 0.21/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.57    inference(resolution,[],[f69,f49])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.57    inference(flattening,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 0.21/0.57    inference(cnf_transformation,[],[f43])).
% 0.21/0.57  fof(f475,plain,(
% 0.21/0.57    ~spl3_1 | spl3_9),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f474])).
% 0.21/0.57  fof(f474,plain,(
% 0.21/0.57    $false | (~spl3_1 | spl3_9)),
% 0.21/0.57    inference(subsumption_resolution,[],[f473,f97])).
% 0.21/0.57  fof(f473,plain,(
% 0.21/0.57    k1_xboole_0 != k6_partfun1(k1_xboole_0) | (~spl3_1 | spl3_9)),
% 0.21/0.57    inference(forward_demodulation,[],[f472,f99])).
% 0.21/0.57  fof(f99,plain,(
% 0.21/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(superposition,[],[f85,f97])).
% 0.21/0.57  fof(f472,plain,(
% 0.21/0.57    k1_xboole_0 != k6_partfun1(k1_relat_1(k1_xboole_0)) | (~spl3_1 | spl3_9)),
% 0.21/0.57    inference(forward_demodulation,[],[f249,f176])).
% 0.21/0.57  fof(f249,plain,(
% 0.21/0.57    sK1 != k6_partfun1(k1_relat_1(sK1)) | spl3_9),
% 0.21/0.57    inference(avatar_component_clause,[],[f247])).
% 0.21/0.57  fof(f247,plain,(
% 0.21/0.57    spl3_9 <=> sK1 = k6_partfun1(k1_relat_1(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.57  fof(f470,plain,(
% 0.21/0.57    ~spl3_1 | spl3_7),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f469])).
% 0.21/0.57  fof(f469,plain,(
% 0.21/0.57    $false | (~spl3_1 | spl3_7)),
% 0.21/0.57    inference(subsumption_resolution,[],[f468,f406])).
% 0.21/0.57  fof(f406,plain,(
% 0.21/0.57    v1_funct_1(k1_xboole_0) | ~spl3_1),
% 0.21/0.57    inference(backward_demodulation,[],[f46,f176])).
% 0.21/0.57  fof(f468,plain,(
% 0.21/0.57    ~v1_funct_1(k1_xboole_0) | (~spl3_1 | spl3_7)),
% 0.21/0.57    inference(forward_demodulation,[],[f460,f97])).
% 0.21/0.57  fof(f460,plain,(
% 0.21/0.57    ~v1_funct_1(k6_partfun1(k1_xboole_0)) | (~spl3_1 | spl3_7)),
% 0.21/0.57    inference(backward_demodulation,[],[f241,f427])).
% 0.21/0.57  fof(f241,plain,(
% 0.21/0.57    ~v1_funct_1(k6_partfun1(sK0)) | spl3_7),
% 0.21/0.57    inference(avatar_component_clause,[],[f239])).
% 0.21/0.57  fof(f239,plain,(
% 0.21/0.57    spl3_7 <=> v1_funct_1(k6_partfun1(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.57  fof(f405,plain,(
% 0.21/0.57    spl3_23 | ~spl3_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f400,f178,f402])).
% 0.21/0.57  fof(f178,plain,(
% 0.21/0.57    spl3_2 <=> k1_xboole_0 = sK0),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.57  fof(f400,plain,(
% 0.21/0.57    k1_xboole_0 != sK0 | k1_xboole_0 = sK2),
% 0.21/0.57    inference(subsumption_resolution,[],[f197,f93])).
% 0.21/0.57  fof(f93,plain,(
% 0.21/0.57    v1_relat_1(sK2)),
% 0.21/0.57    inference(resolution,[],[f70,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f43])).
% 0.21/0.57  fof(f197,plain,(
% 0.21/0.57    k1_xboole_0 != sK0 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 0.21/0.57    inference(superposition,[],[f65,f167])).
% 0.21/0.57  fof(f167,plain,(
% 0.21/0.57    sK0 = k2_relat_1(sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f166,f93])).
% 0.21/0.57  fof(f166,plain,(
% 0.21/0.57    sK0 = k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f165,f110])).
% 0.21/0.57  fof(f110,plain,(
% 0.21/0.57    v5_relat_1(sK2,sK0)),
% 0.21/0.57    inference(resolution,[],[f73,f53])).
% 0.21/0.57  fof(f165,plain,(
% 0.21/0.57    sK0 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.21/0.57    inference(resolution,[],[f161,f67])).
% 0.21/0.57  fof(f161,plain,(
% 0.21/0.57    v2_funct_2(sK2,sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f160,f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    v1_funct_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f43])).
% 0.21/0.57  fof(f160,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | v2_funct_2(sK2,sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f155,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    v3_funct_2(sK2,sK0,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f43])).
% 0.21/0.57  fof(f155,plain,(
% 0.21/0.57    ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | v2_funct_2(sK2,sK0)),
% 0.21/0.57    inference(resolution,[],[f76,f53])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f385,plain,(
% 0.21/0.57    spl3_2),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f384])).
% 0.21/0.57  fof(f384,plain,(
% 0.21/0.57    $false | spl3_2),
% 0.21/0.57    inference(subsumption_resolution,[],[f382,f131])).
% 0.21/0.57  fof(f131,plain,(
% 0.21/0.57    r2_relset_1(sK0,sK0,sK2,sK2)),
% 0.21/0.57    inference(resolution,[],[f90,f53])).
% 0.21/0.57  fof(f382,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,sK2,sK2) | spl3_2),
% 0.21/0.57    inference(backward_demodulation,[],[f225,f380])).
% 0.21/0.57  fof(f380,plain,(
% 0.21/0.57    sK2 = k2_funct_1(sK1) | spl3_2),
% 0.21/0.57    inference(subsumption_resolution,[],[f379,f50])).
% 0.21/0.57  fof(f379,plain,(
% 0.21/0.57    sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK2) | spl3_2),
% 0.21/0.57    inference(subsumption_resolution,[],[f378,f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    v1_funct_2(sK2,sK0,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f43])).
% 0.21/0.57  fof(f378,plain,(
% 0.21/0.57    sK2 = k2_funct_1(sK1) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl3_2),
% 0.21/0.57    inference(subsumption_resolution,[],[f377,f53])).
% 0.21/0.57  fof(f377,plain,(
% 0.21/0.57    sK2 = k2_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl3_2),
% 0.21/0.57    inference(resolution,[],[f337,f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 0.21/0.57    inference(cnf_transformation,[],[f43])).
% 0.21/0.57  fof(f337,plain,(
% 0.21/0.57    ( ! [X2] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) | k2_funct_1(sK1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X2,sK0,sK0) | ~v1_funct_1(X2)) ) | spl3_2),
% 0.21/0.57    inference(subsumption_resolution,[],[f336,f46])).
% 0.21/0.57  fof(f336,plain,(
% 0.21/0.57    ( ! [X2] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) | k2_funct_1(sK1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X2,sK0,sK0) | ~v1_funct_1(X2) | ~v1_funct_1(sK1)) ) | spl3_2),
% 0.21/0.57    inference(subsumption_resolution,[],[f335,f47])).
% 0.21/0.57  fof(f335,plain,(
% 0.21/0.57    ( ! [X2] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) | k2_funct_1(sK1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X2,sK0,sK0) | ~v1_funct_1(X2) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) ) | spl3_2),
% 0.21/0.57    inference(subsumption_resolution,[],[f334,f49])).
% 0.21/0.57  fof(f334,plain,(
% 0.21/0.57    ( ! [X2] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) | k2_funct_1(sK1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X2,sK0,sK0) | ~v1_funct_1(X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) ) | spl3_2),
% 0.21/0.57    inference(subsumption_resolution,[],[f330,f180])).
% 0.21/0.57  fof(f180,plain,(
% 0.21/0.57    k1_xboole_0 != sK0 | spl3_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f178])).
% 0.21/0.57  fof(f330,plain,(
% 0.21/0.57    ( ! [X2] : (k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) | k2_funct_1(sK1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X2,sK0,sK0) | ~v1_funct_1(X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f329])).
% 0.21/0.57  fof(f329,plain,(
% 0.21/0.57    ( ! [X2] : (sK0 != sK0 | k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) | k2_funct_1(sK1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X2,sK0,sK0) | ~v1_funct_1(X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f325])).
% 0.21/0.57  fof(f325,plain,(
% 0.21/0.57    ( ! [X2] : (sK0 != sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) | k2_funct_1(sK1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X2,sK0,sK0) | ~v1_funct_1(X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 0.21/0.57    inference(superposition,[],[f91,f168])).
% 0.21/0.57  fof(f168,plain,(
% 0.21/0.57    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 0.21/0.57    inference(backward_demodulation,[],[f139,f164])).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    k2_relat_1(sK1) = k2_relset_1(sK0,sK0,sK1)),
% 0.21/0.57    inference(resolution,[],[f71,f49])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.57  fof(f91,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_funct_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.57    inference(global_subsumption,[],[f77,f79])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.57    inference(flattening,[],[f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | v2_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.57    inference(flattening,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 0.21/0.57  fof(f250,plain,(
% 0.21/0.57    ~spl3_7 | spl3_8 | ~spl3_9),
% 0.21/0.57    inference(avatar_split_clause,[],[f237,f247,f243,f239])).
% 0.21/0.57  fof(f237,plain,(
% 0.21/0.57    sK1 != k6_partfun1(k1_relat_1(sK1)) | k6_partfun1(sK0) = k2_funct_1(sK1) | ~v1_funct_1(k6_partfun1(sK0))),
% 0.21/0.57    inference(subsumption_resolution,[],[f236,f164])).
% 0.21/0.57  fof(f236,plain,(
% 0.21/0.57    sK0 != k2_relat_1(sK1) | sK1 != k6_partfun1(k1_relat_1(sK1)) | k6_partfun1(sK0) = k2_funct_1(sK1) | ~v1_funct_1(k6_partfun1(sK0))),
% 0.21/0.57    inference(forward_demodulation,[],[f235,f85])).
% 0.21/0.57  fof(f235,plain,(
% 0.21/0.57    sK1 != k6_partfun1(k1_relat_1(sK1)) | k6_partfun1(sK0) = k2_funct_1(sK1) | k2_relat_1(sK1) != k1_relat_1(k6_partfun1(sK0)) | ~v1_funct_1(k6_partfun1(sK0))),
% 0.21/0.57    inference(subsumption_resolution,[],[f234,f92])).
% 0.21/0.57  fof(f234,plain,(
% 0.21/0.57    sK1 != k6_partfun1(k1_relat_1(sK1)) | k6_partfun1(sK0) = k2_funct_1(sK1) | k2_relat_1(sK1) != k1_relat_1(k6_partfun1(sK0)) | ~v1_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f233,f46])).
% 0.21/0.57  fof(f233,plain,(
% 0.21/0.57    sK1 != k6_partfun1(k1_relat_1(sK1)) | k6_partfun1(sK0) = k2_funct_1(sK1) | k2_relat_1(sK1) != k1_relat_1(k6_partfun1(sK0)) | ~v1_funct_1(k6_partfun1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f232,f83])).
% 0.21/0.57  fof(f232,plain,(
% 0.21/0.57    sK1 != k6_partfun1(k1_relat_1(sK1)) | k6_partfun1(sK0) = k2_funct_1(sK1) | k2_relat_1(sK1) != k1_relat_1(k6_partfun1(sK0)) | ~v1_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(k6_partfun1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f228,f150])).
% 0.21/0.57  fof(f150,plain,(
% 0.21/0.57    v2_funct_1(sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f149,f46])).
% 0.21/0.57  fof(f149,plain,(
% 0.21/0.57    ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f145,f48])).
% 0.21/0.57  fof(f145,plain,(
% 0.21/0.57    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 0.21/0.57    inference(resolution,[],[f75,f49])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f228,plain,(
% 0.21/0.57    sK1 != k6_partfun1(k1_relat_1(sK1)) | k6_partfun1(sK0) = k2_funct_1(sK1) | k2_relat_1(sK1) != k1_relat_1(k6_partfun1(sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(k6_partfun1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.57    inference(superposition,[],[f87,f169])).
% 0.21/0.57  fof(f169,plain,(
% 0.21/0.57    sK1 = k5_relat_1(sK1,k6_partfun1(sK0))),
% 0.21/0.57    inference(backward_demodulation,[],[f114,f164])).
% 0.21/0.57  fof(f114,plain,(
% 0.21/0.57    sK1 = k5_relat_1(sK1,k6_partfun1(k2_relat_1(sK1)))),
% 0.21/0.57    inference(resolution,[],[f86,f92])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 0.21/0.57    inference(definition_unfolding,[],[f63,f56])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.57  fof(f87,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k2_funct_1(X0) = X1 | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f66,f56])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 0.21/0.57  fof(f181,plain,(
% 0.21/0.57    spl3_1 | ~spl3_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f172,f178,f174])).
% 0.21/0.57  fof(f172,plain,(
% 0.21/0.57    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 0.21/0.57    inference(subsumption_resolution,[],[f171,f92])).
% 0.21/0.57  fof(f171,plain,(
% 0.21/0.57    k1_xboole_0 != sK0 | k1_xboole_0 = sK1 | ~v1_relat_1(sK1)),
% 0.21/0.57    inference(superposition,[],[f65,f164])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (20242)------------------------------
% 0.21/0.57  % (20242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (20242)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (20242)Memory used [KB]: 11001
% 0.21/0.57  % (20242)Time elapsed: 0.168 s
% 0.21/0.57  % (20242)------------------------------
% 0.21/0.57  % (20242)------------------------------
% 0.21/0.57  % (20235)Success in time 0.208 s
%------------------------------------------------------------------------------
