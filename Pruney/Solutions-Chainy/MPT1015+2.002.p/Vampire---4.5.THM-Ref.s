%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:25 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  234 (3557 expanded)
%              Number of leaves         :   38 (1106 expanded)
%              Depth                    :   27
%              Number of atoms          :  802 (26431 expanded)
%              Number of equality atoms :  182 (1082 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2276,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f183,f308,f391,f457,f461,f617,f2000,f2020,f2201,f2255])).

fof(f2255,plain,
    ( ~ spl5_2
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f2254])).

fof(f2254,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f2211,f211])).

fof(f211,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f127,f83])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & v2_funct_1(sK1)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f71,f70])).

fof(f70,plain,
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

fof(f71,plain,
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
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
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).

fof(f127,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
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

fof(f2211,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(superposition,[],[f86,f2207])).

fof(f2207,plain,
    ( k6_partfun1(sK0) = sK2
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f2206,f2060])).

fof(f2060,plain,
    ( sK2 = k5_relat_1(sK2,sK2)
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f2059,f1698])).

fof(f1698,plain,
    ( sK2 = k6_relat_1(sK0)
    | ~ spl5_13 ),
    inference(global_subsumption,[],[f689,f1688])).

fof(f1688,plain,
    ( sK1 = k5_relat_1(sK2,sK1)
    | ~ spl5_13 ),
    inference(superposition,[],[f307,f600])).

fof(f600,plain,(
    k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f595,f81])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f595,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f336,f83])).

fof(f336,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f331,f78])).

fof(f78,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f72])).

fof(f331,plain,(
    ! [X2,X0,X1] :
      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f122,f80])).

fof(f80,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f72])).

fof(f122,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f307,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl5_13
  <=> sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f689,plain,
    ( sK2 = k6_relat_1(sK0)
    | sK1 != k5_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f688,f178])).

fof(f178,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f110,f83])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f688,plain,
    ( sK2 = k6_relat_1(sK0)
    | sK1 != k5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f687,f81])).

fof(f687,plain,
    ( sK2 = k6_relat_1(sK0)
    | sK1 != k5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f686,f474])).

fof(f474,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(superposition,[],[f223,f275])).

fof(f275,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f274,f78])).

fof(f274,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f269,f79])).

fof(f79,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f269,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f109,f80])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f223,plain,(
    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f111,f80])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f686,plain,
    ( sK2 = k6_relat_1(sK0)
    | sK1 != k5_relat_1(sK2,sK1)
    | sK0 != k1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f656,f483])).

fof(f483,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(superposition,[],[f297,f255])).

fof(f255,plain,(
    k2_relat_1(sK2) = k7_relset_1(sK0,sK0,sK2,sK0) ),
    inference(forward_demodulation,[],[f250,f229])).

fof(f229,plain,(
    k2_relat_1(sK2) = k2_relset_1(sK0,sK0,sK2) ),
    inference(resolution,[],[f112,f83])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f250,plain,(
    k2_relset_1(sK0,sK0,sK2) = k7_relset_1(sK0,sK0,sK2,sK0) ),
    inference(resolution,[],[f113,f83])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f297,plain,(
    ! [X1] : r1_tarski(k7_relset_1(sK0,sK0,sK2,X1),sK0) ),
    inference(subsumption_resolution,[],[f296,f81])).

fof(f296,plain,(
    ! [X1] :
      ( r1_tarski(k7_relset_1(sK0,sK0,sK2,X1),sK0)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f290,f82])).

fof(f82,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f290,plain,(
    ! [X1] :
      ( r1_tarski(k7_relset_1(sK0,sK0,sK2,X1),sK0)
      | ~ v1_funct_2(sK2,sK0,sK0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f119,f83])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_2)).

fof(f656,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | sK2 = k6_relat_1(sK0)
    | sK1 != k5_relat_1(sK2,sK1)
    | sK0 != k1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f404,f476])).

fof(f476,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(superposition,[],[f224,f277])).

fof(f277,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK2) ),
    inference(subsumption_resolution,[],[f276,f81])).

fof(f276,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f270,f82])).

fof(f270,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f109,f83])).

fof(f224,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2) ),
    inference(resolution,[],[f111,f83])).

fof(f404,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
      | k6_relat_1(k1_relat_1(X0)) = X0
      | sK1 != k5_relat_1(X0,sK1)
      | k1_relat_1(X0) != k1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f403,f177])).

fof(f177,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f110,f80])).

fof(f403,plain,(
    ! [X0] :
      ( sK1 != k5_relat_1(X0,sK1)
      | k6_relat_1(k1_relat_1(X0)) = X0
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f401,f78])).

fof(f401,plain,(
    ! [X0] :
      ( sK1 != k5_relat_1(X0,sK1)
      | k6_relat_1(k1_relat_1(X0)) = X0
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f125,f85])).

fof(f85,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f72])).

fof(f125,plain,(
    ! [X2,X1] :
      ( ~ v2_funct_1(X1)
      | k5_relat_1(X2,X1) != X1
      | k6_relat_1(k1_relat_1(X2)) = X2
      | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X2))
      | k1_relat_1(X1) != k1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k6_relat_1(X0) = X2
      | k5_relat_1(X2,X1) != X1
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),X0)
      | k1_relat_1(X2) != X0
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k6_relat_1(X0) = X2
          | k5_relat_1(X2,X1) != X1
          | ~ v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X0
          | k1_relat_1(X1) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k6_relat_1(X0) = X2
          | k5_relat_1(X2,X1) != X1
          | ~ v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X0
          | k1_relat_1(X1) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

fof(f2059,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK2)
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f2034,f2018])).

fof(f2018,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f2017,f476])).

fof(f2017,plain,
    ( k1_relat_1(sK2) = k2_relat_1(sK2)
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f2016,f1729])).

fof(f1729,plain,
    ( sK2 = k2_funct_1(sK2)
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f1728,f1698])).

fof(f1728,plain,
    ( k6_relat_1(sK0) = k2_funct_1(k6_relat_1(sK0))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1727,f474])).

fof(f1727,plain,
    ( k6_relat_1(k1_relat_1(sK1)) = k2_funct_1(k6_relat_1(k1_relat_1(sK1)))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1726,f244])).

fof(f244,plain,(
    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f243,f177])).

fof(f243,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f241,f78])).

fof(f241,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f101,f85])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f1726,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k2_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1725,f177])).

fof(f1725,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k2_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1722,f78])).

fof(f1722,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k2_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f448,f85])).

fof(f448,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | k2_funct_1(k5_relat_1(X0,k2_funct_1(sK1))) = k5_relat_1(sK1,k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f447,f209])).

fof(f209,plain,(
    sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f208,f177])).

fof(f208,plain,
    ( sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f206,f78])).

fof(f206,plain,
    ( sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f96,f85])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f447,plain,
    ( ! [X0] :
        ( k2_funct_1(k5_relat_1(X0,k2_funct_1(sK1))) = k5_relat_1(k2_funct_1(k2_funct_1(sK1)),k2_funct_1(X0))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f446,f137])).

fof(f137,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl5_2
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f446,plain,(
    ! [X0] :
      ( k2_funct_1(k5_relat_1(X0,k2_funct_1(sK1))) = k5_relat_1(k2_funct_1(k2_funct_1(sK1)),k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f415,f186])).

fof(f186,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f148,f177])).

fof(f148,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f95,f78])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f415,plain,(
    ! [X0] :
      ( k2_funct_1(k5_relat_1(X0,k2_funct_1(sK1))) = k5_relat_1(k2_funct_1(k2_funct_1(sK1)),k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(k2_funct_1(sK1))
      | ~ v1_relat_1(k2_funct_1(sK1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f195,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).

fof(f195,plain,(
    v2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f194,f177])).

fof(f194,plain,
    ( v2_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f192,f78])).

fof(f192,plain,
    ( v2_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f93,f85])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f2016,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f2015,f178])).

fof(f2015,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f1989,f81])).

fof(f1989,plain,
    ( ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_13 ),
    inference(superposition,[],[f220,f1698])).

fof(f220,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) = k2_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f98,f87])).

fof(f87,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f98,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f2034,plain,
    ( k5_relat_1(sK2,sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f2033,f1729])).

fof(f2033,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f2032,f178])).

fof(f2032,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f1993,f81])).

fof(f1993,plain,
    ( ~ v1_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_13 ),
    inference(superposition,[],[f246,f1698])).

fof(f246,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_relat_1(X0))
      | k5_relat_1(k2_funct_1(k6_relat_1(X0)),k6_relat_1(X0)) = k6_relat_1(k2_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f102,f87])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2206,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK2)
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f382,f1729])).

fof(f382,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f380])).

fof(f380,plain,
    ( spl5_17
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f86,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f72])).

fof(f2201,plain,
    ( ~ spl5_15
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f2200])).

fof(f2200,plain,
    ( $false
    | ~ spl5_15
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f2139,f460])).

fof(f460,plain,
    ( ! [X5] : ~ r2_hidden(X5,k1_xboole_0)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl5_20
  <=> ! [X5] : ~ r2_hidden(X5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f2139,plain,
    ( r2_hidden(sK4(k1_xboole_0,sK2,k6_partfun1(k1_xboole_0)),k1_xboole_0)
    | ~ spl5_15 ),
    inference(superposition,[],[f742,f370])).

fof(f370,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f368])).

fof(f368,plain,
    ( spl5_15
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f742,plain,(
    r2_hidden(sK4(sK0,sK2,k6_partfun1(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f729,f86])).

fof(f729,plain,
    ( r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    | r2_hidden(sK4(sK0,sK2,k6_partfun1(sK0)),sK0) ),
    inference(resolution,[],[f321,f83])).

fof(f321,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
      | r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | r2_hidden(sK4(X2,X3,k6_partfun1(X2)),X2) ) ),
    inference(resolution,[],[f106,f89])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_relset_1(X0,X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ( k11_relat_1(X1,sK4(X0,X1,X2)) != k11_relat_1(X2,sK4(X0,X1,X2))
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f75])).

fof(f75,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
          & r2_hidden(X3,X0) )
     => ( k11_relat_1(X1,sK4(X0,X1,X2)) != k11_relat_1(X2,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relset_1)).

fof(f2020,plain,
    ( ~ spl5_2
    | ~ spl5_13
    | spl5_19 ),
    inference(avatar_contradiction_clause,[],[f2019])).

fof(f2019,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_13
    | spl5_19 ),
    inference(subsumption_resolution,[],[f2018,f390])).

fof(f390,plain,
    ( sK0 != k2_relat_1(sK2)
    | spl5_19 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl5_19
  <=> sK0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f2000,plain,
    ( ~ spl5_13
    | spl5_18 ),
    inference(avatar_contradiction_clause,[],[f1999])).

fof(f1999,plain,
    ( $false
    | ~ spl5_13
    | spl5_18 ),
    inference(subsumption_resolution,[],[f1985,f386])).

fof(f386,plain,
    ( ~ v2_funct_1(sK2)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl5_18
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f1985,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_13 ),
    inference(superposition,[],[f87,f1698])).

fof(f617,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | spl5_12 ),
    inference(subsumption_resolution,[],[f615,f81])).

fof(f615,plain,
    ( ~ v1_funct_1(sK2)
    | spl5_12 ),
    inference(subsumption_resolution,[],[f609,f303])).

fof(f303,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl5_12
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f609,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f343,f83])).

fof(f343,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f338,f78])).

fof(f338,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f124,f80])).

fof(f124,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f461,plain,
    ( spl5_20
    | spl5_8 ),
    inference(avatar_split_clause,[],[f199,f170,f459])).

fof(f170,plain,
    ( spl5_8
  <=> ! [X1] : ~ v1_xboole_0(X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f199,plain,(
    ! [X4,X5] :
      ( ~ v1_xboole_0(X4)
      | ~ r2_hidden(X5,k1_xboole_0) ) ),
    inference(resolution,[],[f118,f88])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f457,plain,(
    ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f456])).

fof(f456,plain,
    ( $false
    | ~ spl5_8 ),
    inference(resolution,[],[f171,f105])).

fof(f105,plain,(
    ! [X0] : v1_xboole_0(sK3(X0)) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( v1_xboole_0(sK3(X0))
      & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f1,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f171,plain,
    ( ! [X1] : ~ v1_xboole_0(X1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f170])).

fof(f391,plain,
    ( spl5_17
    | ~ spl5_18
    | spl5_15
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f378,f388,f368,f384,f380])).

fof(f378,plain,
    ( sK0 != k2_relat_1(sK2)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f377,f229])).

fof(f377,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK2)
    | sK0 != k2_relset_1(sK0,sK0,sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f376,f81])).

fof(f376,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK2)
    | sK0 != k2_relset_1(sK0,sK0,sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f355,f82])).

fof(f355,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK2)
    | sK0 != k2_relset_1(sK0,sK0,sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f115,f83])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
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

fof(f308,plain,
    ( ~ spl5_12
    | spl5_13 ),
    inference(avatar_split_clause,[],[f299,f305,f301])).

fof(f299,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f298,f80])).

fof(f298,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f120,f84])).

fof(f84,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f72])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f183,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f177,f133])).

fof(f133,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl5_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f138,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f128,f135,f131])).

fof(f128,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f94,f78])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:17:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (17900)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.49  % (17882)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (17881)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (17890)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (17887)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (17904)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (17891)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (17880)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (17888)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (17886)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (17901)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (17902)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (17892)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (17898)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (17896)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (17879)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.54  % (17899)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (17893)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  % (17883)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (17877)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (17878)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (17903)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (17905)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.44/0.55  % (17884)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.44/0.55  % (17895)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.44/0.56  % (17885)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.54/0.60  % (17887)Refutation found. Thanks to Tanya!
% 1.54/0.60  % SZS status Theorem for theBenchmark
% 1.54/0.60  % SZS output start Proof for theBenchmark
% 1.54/0.60  fof(f2276,plain,(
% 1.54/0.60    $false),
% 1.54/0.60    inference(avatar_sat_refutation,[],[f138,f183,f308,f391,f457,f461,f617,f2000,f2020,f2201,f2255])).
% 1.54/0.60  fof(f2255,plain,(
% 1.54/0.60    ~spl5_2 | ~spl5_13 | ~spl5_17),
% 1.54/0.60    inference(avatar_contradiction_clause,[],[f2254])).
% 1.54/0.60  fof(f2254,plain,(
% 1.54/0.60    $false | (~spl5_2 | ~spl5_13 | ~spl5_17)),
% 1.54/0.60    inference(subsumption_resolution,[],[f2211,f211])).
% 1.54/0.60  fof(f211,plain,(
% 1.54/0.60    r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.54/0.60    inference(resolution,[],[f127,f83])).
% 1.54/0.60  fof(f83,plain,(
% 1.54/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.54/0.60    inference(cnf_transformation,[],[f72])).
% 1.54/0.60  fof(f72,plain,(
% 1.54/0.60    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.54/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f71,f70])).
% 1.54/0.60  fof(f70,plain,(
% 1.54/0.60    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f71,plain,(
% 1.54/0.60    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f31,plain,(
% 1.54/0.60    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.54/0.60    inference(flattening,[],[f30])).
% 1.54/0.60  fof(f30,plain,(
% 1.54/0.60    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.54/0.60    inference(ennf_transformation,[],[f28])).
% 1.54/0.60  fof(f28,negated_conjecture,(
% 1.54/0.60    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.54/0.60    inference(negated_conjecture,[],[f27])).
% 1.54/0.60  fof(f27,conjecture,(
% 1.54/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).
% 1.54/0.60  fof(f127,plain,(
% 1.54/0.60    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.54/0.60    inference(duplicate_literal_removal,[],[f126])).
% 1.54/0.60  fof(f126,plain,(
% 1.54/0.60    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.54/0.60    inference(equality_resolution,[],[f121])).
% 1.54/0.60  fof(f121,plain,(
% 1.54/0.60    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f77])).
% 1.54/0.60  fof(f77,plain,(
% 1.54/0.60    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.60    inference(nnf_transformation,[],[f65])).
% 1.54/0.60  fof(f65,plain,(
% 1.54/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.60    inference(flattening,[],[f64])).
% 1.54/0.60  fof(f64,plain,(
% 1.54/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.54/0.60    inference(ennf_transformation,[],[f18])).
% 1.54/0.60  fof(f18,axiom,(
% 1.54/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.54/0.60  fof(f2211,plain,(
% 1.54/0.60    ~r2_relset_1(sK0,sK0,sK2,sK2) | (~spl5_2 | ~spl5_13 | ~spl5_17)),
% 1.54/0.60    inference(superposition,[],[f86,f2207])).
% 1.54/0.60  fof(f2207,plain,(
% 1.54/0.60    k6_partfun1(sK0) = sK2 | (~spl5_2 | ~spl5_13 | ~spl5_17)),
% 1.54/0.60    inference(forward_demodulation,[],[f2206,f2060])).
% 1.54/0.60  fof(f2060,plain,(
% 1.54/0.60    sK2 = k5_relat_1(sK2,sK2) | (~spl5_2 | ~spl5_13)),
% 1.54/0.60    inference(forward_demodulation,[],[f2059,f1698])).
% 1.54/0.60  fof(f1698,plain,(
% 1.54/0.60    sK2 = k6_relat_1(sK0) | ~spl5_13),
% 1.54/0.60    inference(global_subsumption,[],[f689,f1688])).
% 1.54/0.60  fof(f1688,plain,(
% 1.54/0.60    sK1 = k5_relat_1(sK2,sK1) | ~spl5_13),
% 1.54/0.60    inference(superposition,[],[f307,f600])).
% 1.54/0.60  fof(f600,plain,(
% 1.54/0.60    k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)),
% 1.54/0.60    inference(subsumption_resolution,[],[f595,f81])).
% 1.54/0.60  fof(f81,plain,(
% 1.54/0.60    v1_funct_1(sK2)),
% 1.54/0.60    inference(cnf_transformation,[],[f72])).
% 1.54/0.60  fof(f595,plain,(
% 1.54/0.60    k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) | ~v1_funct_1(sK2)),
% 1.54/0.60    inference(resolution,[],[f336,f83])).
% 1.54/0.60  fof(f336,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) | ~v1_funct_1(X2)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f331,f78])).
% 1.54/0.60  fof(f78,plain,(
% 1.54/0.60    v1_funct_1(sK1)),
% 1.54/0.60    inference(cnf_transformation,[],[f72])).
% 1.54/0.60  fof(f331,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) | ~v1_funct_1(sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.54/0.60    inference(resolution,[],[f122,f80])).
% 1.54/0.60  fof(f80,plain,(
% 1.54/0.60    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.54/0.60    inference(cnf_transformation,[],[f72])).
% 1.54/0.60  fof(f122,plain,(
% 1.54/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f67])).
% 1.54/0.60  fof(f67,plain,(
% 1.54/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.54/0.60    inference(flattening,[],[f66])).
% 1.54/0.60  fof(f66,plain,(
% 1.54/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.54/0.60    inference(ennf_transformation,[],[f23])).
% 1.54/0.60  fof(f23,axiom,(
% 1.54/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.54/0.60  fof(f307,plain,(
% 1.54/0.60    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) | ~spl5_13),
% 1.54/0.60    inference(avatar_component_clause,[],[f305])).
% 1.54/0.60  fof(f305,plain,(
% 1.54/0.60    spl5_13 <=> sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.54/0.60  fof(f689,plain,(
% 1.54/0.60    sK2 = k6_relat_1(sK0) | sK1 != k5_relat_1(sK2,sK1)),
% 1.54/0.60    inference(subsumption_resolution,[],[f688,f178])).
% 1.54/0.60  fof(f178,plain,(
% 1.54/0.60    v1_relat_1(sK2)),
% 1.54/0.60    inference(resolution,[],[f110,f83])).
% 1.54/0.60  fof(f110,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f53])).
% 1.54/0.60  fof(f53,plain,(
% 1.54/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.60    inference(ennf_transformation,[],[f15])).
% 1.54/0.60  fof(f15,axiom,(
% 1.54/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.54/0.60  fof(f688,plain,(
% 1.54/0.60    sK2 = k6_relat_1(sK0) | sK1 != k5_relat_1(sK2,sK1) | ~v1_relat_1(sK2)),
% 1.54/0.60    inference(subsumption_resolution,[],[f687,f81])).
% 1.54/0.60  fof(f687,plain,(
% 1.54/0.60    sK2 = k6_relat_1(sK0) | sK1 != k5_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.54/0.60    inference(subsumption_resolution,[],[f686,f474])).
% 1.54/0.60  fof(f474,plain,(
% 1.54/0.60    sK0 = k1_relat_1(sK1)),
% 1.54/0.60    inference(superposition,[],[f223,f275])).
% 1.54/0.60  fof(f275,plain,(
% 1.54/0.60    sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.54/0.60    inference(subsumption_resolution,[],[f274,f78])).
% 1.54/0.60  fof(f274,plain,(
% 1.54/0.60    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1)),
% 1.54/0.60    inference(subsumption_resolution,[],[f269,f79])).
% 1.54/0.60  fof(f79,plain,(
% 1.54/0.60    v1_funct_2(sK1,sK0,sK0)),
% 1.54/0.60    inference(cnf_transformation,[],[f72])).
% 1.54/0.60  fof(f269,plain,(
% 1.54/0.60    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.54/0.60    inference(resolution,[],[f109,f80])).
% 1.54/0.60  fof(f109,plain,(
% 1.54/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f52])).
% 1.54/0.60  fof(f52,plain,(
% 1.54/0.60    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.54/0.60    inference(flattening,[],[f51])).
% 1.54/0.60  fof(f51,plain,(
% 1.54/0.60    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.54/0.60    inference(ennf_transformation,[],[f26])).
% 1.54/0.60  fof(f26,axiom,(
% 1.54/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 1.54/0.60  fof(f223,plain,(
% 1.54/0.60    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 1.54/0.60    inference(resolution,[],[f111,f80])).
% 1.54/0.60  fof(f111,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f54])).
% 1.54/0.60  fof(f54,plain,(
% 1.54/0.60    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.60    inference(ennf_transformation,[],[f16])).
% 1.54/0.60  fof(f16,axiom,(
% 1.54/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.54/0.60  fof(f686,plain,(
% 1.54/0.60    sK2 = k6_relat_1(sK0) | sK1 != k5_relat_1(sK2,sK1) | sK0 != k1_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.54/0.60    inference(subsumption_resolution,[],[f656,f483])).
% 1.54/0.60  fof(f483,plain,(
% 1.54/0.60    r1_tarski(k2_relat_1(sK2),sK0)),
% 1.54/0.60    inference(superposition,[],[f297,f255])).
% 1.54/0.60  fof(f255,plain,(
% 1.54/0.60    k2_relat_1(sK2) = k7_relset_1(sK0,sK0,sK2,sK0)),
% 1.54/0.60    inference(forward_demodulation,[],[f250,f229])).
% 1.54/0.60  fof(f229,plain,(
% 1.54/0.60    k2_relat_1(sK2) = k2_relset_1(sK0,sK0,sK2)),
% 1.54/0.60    inference(resolution,[],[f112,f83])).
% 1.54/0.60  fof(f112,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(X2) = k2_relset_1(X0,X1,X2)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f55])).
% 1.54/0.60  fof(f55,plain,(
% 1.54/0.60    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.60    inference(ennf_transformation,[],[f17])).
% 1.54/0.60  fof(f17,axiom,(
% 1.54/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.54/0.60  fof(f250,plain,(
% 1.54/0.60    k2_relset_1(sK0,sK0,sK2) = k7_relset_1(sK0,sK0,sK2,sK0)),
% 1.54/0.60    inference(resolution,[],[f113,f83])).
% 1.54/0.60  fof(f113,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f56])).
% 1.54/0.60  fof(f56,plain,(
% 1.54/0.60    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.60    inference(ennf_transformation,[],[f19])).
% 1.54/0.60  fof(f19,axiom,(
% 1.54/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 1.54/0.60  fof(f297,plain,(
% 1.54/0.60    ( ! [X1] : (r1_tarski(k7_relset_1(sK0,sK0,sK2,X1),sK0)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f296,f81])).
% 1.54/0.60  fof(f296,plain,(
% 1.54/0.60    ( ! [X1] : (r1_tarski(k7_relset_1(sK0,sK0,sK2,X1),sK0) | ~v1_funct_1(sK2)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f290,f82])).
% 1.54/0.60  fof(f82,plain,(
% 1.54/0.60    v1_funct_2(sK2,sK0,sK0)),
% 1.54/0.60    inference(cnf_transformation,[],[f72])).
% 1.54/0.60  fof(f290,plain,(
% 1.54/0.60    ( ! [X1] : (r1_tarski(k7_relset_1(sK0,sK0,sK2,X1),sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)) )),
% 1.54/0.60    inference(resolution,[],[f119,f83])).
% 1.54/0.60  fof(f119,plain,(
% 1.54/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f63])).
% 1.54/0.60  fof(f63,plain,(
% 1.54/0.60    ! [X0,X1,X2,X3] : (r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.54/0.60    inference(flattening,[],[f62])).
% 1.54/0.60  fof(f62,plain,(
% 1.54/0.60    ! [X0,X1,X2,X3] : (r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.54/0.60    inference(ennf_transformation,[],[f25])).
% 1.54/0.60  fof(f25,axiom,(
% 1.54/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_2)).
% 1.54/0.60  fof(f656,plain,(
% 1.54/0.60    ~r1_tarski(k2_relat_1(sK2),sK0) | sK2 = k6_relat_1(sK0) | sK1 != k5_relat_1(sK2,sK1) | sK0 != k1_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.54/0.60    inference(superposition,[],[f404,f476])).
% 1.54/0.60  fof(f476,plain,(
% 1.54/0.60    sK0 = k1_relat_1(sK2)),
% 1.54/0.60    inference(superposition,[],[f224,f277])).
% 1.54/0.60  fof(f277,plain,(
% 1.54/0.60    sK0 = k1_relset_1(sK0,sK0,sK2)),
% 1.54/0.60    inference(subsumption_resolution,[],[f276,f81])).
% 1.54/0.60  fof(f276,plain,(
% 1.54/0.60    sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_1(sK2)),
% 1.54/0.60    inference(subsumption_resolution,[],[f270,f82])).
% 1.54/0.60  fof(f270,plain,(
% 1.54/0.60    sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 1.54/0.60    inference(resolution,[],[f109,f83])).
% 1.54/0.60  fof(f224,plain,(
% 1.54/0.60    k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2)),
% 1.54/0.60    inference(resolution,[],[f111,f83])).
% 1.54/0.60  fof(f404,plain,(
% 1.54/0.60    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X0)) | k6_relat_1(k1_relat_1(X0)) = X0 | sK1 != k5_relat_1(X0,sK1) | k1_relat_1(X0) != k1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f403,f177])).
% 1.54/0.60  fof(f177,plain,(
% 1.54/0.60    v1_relat_1(sK1)),
% 1.54/0.60    inference(resolution,[],[f110,f80])).
% 1.54/0.60  fof(f403,plain,(
% 1.54/0.60    ( ! [X0] : (sK1 != k5_relat_1(X0,sK1) | k6_relat_1(k1_relat_1(X0)) = X0 | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK1)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f401,f78])).
% 1.54/0.60  fof(f401,plain,(
% 1.54/0.60    ( ! [X0] : (sK1 != k5_relat_1(X0,sK1) | k6_relat_1(k1_relat_1(X0)) = X0 | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.54/0.60    inference(resolution,[],[f125,f85])).
% 1.54/0.60  fof(f85,plain,(
% 1.54/0.60    v2_funct_1(sK1)),
% 1.54/0.60    inference(cnf_transformation,[],[f72])).
% 1.54/0.60  fof(f125,plain,(
% 1.54/0.60    ( ! [X2,X1] : (~v2_funct_1(X1) | k5_relat_1(X2,X1) != X1 | k6_relat_1(k1_relat_1(X2)) = X2 | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X2)) | k1_relat_1(X1) != k1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.54/0.60    inference(equality_resolution,[],[f108])).
% 1.54/0.60  fof(f108,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (k6_relat_1(X0) = X2 | k5_relat_1(X2,X1) != X1 | ~v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f50])).
% 1.54/0.60  fof(f50,plain,(
% 1.54/0.60    ! [X0,X1] : (! [X2] : (k6_relat_1(X0) = X2 | k5_relat_1(X2,X1) != X1 | ~v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.54/0.60    inference(flattening,[],[f49])).
% 1.54/0.60  fof(f49,plain,(
% 1.54/0.60    ! [X0,X1] : (! [X2] : ((k6_relat_1(X0) = X2 | (k5_relat_1(X2,X1) != X1 | ~v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.54/0.60    inference(ennf_transformation,[],[f8])).
% 1.54/0.60  fof(f8,axiom,(
% 1.54/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).
% 1.54/0.60  fof(f2059,plain,(
% 1.54/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,sK2) | (~spl5_2 | ~spl5_13)),
% 1.54/0.60    inference(forward_demodulation,[],[f2034,f2018])).
% 1.54/0.60  fof(f2018,plain,(
% 1.54/0.60    sK0 = k2_relat_1(sK2) | (~spl5_2 | ~spl5_13)),
% 1.54/0.60    inference(forward_demodulation,[],[f2017,f476])).
% 1.54/0.60  fof(f2017,plain,(
% 1.54/0.60    k1_relat_1(sK2) = k2_relat_1(sK2) | (~spl5_2 | ~spl5_13)),
% 1.54/0.60    inference(forward_demodulation,[],[f2016,f1729])).
% 1.54/0.60  fof(f1729,plain,(
% 1.54/0.60    sK2 = k2_funct_1(sK2) | (~spl5_2 | ~spl5_13)),
% 1.54/0.60    inference(forward_demodulation,[],[f1728,f1698])).
% 1.54/0.60  fof(f1728,plain,(
% 1.54/0.60    k6_relat_1(sK0) = k2_funct_1(k6_relat_1(sK0)) | ~spl5_2),
% 1.54/0.60    inference(forward_demodulation,[],[f1727,f474])).
% 1.54/0.60  fof(f1727,plain,(
% 1.54/0.60    k6_relat_1(k1_relat_1(sK1)) = k2_funct_1(k6_relat_1(k1_relat_1(sK1))) | ~spl5_2),
% 1.54/0.60    inference(forward_demodulation,[],[f1726,f244])).
% 1.54/0.60  fof(f244,plain,(
% 1.54/0.60    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 1.54/0.60    inference(subsumption_resolution,[],[f243,f177])).
% 1.54/0.60  fof(f243,plain,(
% 1.54/0.60    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.54/0.60    inference(subsumption_resolution,[],[f241,f78])).
% 1.54/0.60  fof(f241,plain,(
% 1.54/0.60    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.54/0.60    inference(resolution,[],[f101,f85])).
% 1.54/0.60  fof(f101,plain,(
% 1.54/0.60    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f44])).
% 1.54/0.60  fof(f44,plain,(
% 1.54/0.60    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.60    inference(flattening,[],[f43])).
% 1.54/0.60  fof(f43,plain,(
% 1.54/0.60    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.60    inference(ennf_transformation,[],[f12])).
% 1.54/0.60  fof(f12,axiom,(
% 1.54/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.54/0.60  fof(f1726,plain,(
% 1.54/0.60    k5_relat_1(sK1,k2_funct_1(sK1)) = k2_funct_1(k5_relat_1(sK1,k2_funct_1(sK1))) | ~spl5_2),
% 1.54/0.60    inference(subsumption_resolution,[],[f1725,f177])).
% 1.54/0.60  fof(f1725,plain,(
% 1.54/0.60    k5_relat_1(sK1,k2_funct_1(sK1)) = k2_funct_1(k5_relat_1(sK1,k2_funct_1(sK1))) | ~v1_relat_1(sK1) | ~spl5_2),
% 1.54/0.60    inference(subsumption_resolution,[],[f1722,f78])).
% 1.54/0.60  fof(f1722,plain,(
% 1.54/0.60    k5_relat_1(sK1,k2_funct_1(sK1)) = k2_funct_1(k5_relat_1(sK1,k2_funct_1(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl5_2),
% 1.54/0.60    inference(resolution,[],[f448,f85])).
% 1.54/0.60  fof(f448,plain,(
% 1.54/0.60    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k5_relat_1(X0,k2_funct_1(sK1))) = k5_relat_1(sK1,k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_2),
% 1.54/0.60    inference(forward_demodulation,[],[f447,f209])).
% 1.54/0.60  fof(f209,plain,(
% 1.54/0.60    sK1 = k2_funct_1(k2_funct_1(sK1))),
% 1.54/0.60    inference(subsumption_resolution,[],[f208,f177])).
% 1.54/0.60  fof(f208,plain,(
% 1.54/0.60    sK1 = k2_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 1.54/0.60    inference(subsumption_resolution,[],[f206,f78])).
% 1.54/0.60  fof(f206,plain,(
% 1.54/0.60    sK1 = k2_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.54/0.60    inference(resolution,[],[f96,f85])).
% 1.54/0.60  fof(f96,plain,(
% 1.54/0.60    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f38])).
% 1.54/0.60  fof(f38,plain,(
% 1.54/0.60    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.60    inference(flattening,[],[f37])).
% 1.54/0.60  fof(f37,plain,(
% 1.54/0.60    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.60    inference(ennf_transformation,[],[f13])).
% 1.54/0.60  fof(f13,axiom,(
% 1.54/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 1.54/0.60  fof(f447,plain,(
% 1.54/0.60    ( ! [X0] : (k2_funct_1(k5_relat_1(X0,k2_funct_1(sK1))) = k5_relat_1(k2_funct_1(k2_funct_1(sK1)),k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_2),
% 1.54/0.60    inference(subsumption_resolution,[],[f446,f137])).
% 1.54/0.60  fof(f137,plain,(
% 1.54/0.60    v1_relat_1(k2_funct_1(sK1)) | ~spl5_2),
% 1.54/0.60    inference(avatar_component_clause,[],[f135])).
% 1.54/0.60  fof(f135,plain,(
% 1.54/0.60    spl5_2 <=> v1_relat_1(k2_funct_1(sK1))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.54/0.60  fof(f446,plain,(
% 1.54/0.60    ( ! [X0] : (k2_funct_1(k5_relat_1(X0,k2_funct_1(sK1))) = k5_relat_1(k2_funct_1(k2_funct_1(sK1)),k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f415,f186])).
% 1.54/0.60  fof(f186,plain,(
% 1.54/0.60    v1_funct_1(k2_funct_1(sK1))),
% 1.54/0.60    inference(subsumption_resolution,[],[f148,f177])).
% 1.54/0.60  fof(f148,plain,(
% 1.54/0.60    v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 1.54/0.60    inference(resolution,[],[f95,f78])).
% 1.54/0.60  fof(f95,plain,(
% 1.54/0.60    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f36])).
% 1.54/0.60  fof(f36,plain,(
% 1.54/0.60    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.60    inference(flattening,[],[f35])).
% 1.54/0.60  fof(f35,plain,(
% 1.54/0.60    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.60    inference(ennf_transformation,[],[f6])).
% 1.54/0.60  fof(f6,axiom,(
% 1.54/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.54/0.60  fof(f415,plain,(
% 1.54/0.60    ( ! [X0] : (k2_funct_1(k5_relat_1(X0,k2_funct_1(sK1))) = k5_relat_1(k2_funct_1(k2_funct_1(sK1)),k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.60    inference(resolution,[],[f195,f103])).
% 1.54/0.60  fof(f103,plain,(
% 1.54/0.60    ( ! [X0,X1] : (~v2_funct_1(X1) | k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f46])).
% 1.54/0.60  fof(f46,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.60    inference(flattening,[],[f45])).
% 1.54/0.60  fof(f45,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : ((k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.60    inference(ennf_transformation,[],[f14])).
% 1.54/0.60  fof(f14,axiom,(
% 1.54/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).
% 1.54/0.60  fof(f195,plain,(
% 1.54/0.60    v2_funct_1(k2_funct_1(sK1))),
% 1.54/0.60    inference(subsumption_resolution,[],[f194,f177])).
% 1.54/0.60  fof(f194,plain,(
% 1.54/0.60    v2_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 1.54/0.60    inference(subsumption_resolution,[],[f192,f78])).
% 1.54/0.60  fof(f192,plain,(
% 1.54/0.60    v2_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.54/0.60    inference(resolution,[],[f93,f85])).
% 1.54/0.60  fof(f93,plain,(
% 1.54/0.60    ( ! [X0] : (~v2_funct_1(X0) | v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f34])).
% 1.54/0.60  fof(f34,plain,(
% 1.54/0.60    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.60    inference(flattening,[],[f33])).
% 1.54/0.60  fof(f33,plain,(
% 1.54/0.60    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.60    inference(ennf_transformation,[],[f7])).
% 1.54/0.60  fof(f7,axiom,(
% 1.54/0.60    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.54/0.60  fof(f2016,plain,(
% 1.54/0.60    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl5_13),
% 1.54/0.60    inference(subsumption_resolution,[],[f2015,f178])).
% 1.54/0.60  fof(f2015,plain,(
% 1.54/0.60    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~spl5_13),
% 1.54/0.60    inference(subsumption_resolution,[],[f1989,f81])).
% 1.54/0.60  fof(f1989,plain,(
% 1.54/0.60    ~v1_funct_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~spl5_13),
% 1.54/0.60    inference(superposition,[],[f220,f1698])).
% 1.54/0.60  fof(f220,plain,(
% 1.54/0.60    ( ! [X0] : (~v1_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) = k2_relat_1(k2_funct_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.54/0.60    inference(resolution,[],[f98,f87])).
% 1.54/0.60  fof(f87,plain,(
% 1.54/0.60    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f9])).
% 1.54/0.60  fof(f9,axiom,(
% 1.54/0.60    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 1.54/0.60  fof(f98,plain,(
% 1.54/0.60    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f40])).
% 1.54/0.60  fof(f40,plain,(
% 1.54/0.60    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.60    inference(flattening,[],[f39])).
% 1.54/0.60  fof(f39,plain,(
% 1.54/0.60    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.60    inference(ennf_transformation,[],[f10])).
% 1.54/0.60  fof(f10,axiom,(
% 1.54/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.54/0.60  fof(f2034,plain,(
% 1.54/0.60    k5_relat_1(sK2,sK2) = k6_relat_1(k2_relat_1(sK2)) | (~spl5_2 | ~spl5_13)),
% 1.54/0.60    inference(forward_demodulation,[],[f2033,f1729])).
% 1.54/0.60  fof(f2033,plain,(
% 1.54/0.60    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~spl5_13),
% 1.54/0.60    inference(subsumption_resolution,[],[f2032,f178])).
% 1.54/0.60  fof(f2032,plain,(
% 1.54/0.60    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl5_13),
% 1.54/0.60    inference(subsumption_resolution,[],[f1993,f81])).
% 1.54/0.60  fof(f1993,plain,(
% 1.54/0.60    ~v1_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl5_13),
% 1.54/0.60    inference(superposition,[],[f246,f1698])).
% 1.54/0.60  fof(f246,plain,(
% 1.54/0.60    ( ! [X0] : (~v1_funct_1(k6_relat_1(X0)) | k5_relat_1(k2_funct_1(k6_relat_1(X0)),k6_relat_1(X0)) = k6_relat_1(k2_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.54/0.60    inference(resolution,[],[f102,f87])).
% 1.54/0.60  fof(f102,plain,(
% 1.54/0.60    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f44])).
% 1.54/0.60  fof(f2206,plain,(
% 1.54/0.60    k6_partfun1(sK0) = k5_relat_1(sK2,sK2) | (~spl5_2 | ~spl5_13 | ~spl5_17)),
% 1.54/0.60    inference(forward_demodulation,[],[f382,f1729])).
% 1.54/0.60  fof(f382,plain,(
% 1.54/0.60    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl5_17),
% 1.54/0.60    inference(avatar_component_clause,[],[f380])).
% 1.54/0.60  fof(f380,plain,(
% 1.54/0.60    spl5_17 <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.54/0.60  fof(f86,plain,(
% 1.54/0.60    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 1.54/0.60    inference(cnf_transformation,[],[f72])).
% 1.54/0.60  fof(f2201,plain,(
% 1.54/0.60    ~spl5_15 | ~spl5_20),
% 1.54/0.60    inference(avatar_contradiction_clause,[],[f2200])).
% 1.54/0.60  fof(f2200,plain,(
% 1.54/0.60    $false | (~spl5_15 | ~spl5_20)),
% 1.54/0.60    inference(subsumption_resolution,[],[f2139,f460])).
% 1.54/0.60  fof(f460,plain,(
% 1.54/0.60    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0)) ) | ~spl5_20),
% 1.54/0.60    inference(avatar_component_clause,[],[f459])).
% 1.54/0.60  fof(f459,plain,(
% 1.54/0.60    spl5_20 <=> ! [X5] : ~r2_hidden(X5,k1_xboole_0)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.54/0.60  fof(f2139,plain,(
% 1.54/0.60    r2_hidden(sK4(k1_xboole_0,sK2,k6_partfun1(k1_xboole_0)),k1_xboole_0) | ~spl5_15),
% 1.54/0.60    inference(superposition,[],[f742,f370])).
% 1.54/0.60  fof(f370,plain,(
% 1.54/0.60    k1_xboole_0 = sK0 | ~spl5_15),
% 1.54/0.60    inference(avatar_component_clause,[],[f368])).
% 1.54/0.60  fof(f368,plain,(
% 1.54/0.60    spl5_15 <=> k1_xboole_0 = sK0),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.54/0.60  fof(f742,plain,(
% 1.54/0.60    r2_hidden(sK4(sK0,sK2,k6_partfun1(sK0)),sK0)),
% 1.54/0.60    inference(subsumption_resolution,[],[f729,f86])).
% 1.54/0.60  fof(f729,plain,(
% 1.54/0.60    r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) | r2_hidden(sK4(sK0,sK2,k6_partfun1(sK0)),sK0)),
% 1.54/0.60    inference(resolution,[],[f321,f83])).
% 1.54/0.60  fof(f321,plain,(
% 1.54/0.60    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) | r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | r2_hidden(sK4(X2,X3,k6_partfun1(X2)),X2)) )),
% 1.54/0.60    inference(resolution,[],[f106,f89])).
% 1.54/0.60  fof(f89,plain,(
% 1.54/0.60    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f29])).
% 1.54/0.60  fof(f29,plain,(
% 1.54/0.60    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.54/0.60    inference(pure_predicate_removal,[],[f22])).
% 1.54/0.60  fof(f22,axiom,(
% 1.54/0.60    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.54/0.60  fof(f106,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | r2_hidden(sK4(X0,X1,X2),X0) | r2_relset_1(X0,X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f76])).
% 1.54/0.60  fof(f76,plain,(
% 1.54/0.60    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | (k11_relat_1(X1,sK4(X0,X1,X2)) != k11_relat_1(X2,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.54/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f75])).
% 1.54/0.60  fof(f75,plain,(
% 1.54/0.60    ! [X2,X1,X0] : (? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) => (k11_relat_1(X1,sK4(X0,X1,X2)) != k11_relat_1(X2,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f48,plain,(
% 1.54/0.60    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.54/0.60    inference(flattening,[],[f47])).
% 1.54/0.60  fof(f47,plain,(
% 1.54/0.60    ! [X0,X1] : (! [X2] : ((r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.54/0.60    inference(ennf_transformation,[],[f20])).
% 1.54/0.60  fof(f20,axiom,(
% 1.54/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relset_1)).
% 1.54/0.60  fof(f2020,plain,(
% 1.54/0.60    ~spl5_2 | ~spl5_13 | spl5_19),
% 1.54/0.60    inference(avatar_contradiction_clause,[],[f2019])).
% 1.54/0.60  fof(f2019,plain,(
% 1.54/0.60    $false | (~spl5_2 | ~spl5_13 | spl5_19)),
% 1.54/0.60    inference(subsumption_resolution,[],[f2018,f390])).
% 1.54/0.60  fof(f390,plain,(
% 1.54/0.60    sK0 != k2_relat_1(sK2) | spl5_19),
% 1.54/0.60    inference(avatar_component_clause,[],[f388])).
% 1.54/0.60  fof(f388,plain,(
% 1.54/0.60    spl5_19 <=> sK0 = k2_relat_1(sK2)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.54/0.60  fof(f2000,plain,(
% 1.54/0.60    ~spl5_13 | spl5_18),
% 1.54/0.60    inference(avatar_contradiction_clause,[],[f1999])).
% 1.54/0.60  fof(f1999,plain,(
% 1.54/0.60    $false | (~spl5_13 | spl5_18)),
% 1.54/0.60    inference(subsumption_resolution,[],[f1985,f386])).
% 1.54/0.60  fof(f386,plain,(
% 1.54/0.60    ~v2_funct_1(sK2) | spl5_18),
% 1.54/0.60    inference(avatar_component_clause,[],[f384])).
% 1.54/0.60  fof(f384,plain,(
% 1.54/0.60    spl5_18 <=> v2_funct_1(sK2)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.54/0.60  fof(f1985,plain,(
% 1.54/0.60    v2_funct_1(sK2) | ~spl5_13),
% 1.54/0.60    inference(superposition,[],[f87,f1698])).
% 1.54/0.60  fof(f617,plain,(
% 1.54/0.60    spl5_12),
% 1.54/0.60    inference(avatar_contradiction_clause,[],[f616])).
% 1.54/0.60  fof(f616,plain,(
% 1.54/0.60    $false | spl5_12),
% 1.54/0.60    inference(subsumption_resolution,[],[f615,f81])).
% 1.54/0.60  fof(f615,plain,(
% 1.54/0.60    ~v1_funct_1(sK2) | spl5_12),
% 1.54/0.60    inference(subsumption_resolution,[],[f609,f303])).
% 1.54/0.60  fof(f303,plain,(
% 1.54/0.60    ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl5_12),
% 1.54/0.60    inference(avatar_component_clause,[],[f301])).
% 1.54/0.60  fof(f301,plain,(
% 1.54/0.60    spl5_12 <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.54/0.60  fof(f609,plain,(
% 1.54/0.60    m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.54/0.60    inference(resolution,[],[f343,f83])).
% 1.54/0.60  fof(f343,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v1_funct_1(X2)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f338,f78])).
% 1.54/0.60  fof(f338,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (m1_subset_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.54/0.60    inference(resolution,[],[f124,f80])).
% 1.54/0.60  fof(f124,plain,(
% 1.54/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f69])).
% 1.54/0.60  fof(f69,plain,(
% 1.54/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.54/0.60    inference(flattening,[],[f68])).
% 1.54/0.60  fof(f68,plain,(
% 1.54/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.54/0.60    inference(ennf_transformation,[],[f21])).
% 1.54/0.60  fof(f21,axiom,(
% 1.54/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.54/0.60  fof(f461,plain,(
% 1.54/0.60    spl5_20 | spl5_8),
% 1.54/0.60    inference(avatar_split_clause,[],[f199,f170,f459])).
% 1.54/0.60  fof(f170,plain,(
% 1.54/0.60    spl5_8 <=> ! [X1] : ~v1_xboole_0(X1)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.54/0.60  fof(f199,plain,(
% 1.54/0.60    ( ! [X4,X5] : (~v1_xboole_0(X4) | ~r2_hidden(X5,k1_xboole_0)) )),
% 1.54/0.60    inference(resolution,[],[f118,f88])).
% 1.54/0.60  fof(f88,plain,(
% 1.54/0.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f2])).
% 1.54/0.60  fof(f2,axiom,(
% 1.54/0.60    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.54/0.60  fof(f118,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f61])).
% 1.54/0.60  fof(f61,plain,(
% 1.54/0.60    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.54/0.60    inference(ennf_transformation,[],[f5])).
% 1.54/0.60  fof(f5,axiom,(
% 1.54/0.60    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.54/0.60  fof(f457,plain,(
% 1.54/0.60    ~spl5_8),
% 1.54/0.60    inference(avatar_contradiction_clause,[],[f456])).
% 1.54/0.60  fof(f456,plain,(
% 1.54/0.60    $false | ~spl5_8),
% 1.54/0.60    inference(resolution,[],[f171,f105])).
% 1.54/0.60  fof(f105,plain,(
% 1.54/0.60    ( ! [X0] : (v1_xboole_0(sK3(X0))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f74])).
% 1.54/0.60  fof(f74,plain,(
% 1.54/0.60    ! [X0] : (v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)))),
% 1.54/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f1,f73])).
% 1.54/0.60  fof(f73,plain,(
% 1.54/0.60    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0))))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f1,axiom,(
% 1.54/0.60    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).
% 1.54/0.60  fof(f171,plain,(
% 1.54/0.60    ( ! [X1] : (~v1_xboole_0(X1)) ) | ~spl5_8),
% 1.54/0.60    inference(avatar_component_clause,[],[f170])).
% 1.54/0.60  fof(f391,plain,(
% 1.54/0.60    spl5_17 | ~spl5_18 | spl5_15 | ~spl5_19),
% 1.54/0.60    inference(avatar_split_clause,[],[f378,f388,f368,f384,f380])).
% 1.54/0.60  fof(f378,plain,(
% 1.54/0.60    sK0 != k2_relat_1(sK2) | k1_xboole_0 = sK0 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.54/0.60    inference(forward_demodulation,[],[f377,f229])).
% 1.54/0.60  fof(f377,plain,(
% 1.54/0.60    k1_xboole_0 = sK0 | ~v2_funct_1(sK2) | sK0 != k2_relset_1(sK0,sK0,sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.54/0.60    inference(subsumption_resolution,[],[f376,f81])).
% 1.54/0.60  fof(f376,plain,(
% 1.54/0.60    k1_xboole_0 = sK0 | ~v2_funct_1(sK2) | sK0 != k2_relset_1(sK0,sK0,sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 1.54/0.60    inference(subsumption_resolution,[],[f355,f82])).
% 1.54/0.60  fof(f355,plain,(
% 1.54/0.60    k1_xboole_0 = sK0 | ~v2_funct_1(sK2) | sK0 != k2_relset_1(sK0,sK0,sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 1.54/0.60    inference(resolution,[],[f115,f83])).
% 1.54/0.62  fof(f115,plain,(
% 1.54/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f58])).
% 1.54/0.62  fof(f58,plain,(
% 1.54/0.62    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.54/0.62    inference(flattening,[],[f57])).
% 1.54/0.62  fof(f57,plain,(
% 1.54/0.62    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.54/0.62    inference(ennf_transformation,[],[f24])).
% 1.54/0.62  fof(f24,axiom,(
% 1.54/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.54/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.54/0.62  fof(f308,plain,(
% 1.54/0.62    ~spl5_12 | spl5_13),
% 1.54/0.62    inference(avatar_split_clause,[],[f299,f305,f301])).
% 1.54/0.62  fof(f299,plain,(
% 1.54/0.62    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.54/0.62    inference(subsumption_resolution,[],[f298,f80])).
% 1.54/0.62  fof(f298,plain,(
% 1.54/0.62    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.54/0.62    inference(resolution,[],[f120,f84])).
% 1.54/0.62  fof(f84,plain,(
% 1.54/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)),
% 1.54/0.62    inference(cnf_transformation,[],[f72])).
% 1.54/0.62  fof(f120,plain,(
% 1.54/0.62    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.54/0.62    inference(cnf_transformation,[],[f77])).
% 1.54/0.62  fof(f183,plain,(
% 1.54/0.62    spl5_1),
% 1.54/0.62    inference(avatar_contradiction_clause,[],[f182])).
% 1.54/0.62  fof(f182,plain,(
% 1.54/0.62    $false | spl5_1),
% 1.54/0.62    inference(subsumption_resolution,[],[f177,f133])).
% 1.54/0.62  fof(f133,plain,(
% 1.54/0.62    ~v1_relat_1(sK1) | spl5_1),
% 1.54/0.62    inference(avatar_component_clause,[],[f131])).
% 1.54/0.62  fof(f131,plain,(
% 1.54/0.62    spl5_1 <=> v1_relat_1(sK1)),
% 1.54/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.54/0.62  fof(f138,plain,(
% 1.54/0.62    ~spl5_1 | spl5_2),
% 1.54/0.62    inference(avatar_split_clause,[],[f128,f135,f131])).
% 1.54/0.62  fof(f128,plain,(
% 1.54/0.62    v1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 1.54/0.62    inference(resolution,[],[f94,f78])).
% 1.54/0.62  fof(f94,plain,(
% 1.54/0.62    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f36])).
% 1.54/0.62  % SZS output end Proof for theBenchmark
% 1.54/0.62  % (17887)------------------------------
% 1.54/0.62  % (17887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.62  % (17887)Termination reason: Refutation
% 1.54/0.62  
% 1.54/0.62  % (17887)Memory used [KB]: 12281
% 1.54/0.62  % (17887)Time elapsed: 0.182 s
% 1.54/0.62  % (17887)------------------------------
% 1.54/0.62  % (17887)------------------------------
% 1.54/0.62  % (17873)Success in time 0.255 s
%------------------------------------------------------------------------------
