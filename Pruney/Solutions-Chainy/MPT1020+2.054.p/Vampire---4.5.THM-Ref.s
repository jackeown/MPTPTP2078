%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:48 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  216 (1496 expanded)
%              Number of leaves         :   26 ( 461 expanded)
%              Depth                    :   23
%              Number of atoms          :  830 (11050 expanded)
%              Number of equality atoms :  143 ( 337 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f316,f525,f568,f920,f928,f955,f1010,f1113,f1121,f1133])).

% (6241)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f1133,plain,
    ( spl5_6
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_34 ),
    inference(avatar_contradiction_clause,[],[f1132])).

fof(f1132,plain,
    ( $false
    | spl5_6
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f1131,f209])).

fof(f209,plain,(
    v1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f179,f125])).

fof(f125,plain,(
    sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f124,f48])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f41,f40])).

fof(f40,plain,
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

fof(f41,plain,
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

% (6227)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f124,plain,
    ( sP0(sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f123,f49])).

fof(f49,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f123,plain,
    ( sP0(sK2,sK3)
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f120,f50])).

fof(f50,plain,(
    v3_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f120,plain,
    ( sP0(sK2,sK3)
    | ~ v3_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f68,f51])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | sP0(X0,X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(definition_folding,[],[f25,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f24])).

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

fof(f179,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ sP0(sK2,sK3) ),
    inference(superposition,[],[f95,f163])).

fof(f163,plain,(
    k2_funct_2(sK2,sK3) = k2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f162,f48])).

fof(f162,plain,
    ( k2_funct_2(sK2,sK3) = k2_funct_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f161,f49])).

fof(f161,plain,
    ( k2_funct_2(sK2,sK3) = k2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f158,f50])).

fof(f158,plain,
    ( k2_funct_2(sK2,sK3) = k2_funct_1(sK3)
    | ~ v3_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f63,f51])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f95,plain,(
    ! [X4,X5] :
      ( v1_relat_1(k2_funct_2(X4,X5))
      | ~ sP0(X4,X5) ) ),
    inference(subsumption_resolution,[],[f94,f60])).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f94,plain,(
    ! [X4,X5] :
      ( ~ sP0(X4,X5)
      | v1_relat_1(k2_funct_2(X4,X5))
      | ~ v1_relat_1(k2_zfmisc_1(X4,X4)) ) ),
    inference(resolution,[],[f67,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f1131,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl5_6
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f1130,f196])).

fof(f196,plain,
    ( sK3 != k2_funct_1(sK3)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl5_6
  <=> sK3 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1130,plain,
    ( sK3 = k2_funct_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_34 ),
    inference(trivial_inequality_removal,[],[f1123])).

fof(f1123,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK3 = k2_funct_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_34 ),
    inference(superposition,[],[f764,f1112])).

fof(f1112,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(sK3))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f1110])).

fof(f1110,plain,
    ( spl5_34
  <=> k1_xboole_0 = k2_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f764,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k2_relat_1(X2)
        | sK3 = X2
        | ~ v1_relat_1(X2) )
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f758,f86])).

fof(f86,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f84,f60])).

fof(f84,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(resolution,[],[f59,f51])).

fof(f758,plain,
    ( ! [X2] :
        ( sK3 = X2
        | k1_xboole_0 != k2_relat_1(X2)
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X2) )
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(trivial_inequality_removal,[],[f755])).

fof(f755,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k1_xboole_0
        | sK3 = X2
        | k1_xboole_0 != k2_relat_1(X2)
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X2) )
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(superposition,[],[f58,f750])).

fof(f750,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f748,f574])).

fof(f574,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f51,f315])).

fof(f315,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl5_13
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f748,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(superposition,[],[f698,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f698,plain,
    ( k1_xboole_0 = k2_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f310,f315])).

fof(f310,plain,
    ( sK2 = k2_relset_1(sK2,sK2,sK3)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl5_12
  <=> sK2 = k2_relset_1(sK2,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_relat_1(X1)
      | X0 = X1
      | k2_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k1_xboole_0 != k2_relat_1(X1)
          | k2_relat_1(X0) != k1_xboole_0
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k1_xboole_0 != k2_relat_1(X1)
          | k2_relat_1(X0) != k1_xboole_0
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k2_relat_1(X1)
              & k2_relat_1(X0) = k1_xboole_0 )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t197_relat_1)).

fof(f1121,plain,
    ( ~ spl5_13
    | spl5_33 ),
    inference(avatar_contradiction_clause,[],[f1120])).

fof(f1120,plain,
    ( $false
    | ~ spl5_13
    | spl5_33 ),
    inference(subsumption_resolution,[],[f1117,f634])).

fof(f634,plain,
    ( v5_relat_1(k2_funct_1(sK3),k1_xboole_0)
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f207,f315])).

fof(f207,plain,(
    v5_relat_1(k2_funct_1(sK3),sK2) ),
    inference(subsumption_resolution,[],[f177,f125])).

fof(f177,plain,
    ( v5_relat_1(k2_funct_1(sK3),sK2)
    | ~ sP0(sK2,sK3) ),
    inference(superposition,[],[f92,f163])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v5_relat_1(k2_funct_2(X0,X1),X0)
      | ~ sP0(X0,X1) ) ),
    inference(resolution,[],[f67,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f1117,plain,
    ( ~ v5_relat_1(k2_funct_1(sK3),k1_xboole_0)
    | ~ spl5_13
    | spl5_33 ),
    inference(resolution,[],[f1116,f643])).

fof(f643,plain,
    ( v2_funct_2(k2_funct_1(sK3),k1_xboole_0)
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f213,f315])).

fof(f213,plain,(
    v2_funct_2(k2_funct_1(sK3),sK2) ),
    inference(resolution,[],[f211,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP1(X1,X2) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP1(X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f211,plain,(
    sP1(sK2,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f181,f125])).

fof(f181,plain,
    ( sP1(sK2,k2_funct_1(sK3))
    | ~ sP0(sK2,sK3) ),
    inference(superposition,[],[f113,f163])).

fof(f113,plain,(
    ! [X0,X1] :
      ( sP1(X0,k2_funct_2(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f112,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(k2_funct_2(X0,X1))
      | sP1(X0,k2_funct_2(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f107,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ v1_funct_1(k2_funct_2(X0,X1))
      | sP1(X0,k2_funct_2(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(resolution,[],[f75,f67])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | sP1(X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f29,f38])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f1116,plain,
    ( ! [X0] :
        ( ~ v2_funct_2(k2_funct_1(sK3),X0)
        | ~ v5_relat_1(k2_funct_1(sK3),X0) )
    | spl5_33 ),
    inference(subsumption_resolution,[],[f1115,f209])).

fof(f1115,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(k2_funct_1(sK3),X0)
        | ~ v2_funct_2(k2_funct_1(sK3),X0)
        | ~ v1_relat_1(k2_funct_1(sK3)) )
    | spl5_33 ),
    inference(duplicate_literal_removal,[],[f1114])).

fof(f1114,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(k2_funct_1(sK3),X0)
        | ~ v2_funct_2(k2_funct_1(sK3),X0)
        | ~ v5_relat_1(k2_funct_1(sK3),X0)
        | ~ v1_relat_1(k2_funct_1(sK3)) )
    | spl5_33 ),
    inference(superposition,[],[f1108,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f1108,plain,
    ( ~ v5_relat_1(k2_funct_1(sK3),k2_relat_1(k2_funct_1(sK3)))
    | spl5_33 ),
    inference(avatar_component_clause,[],[f1106])).

fof(f1106,plain,
    ( spl5_33
  <=> v5_relat_1(k2_funct_1(sK3),k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f1113,plain,
    ( ~ spl5_33
    | spl5_34
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f1104,f313,f1110,f1106])).

fof(f1104,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(sK3))
    | ~ v5_relat_1(k2_funct_1(sK3),k2_relat_1(k2_funct_1(sK3)))
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f1103,f209])).

fof(f1103,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(sK3))
    | ~ v5_relat_1(k2_funct_1(sK3),k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl5_13 ),
    inference(duplicate_literal_removal,[],[f1102])).

fof(f1102,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(sK3))
    | ~ v5_relat_1(k2_funct_1(sK3),k2_relat_1(k2_funct_1(sK3)))
    | ~ v5_relat_1(k2_funct_1(sK3),k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl5_13 ),
    inference(resolution,[],[f670,f81])).

fof(f81,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f670,plain,
    ( ! [X0] :
        ( ~ v2_funct_2(k2_funct_1(sK3),X0)
        | k1_xboole_0 = X0
        | ~ v5_relat_1(k2_funct_1(sK3),X0) )
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f669,f209])).

fof(f669,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_relat_1(k2_funct_1(sK3))
        | ~ v2_funct_2(k2_funct_1(sK3),X0)
        | ~ v5_relat_1(k2_funct_1(sK3),X0) )
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f668,f634])).

fof(f668,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v5_relat_1(k2_funct_1(sK3),k1_xboole_0)
        | ~ v1_relat_1(k2_funct_1(sK3))
        | ~ v2_funct_2(k2_funct_1(sK3),X0)
        | ~ v5_relat_1(k2_funct_1(sK3),X0) )
    | ~ spl5_13 ),
    inference(resolution,[],[f643,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_2(X0,X2)
      | X1 = X2
      | ~ v5_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_2(X0,X1)
      | ~ v5_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ v2_funct_2(X0,X2)
      | ~ v5_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_2(X0,X1)
      | ~ v5_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f61,f61])).

fof(f1010,plain,
    ( ~ spl5_6
    | ~ spl5_2
    | spl5_4 ),
    inference(avatar_split_clause,[],[f959,f185,f146,f195])).

fof(f146,plain,
    ( spl5_2
  <=> sK3 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f185,plain,
    ( spl5_4
  <=> sK4 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f959,plain,
    ( sK3 != k2_funct_1(sK3)
    | ~ spl5_2
    | spl5_4 ),
    inference(backward_demodulation,[],[f186,f148])).

fof(f148,plain,
    ( sK3 = sK4
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f146])).

fof(f186,plain,
    ( sK4 != k2_funct_1(sK3)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f185])).

fof(f955,plain,
    ( spl5_2
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f954,f917,f313,f309,f146])).

fof(f917,plain,
    ( spl5_30
  <=> k1_xboole_0 = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f954,plain,
    ( sK3 = sK4
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f952,f86])).

fof(f952,plain,
    ( sK3 = sK4
    | ~ v1_relat_1(sK3)
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_30 ),
    inference(trivial_inequality_removal,[],[f950])).

fof(f950,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK3 = sK4
    | ~ v1_relat_1(sK3)
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_30 ),
    inference(superposition,[],[f945,f750])).

fof(f945,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k2_relat_1(X2)
        | sK4 = X2
        | ~ v1_relat_1(X2) )
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f942,f87])).

fof(f87,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f85,f60])).

% (6247)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f85,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(resolution,[],[f59,f55])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f942,plain,
    ( ! [X2] :
        ( sK4 = X2
        | k1_xboole_0 != k2_relat_1(X2)
        | ~ v1_relat_1(sK4)
        | ~ v1_relat_1(X2) )
    | ~ spl5_30 ),
    inference(trivial_inequality_removal,[],[f939])).

fof(f939,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k1_xboole_0
        | sK4 = X2
        | k1_xboole_0 != k2_relat_1(X2)
        | ~ v1_relat_1(sK4)
        | ~ v1_relat_1(X2) )
    | ~ spl5_30 ),
    inference(superposition,[],[f58,f919])).

fof(f919,plain,
    ( k1_xboole_0 = k2_relat_1(sK4)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f917])).

fof(f928,plain,
    ( ~ spl5_13
    | spl5_29 ),
    inference(avatar_contradiction_clause,[],[f927])).

fof(f927,plain,
    ( $false
    | ~ spl5_13
    | spl5_29 ),
    inference(subsumption_resolution,[],[f924,f582])).

fof(f582,plain,
    ( v5_relat_1(sK4,k1_xboole_0)
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f91,f315])).

fof(f91,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f71,f55])).

fof(f924,plain,
    ( ~ v5_relat_1(sK4,k1_xboole_0)
    | ~ spl5_13
    | spl5_29 ),
    inference(resolution,[],[f923,f588])).

fof(f588,plain,
    ( v2_funct_2(sK4,k1_xboole_0)
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f117,f315])).

fof(f117,plain,(
    v2_funct_2(sK4,sK2) ),
    inference(resolution,[],[f111,f74])).

fof(f111,plain,(
    sP1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f110,f52])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f110,plain,
    ( ~ v1_funct_1(sK4)
    | sP1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f106,f54])).

fof(f54,plain,(
    v3_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f106,plain,
    ( ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | sP1(sK2,sK4) ),
    inference(resolution,[],[f75,f55])).

fof(f923,plain,
    ( ! [X0] :
        ( ~ v2_funct_2(sK4,X0)
        | ~ v5_relat_1(sK4,X0) )
    | spl5_29 ),
    inference(subsumption_resolution,[],[f922,f87])).

fof(f922,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK4,X0)
        | ~ v2_funct_2(sK4,X0)
        | ~ v1_relat_1(sK4) )
    | spl5_29 ),
    inference(duplicate_literal_removal,[],[f921])).

fof(f921,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK4,X0)
        | ~ v2_funct_2(sK4,X0)
        | ~ v5_relat_1(sK4,X0)
        | ~ v1_relat_1(sK4) )
    | spl5_29 ),
    inference(superposition,[],[f915,f61])).

fof(f915,plain,
    ( ~ v5_relat_1(sK4,k2_relat_1(sK4))
    | spl5_29 ),
    inference(avatar_component_clause,[],[f913])).

fof(f913,plain,
    ( spl5_29
  <=> v5_relat_1(sK4,k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f920,plain,
    ( ~ spl5_29
    | spl5_30
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f911,f313,f917,f913])).

fof(f911,plain,
    ( k1_xboole_0 = k2_relat_1(sK4)
    | ~ v5_relat_1(sK4,k2_relat_1(sK4))
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f910,f87])).

fof(f910,plain,
    ( k1_xboole_0 = k2_relat_1(sK4)
    | ~ v5_relat_1(sK4,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_13 ),
    inference(duplicate_literal_removal,[],[f909])).

fof(f909,plain,
    ( k1_xboole_0 = k2_relat_1(sK4)
    | ~ v5_relat_1(sK4,k2_relat_1(sK4))
    | ~ v5_relat_1(sK4,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_13 ),
    inference(resolution,[],[f642,f81])).

fof(f642,plain,
    ( ! [X0] :
        ( ~ v2_funct_2(sK4,X0)
        | k1_xboole_0 = X0
        | ~ v5_relat_1(sK4,X0) )
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f641,f87])).

fof(f641,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_relat_1(sK4)
        | ~ v2_funct_2(sK4,X0)
        | ~ v5_relat_1(sK4,X0) )
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f640,f582])).

fof(f640,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v5_relat_1(sK4,k1_xboole_0)
        | ~ v1_relat_1(sK4)
        | ~ v2_funct_2(sK4,X0)
        | ~ v5_relat_1(sK4,X0) )
    | ~ spl5_13 ),
    inference(resolution,[],[f588,f102])).

fof(f568,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f567])).

fof(f567,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f537,f97])).

fof(f97,plain,(
    r2_relset_1(sK2,sK2,sK4,sK4) ),
    inference(resolution,[],[f83,f55])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f537,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,sK4)
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f170,f187])).

fof(f187,plain,
    ( sK4 = k2_funct_1(sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f185])).

fof(f170,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f57,f163])).

fof(f57,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f525,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f524])).

fof(f524,plain,
    ( $false
    | spl5_12 ),
    inference(subsumption_resolution,[],[f521,f90])).

fof(f90,plain,(
    v5_relat_1(sK3,sK2) ),
    inference(resolution,[],[f71,f51])).

fof(f521,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | spl5_12 ),
    inference(resolution,[],[f519,f114])).

fof(f114,plain,(
    v2_funct_2(sK3,sK2) ),
    inference(resolution,[],[f109,f74])).

fof(f109,plain,(
    sP1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f108,f48])).

fof(f108,plain,
    ( ~ v1_funct_1(sK3)
    | sP1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f105,f50])).

fof(f105,plain,
    ( ~ v3_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3)
    | sP1(sK2,sK3) ),
    inference(resolution,[],[f75,f51])).

fof(f519,plain,
    ( ! [X0] :
        ( ~ v2_funct_2(sK3,X0)
        | ~ v5_relat_1(sK3,X0) )
    | spl5_12 ),
    inference(subsumption_resolution,[],[f518,f86])).

fof(f518,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK3,X0)
        | ~ v2_funct_2(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl5_12 ),
    inference(duplicate_literal_removal,[],[f517])).

fof(f517,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK3,X0)
        | ~ v2_funct_2(sK3,X0)
        | ~ v5_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl5_12 ),
    inference(superposition,[],[f516,f61])).

fof(f516,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | spl5_12 ),
    inference(subsumption_resolution,[],[f515,f86])).

fof(f515,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl5_12 ),
    inference(subsumption_resolution,[],[f514,f318])).

fof(f318,plain,
    ( sK2 != k2_relat_1(sK3)
    | spl5_12 ),
    inference(subsumption_resolution,[],[f317,f51])).

fof(f317,plain,
    ( sK2 != k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | spl5_12 ),
    inference(superposition,[],[f311,f69])).

fof(f311,plain,
    ( sK2 != k2_relset_1(sK2,sK2,sK3)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f309])).

fof(f514,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f513])).

fof(f513,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f463,f81])).

fof(f463,plain,(
    ! [X5] :
      ( ~ v2_funct_2(sK3,X5)
      | sK2 = X5
      | ~ v5_relat_1(sK3,X5) ) ),
    inference(subsumption_resolution,[],[f462,f86])).

fof(f462,plain,(
    ! [X5] :
      ( sK2 = X5
      | ~ v1_relat_1(sK3)
      | ~ v2_funct_2(sK3,X5)
      | ~ v5_relat_1(sK3,X5) ) ),
    inference(subsumption_resolution,[],[f453,f90])).

fof(f453,plain,(
    ! [X5] :
      ( sK2 = X5
      | ~ v5_relat_1(sK3,sK2)
      | ~ v1_relat_1(sK3)
      | ~ v2_funct_2(sK3,X5)
      | ~ v5_relat_1(sK3,X5) ) ),
    inference(resolution,[],[f102,f114])).

fof(f316,plain,
    ( ~ spl5_12
    | spl5_4
    | spl5_13 ),
    inference(avatar_split_clause,[],[f307,f313,f185,f309])).

fof(f307,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3) ),
    inference(subsumption_resolution,[],[f306,f48])).

fof(f306,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f305,f49])).

fof(f305,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f304,f51])).

fof(f304,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f303,f52])).

fof(f303,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f302,f53])).

fof(f53,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f302,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f301,f55])).

fof(f301,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(duplicate_literal_removal,[],[f300])).

fof(f300,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f299,f56])).

fof(f56,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f299,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_funct_1(X2) = X3
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f78,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | v2_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n025.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 21:06:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.46  % (6248)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.47  % (6232)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.48  % (6249)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.48  % (6231)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.48  % (6229)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.49  % (6238)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.49  % (6246)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.49  % (6226)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.49  % (6233)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.49  % (6245)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.49  % (6234)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.49  % (6228)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.49  % (6237)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.49  % (6230)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.49  % (6239)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.50  % (6244)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.50  % (6225)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.50  % (6235)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.50  % (6240)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.51  % (6236)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.51  % (6243)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.51  % (6250)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.19/0.52  % (6229)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % (6242)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f1136,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(avatar_sat_refutation,[],[f316,f525,f568,f920,f928,f955,f1010,f1113,f1121,f1133])).
% 0.19/0.52  % (6241)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.52  fof(f1133,plain,(
% 0.19/0.52    spl5_6 | ~spl5_12 | ~spl5_13 | ~spl5_34),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f1132])).
% 0.19/0.52  fof(f1132,plain,(
% 0.19/0.52    $false | (spl5_6 | ~spl5_12 | ~spl5_13 | ~spl5_34)),
% 0.19/0.52    inference(subsumption_resolution,[],[f1131,f209])).
% 0.19/0.52  fof(f209,plain,(
% 0.19/0.52    v1_relat_1(k2_funct_1(sK3))),
% 0.19/0.52    inference(subsumption_resolution,[],[f179,f125])).
% 0.19/0.52  fof(f125,plain,(
% 0.19/0.52    sP0(sK2,sK3)),
% 0.19/0.52    inference(subsumption_resolution,[],[f124,f48])).
% 0.19/0.52  fof(f48,plain,(
% 0.19/0.52    v1_funct_1(sK3)),
% 0.19/0.52    inference(cnf_transformation,[],[f42])).
% 0.19/0.52  fof(f42,plain,(
% 0.19/0.52    (~r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK4,sK2,sK2) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK3,sK2,sK2) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f41,f40])).
% 0.19/0.52  fof(f40,plain,(
% 0.19/0.52    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK2,sK2,X2,k2_funct_2(sK2,sK3)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X2),k6_partfun1(sK2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(X2,sK2,sK2) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK3,sK2,sK2) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f41,plain,(
% 0.19/0.52    ? [X2] : (~r2_relset_1(sK2,sK2,X2,k2_funct_2(sK2,sK3)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X2),k6_partfun1(sK2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(X2,sK2,sK2) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) => (~r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK4,sK2,sK2) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f16,plain,(
% 0.19/0.52    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.19/0.52    inference(flattening,[],[f15])).
% 0.19/0.52  fof(f15,plain,(
% 0.19/0.52    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.19/0.52    inference(ennf_transformation,[],[f14])).
% 0.19/0.52  fof(f14,negated_conjecture,(
% 0.19/0.52    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.19/0.52    inference(negated_conjecture,[],[f13])).
% 0.19/0.52  fof(f13,conjecture,(
% 0.19/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).
% 0.19/0.52  % (6227)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.53  fof(f124,plain,(
% 0.19/0.53    sP0(sK2,sK3) | ~v1_funct_1(sK3)),
% 0.19/0.53    inference(subsumption_resolution,[],[f123,f49])).
% 0.19/0.53  fof(f49,plain,(
% 0.19/0.53    v1_funct_2(sK3,sK2,sK2)),
% 0.19/0.53    inference(cnf_transformation,[],[f42])).
% 0.19/0.53  fof(f123,plain,(
% 0.19/0.53    sP0(sK2,sK3) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.19/0.53    inference(subsumption_resolution,[],[f120,f50])).
% 0.19/0.53  fof(f50,plain,(
% 0.19/0.53    v3_funct_2(sK3,sK2,sK2)),
% 0.19/0.53    inference(cnf_transformation,[],[f42])).
% 0.19/0.53  fof(f120,plain,(
% 0.19/0.53    sP0(sK2,sK3) | ~v3_funct_2(sK3,sK2,sK2) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.19/0.53    inference(resolution,[],[f68,f51])).
% 0.19/0.53  fof(f51,plain,(
% 0.19/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.19/0.53    inference(cnf_transformation,[],[f42])).
% 0.19/0.53  fof(f68,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | sP0(X0,X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f37])).
% 0.19/0.53  fof(f37,plain,(
% 0.19/0.53    ! [X0,X1] : (sP0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.19/0.53    inference(definition_folding,[],[f25,f36])).
% 0.19/0.53  fof(f36,plain,(
% 0.19/0.53    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~sP0(X0,X1))),
% 0.19/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.53  fof(f25,plain,(
% 0.19/0.53    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.19/0.53    inference(flattening,[],[f24])).
% 0.19/0.53  fof(f24,plain,(
% 0.19/0.53    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.19/0.53    inference(ennf_transformation,[],[f9])).
% 0.19/0.53  fof(f9,axiom,(
% 0.19/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.19/0.53  fof(f179,plain,(
% 0.19/0.53    v1_relat_1(k2_funct_1(sK3)) | ~sP0(sK2,sK3)),
% 0.19/0.53    inference(superposition,[],[f95,f163])).
% 0.19/0.53  fof(f163,plain,(
% 0.19/0.53    k2_funct_2(sK2,sK3) = k2_funct_1(sK3)),
% 0.19/0.53    inference(subsumption_resolution,[],[f162,f48])).
% 0.19/0.53  fof(f162,plain,(
% 0.19/0.53    k2_funct_2(sK2,sK3) = k2_funct_1(sK3) | ~v1_funct_1(sK3)),
% 0.19/0.53    inference(subsumption_resolution,[],[f161,f49])).
% 0.19/0.53  fof(f161,plain,(
% 0.19/0.53    k2_funct_2(sK2,sK3) = k2_funct_1(sK3) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.19/0.53    inference(subsumption_resolution,[],[f158,f50])).
% 0.19/0.53  fof(f158,plain,(
% 0.19/0.53    k2_funct_2(sK2,sK3) = k2_funct_1(sK3) | ~v3_funct_2(sK3,sK2,sK2) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.19/0.53    inference(resolution,[],[f63,f51])).
% 0.19/0.53  fof(f63,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f23])).
% 0.19/0.53  fof(f23,plain,(
% 0.19/0.53    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.19/0.53    inference(flattening,[],[f22])).
% 0.19/0.53  fof(f22,plain,(
% 0.19/0.53    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.19/0.53    inference(ennf_transformation,[],[f10])).
% 0.19/0.53  fof(f10,axiom,(
% 0.19/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.19/0.53  fof(f95,plain,(
% 0.19/0.53    ( ! [X4,X5] : (v1_relat_1(k2_funct_2(X4,X5)) | ~sP0(X4,X5)) )),
% 0.19/0.53    inference(subsumption_resolution,[],[f94,f60])).
% 0.19/0.53  fof(f60,plain,(
% 0.19/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f2])).
% 0.19/0.53  fof(f2,axiom,(
% 0.19/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.53  fof(f94,plain,(
% 0.19/0.53    ( ! [X4,X5] : (~sP0(X4,X5) | v1_relat_1(k2_funct_2(X4,X5)) | ~v1_relat_1(k2_zfmisc_1(X4,X4))) )),
% 0.19/0.53    inference(resolution,[],[f67,f59])).
% 0.19/0.53  fof(f59,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f19])).
% 0.19/0.53  fof(f19,plain,(
% 0.19/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.53    inference(ennf_transformation,[],[f1])).
% 0.19/0.53  fof(f1,axiom,(
% 0.19/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.53  fof(f67,plain,(
% 0.19/0.53    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~sP0(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f44])).
% 0.19/0.53  fof(f44,plain,(
% 0.19/0.53    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~sP0(X0,X1))),
% 0.19/0.53    inference(nnf_transformation,[],[f36])).
% 0.19/0.53  fof(f1131,plain,(
% 0.19/0.53    ~v1_relat_1(k2_funct_1(sK3)) | (spl5_6 | ~spl5_12 | ~spl5_13 | ~spl5_34)),
% 0.19/0.53    inference(subsumption_resolution,[],[f1130,f196])).
% 0.19/0.53  fof(f196,plain,(
% 0.19/0.53    sK3 != k2_funct_1(sK3) | spl5_6),
% 0.19/0.53    inference(avatar_component_clause,[],[f195])).
% 0.19/0.53  fof(f195,plain,(
% 0.19/0.53    spl5_6 <=> sK3 = k2_funct_1(sK3)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.19/0.53  fof(f1130,plain,(
% 0.19/0.53    sK3 = k2_funct_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl5_12 | ~spl5_13 | ~spl5_34)),
% 0.19/0.53    inference(trivial_inequality_removal,[],[f1123])).
% 0.19/0.53  fof(f1123,plain,(
% 0.19/0.53    k1_xboole_0 != k1_xboole_0 | sK3 = k2_funct_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl5_12 | ~spl5_13 | ~spl5_34)),
% 0.19/0.53    inference(superposition,[],[f764,f1112])).
% 0.19/0.53  fof(f1112,plain,(
% 0.19/0.53    k1_xboole_0 = k2_relat_1(k2_funct_1(sK3)) | ~spl5_34),
% 0.19/0.53    inference(avatar_component_clause,[],[f1110])).
% 0.19/0.53  fof(f1110,plain,(
% 0.19/0.53    spl5_34 <=> k1_xboole_0 = k2_relat_1(k2_funct_1(sK3))),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.19/0.53  fof(f764,plain,(
% 0.19/0.53    ( ! [X2] : (k1_xboole_0 != k2_relat_1(X2) | sK3 = X2 | ~v1_relat_1(X2)) ) | (~spl5_12 | ~spl5_13)),
% 0.19/0.53    inference(subsumption_resolution,[],[f758,f86])).
% 0.19/0.53  fof(f86,plain,(
% 0.19/0.53    v1_relat_1(sK3)),
% 0.19/0.53    inference(subsumption_resolution,[],[f84,f60])).
% 0.19/0.53  fof(f84,plain,(
% 0.19/0.53    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))),
% 0.19/0.53    inference(resolution,[],[f59,f51])).
% 0.19/0.53  fof(f758,plain,(
% 0.19/0.53    ( ! [X2] : (sK3 = X2 | k1_xboole_0 != k2_relat_1(X2) | ~v1_relat_1(sK3) | ~v1_relat_1(X2)) ) | (~spl5_12 | ~spl5_13)),
% 0.19/0.53    inference(trivial_inequality_removal,[],[f755])).
% 0.19/0.53  fof(f755,plain,(
% 0.19/0.53    ( ! [X2] : (k1_xboole_0 != k1_xboole_0 | sK3 = X2 | k1_xboole_0 != k2_relat_1(X2) | ~v1_relat_1(sK3) | ~v1_relat_1(X2)) ) | (~spl5_12 | ~spl5_13)),
% 0.19/0.53    inference(superposition,[],[f58,f750])).
% 0.19/0.53  fof(f750,plain,(
% 0.19/0.53    k1_xboole_0 = k2_relat_1(sK3) | (~spl5_12 | ~spl5_13)),
% 0.19/0.53    inference(subsumption_resolution,[],[f748,f574])).
% 0.19/0.53  fof(f574,plain,(
% 0.19/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl5_13),
% 0.19/0.53    inference(backward_demodulation,[],[f51,f315])).
% 0.19/0.53  fof(f315,plain,(
% 0.19/0.53    k1_xboole_0 = sK2 | ~spl5_13),
% 0.19/0.53    inference(avatar_component_clause,[],[f313])).
% 0.19/0.53  fof(f313,plain,(
% 0.19/0.53    spl5_13 <=> k1_xboole_0 = sK2),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.19/0.53  fof(f748,plain,(
% 0.19/0.53    k1_xboole_0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_12 | ~spl5_13)),
% 0.19/0.53    inference(superposition,[],[f698,f69])).
% 0.19/0.53  fof(f69,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f26])).
% 0.19/0.53  fof(f26,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.53    inference(ennf_transformation,[],[f5])).
% 0.19/0.53  fof(f5,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.53  fof(f698,plain,(
% 0.19/0.53    k1_xboole_0 = k2_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl5_12 | ~spl5_13)),
% 0.19/0.53    inference(forward_demodulation,[],[f310,f315])).
% 0.19/0.53  fof(f310,plain,(
% 0.19/0.53    sK2 = k2_relset_1(sK2,sK2,sK3) | ~spl5_12),
% 0.19/0.53    inference(avatar_component_clause,[],[f309])).
% 0.19/0.53  fof(f309,plain,(
% 0.19/0.53    spl5_12 <=> sK2 = k2_relset_1(sK2,sK2,sK3)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.19/0.53  fof(f58,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k1_xboole_0 != k2_relat_1(X1) | X0 = X1 | k2_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f18])).
% 0.19/0.53  fof(f18,plain,(
% 0.19/0.53    ! [X0] : (! [X1] : (X0 = X1 | k1_xboole_0 != k2_relat_1(X1) | k2_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.53    inference(flattening,[],[f17])).
% 0.19/0.53  fof(f17,plain,(
% 0.19/0.53    ! [X0] : (! [X1] : ((X0 = X1 | (k1_xboole_0 != k2_relat_1(X1) | k2_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.53    inference(ennf_transformation,[],[f3])).
% 0.19/0.53  fof(f3,axiom,(
% 0.19/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k2_relat_1(X1) & k2_relat_1(X0) = k1_xboole_0) => X0 = X1)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t197_relat_1)).
% 0.19/0.53  fof(f1121,plain,(
% 0.19/0.53    ~spl5_13 | spl5_33),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f1120])).
% 0.19/0.53  fof(f1120,plain,(
% 0.19/0.53    $false | (~spl5_13 | spl5_33)),
% 0.19/0.53    inference(subsumption_resolution,[],[f1117,f634])).
% 0.19/0.53  fof(f634,plain,(
% 0.19/0.53    v5_relat_1(k2_funct_1(sK3),k1_xboole_0) | ~spl5_13),
% 0.19/0.53    inference(forward_demodulation,[],[f207,f315])).
% 0.19/0.53  fof(f207,plain,(
% 0.19/0.53    v5_relat_1(k2_funct_1(sK3),sK2)),
% 0.19/0.53    inference(subsumption_resolution,[],[f177,f125])).
% 0.19/0.53  fof(f177,plain,(
% 0.19/0.53    v5_relat_1(k2_funct_1(sK3),sK2) | ~sP0(sK2,sK3)),
% 0.19/0.53    inference(superposition,[],[f92,f163])).
% 0.19/0.53  fof(f92,plain,(
% 0.19/0.53    ( ! [X0,X1] : (v5_relat_1(k2_funct_2(X0,X1),X0) | ~sP0(X0,X1)) )),
% 0.19/0.53    inference(resolution,[],[f67,f71])).
% 0.19/0.53  fof(f71,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f27])).
% 0.19/0.53  fof(f27,plain,(
% 0.19/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.53    inference(ennf_transformation,[],[f4])).
% 0.19/0.53  fof(f4,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.53  fof(f1117,plain,(
% 0.19/0.53    ~v5_relat_1(k2_funct_1(sK3),k1_xboole_0) | (~spl5_13 | spl5_33)),
% 0.19/0.53    inference(resolution,[],[f1116,f643])).
% 0.19/0.53  fof(f643,plain,(
% 0.19/0.53    v2_funct_2(k2_funct_1(sK3),k1_xboole_0) | ~spl5_13),
% 0.19/0.53    inference(forward_demodulation,[],[f213,f315])).
% 0.19/0.53  fof(f213,plain,(
% 0.19/0.53    v2_funct_2(k2_funct_1(sK3),sK2)),
% 0.19/0.53    inference(resolution,[],[f211,f74])).
% 0.19/0.53  fof(f74,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~sP1(X0,X1) | v2_funct_2(X1,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f46])).
% 0.19/0.53  fof(f46,plain,(
% 0.19/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) & v2_funct_1(X1) & v1_funct_1(X1)) | ~sP1(X0,X1))),
% 0.19/0.53    inference(rectify,[],[f45])).
% 0.19/0.53  fof(f45,plain,(
% 0.19/0.53    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP1(X1,X2))),
% 0.19/0.53    inference(nnf_transformation,[],[f38])).
% 0.19/0.53  fof(f38,plain,(
% 0.19/0.53    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP1(X1,X2))),
% 0.19/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.19/0.53  fof(f211,plain,(
% 0.19/0.53    sP1(sK2,k2_funct_1(sK3))),
% 0.19/0.53    inference(subsumption_resolution,[],[f181,f125])).
% 0.19/0.53  fof(f181,plain,(
% 0.19/0.53    sP1(sK2,k2_funct_1(sK3)) | ~sP0(sK2,sK3)),
% 0.19/0.53    inference(superposition,[],[f113,f163])).
% 0.19/0.53  fof(f113,plain,(
% 0.19/0.53    ( ! [X0,X1] : (sP1(X0,k2_funct_2(X0,X1)) | ~sP0(X0,X1)) )),
% 0.19/0.53    inference(subsumption_resolution,[],[f112,f64])).
% 0.19/0.53  fof(f64,plain,(
% 0.19/0.53    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~sP0(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f44])).
% 0.19/0.53  fof(f112,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~v1_funct_1(k2_funct_2(X0,X1)) | sP1(X0,k2_funct_2(X0,X1)) | ~sP0(X0,X1)) )),
% 0.19/0.53    inference(subsumption_resolution,[],[f107,f66])).
% 0.19/0.53  fof(f66,plain,(
% 0.19/0.53    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~sP0(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f44])).
% 0.19/0.53  fof(f107,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~v1_funct_1(k2_funct_2(X0,X1)) | sP1(X0,k2_funct_2(X0,X1)) | ~sP0(X0,X1)) )),
% 0.19/0.53    inference(resolution,[],[f75,f67])).
% 0.19/0.53  fof(f75,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | sP1(X1,X2)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f39])).
% 0.19/0.53  fof(f39,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (sP1(X1,X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.53    inference(definition_folding,[],[f29,f38])).
% 0.19/0.53  fof(f29,plain,(
% 0.19/0.53    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.53    inference(flattening,[],[f28])).
% 0.19/0.53  fof(f28,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.53    inference(ennf_transformation,[],[f7])).
% 0.19/0.53  fof(f7,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.19/0.53  fof(f1116,plain,(
% 0.19/0.53    ( ! [X0] : (~v2_funct_2(k2_funct_1(sK3),X0) | ~v5_relat_1(k2_funct_1(sK3),X0)) ) | spl5_33),
% 0.19/0.53    inference(subsumption_resolution,[],[f1115,f209])).
% 0.19/0.53  fof(f1115,plain,(
% 0.19/0.53    ( ! [X0] : (~v5_relat_1(k2_funct_1(sK3),X0) | ~v2_funct_2(k2_funct_1(sK3),X0) | ~v1_relat_1(k2_funct_1(sK3))) ) | spl5_33),
% 0.19/0.53    inference(duplicate_literal_removal,[],[f1114])).
% 0.19/0.53  fof(f1114,plain,(
% 0.19/0.53    ( ! [X0] : (~v5_relat_1(k2_funct_1(sK3),X0) | ~v2_funct_2(k2_funct_1(sK3),X0) | ~v5_relat_1(k2_funct_1(sK3),X0) | ~v1_relat_1(k2_funct_1(sK3))) ) | spl5_33),
% 0.19/0.53    inference(superposition,[],[f1108,f61])).
% 0.19/0.53  fof(f61,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f43])).
% 0.19/0.53  fof(f43,plain,(
% 0.19/0.53    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.53    inference(nnf_transformation,[],[f21])).
% 0.19/0.53  fof(f21,plain,(
% 0.19/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.53    inference(flattening,[],[f20])).
% 0.19/0.53  fof(f20,plain,(
% 0.19/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.53    inference(ennf_transformation,[],[f8])).
% 0.19/0.53  fof(f8,axiom,(
% 0.19/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.19/0.53  fof(f1108,plain,(
% 0.19/0.53    ~v5_relat_1(k2_funct_1(sK3),k2_relat_1(k2_funct_1(sK3))) | spl5_33),
% 0.19/0.53    inference(avatar_component_clause,[],[f1106])).
% 0.19/0.53  fof(f1106,plain,(
% 0.19/0.53    spl5_33 <=> v5_relat_1(k2_funct_1(sK3),k2_relat_1(k2_funct_1(sK3)))),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.19/0.53  fof(f1113,plain,(
% 0.19/0.53    ~spl5_33 | spl5_34 | ~spl5_13),
% 0.19/0.53    inference(avatar_split_clause,[],[f1104,f313,f1110,f1106])).
% 0.19/0.53  fof(f1104,plain,(
% 0.19/0.53    k1_xboole_0 = k2_relat_1(k2_funct_1(sK3)) | ~v5_relat_1(k2_funct_1(sK3),k2_relat_1(k2_funct_1(sK3))) | ~spl5_13),
% 0.19/0.53    inference(subsumption_resolution,[],[f1103,f209])).
% 0.19/0.53  fof(f1103,plain,(
% 0.19/0.53    k1_xboole_0 = k2_relat_1(k2_funct_1(sK3)) | ~v5_relat_1(k2_funct_1(sK3),k2_relat_1(k2_funct_1(sK3))) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl5_13),
% 0.19/0.53    inference(duplicate_literal_removal,[],[f1102])).
% 0.19/0.53  fof(f1102,plain,(
% 0.19/0.53    k1_xboole_0 = k2_relat_1(k2_funct_1(sK3)) | ~v5_relat_1(k2_funct_1(sK3),k2_relat_1(k2_funct_1(sK3))) | ~v5_relat_1(k2_funct_1(sK3),k2_relat_1(k2_funct_1(sK3))) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl5_13),
% 0.19/0.53    inference(resolution,[],[f670,f81])).
% 0.19/0.53  fof(f81,plain,(
% 0.19/0.53    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.19/0.53    inference(equality_resolution,[],[f62])).
% 0.19/0.53  fof(f62,plain,(
% 0.19/0.53    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f43])).
% 0.19/0.53  fof(f670,plain,(
% 0.19/0.53    ( ! [X0] : (~v2_funct_2(k2_funct_1(sK3),X0) | k1_xboole_0 = X0 | ~v5_relat_1(k2_funct_1(sK3),X0)) ) | ~spl5_13),
% 0.19/0.53    inference(subsumption_resolution,[],[f669,f209])).
% 0.19/0.53  fof(f669,plain,(
% 0.19/0.53    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_relat_1(k2_funct_1(sK3)) | ~v2_funct_2(k2_funct_1(sK3),X0) | ~v5_relat_1(k2_funct_1(sK3),X0)) ) | ~spl5_13),
% 0.19/0.53    inference(subsumption_resolution,[],[f668,f634])).
% 0.19/0.53  fof(f668,plain,(
% 0.19/0.53    ( ! [X0] : (k1_xboole_0 = X0 | ~v5_relat_1(k2_funct_1(sK3),k1_xboole_0) | ~v1_relat_1(k2_funct_1(sK3)) | ~v2_funct_2(k2_funct_1(sK3),X0) | ~v5_relat_1(k2_funct_1(sK3),X0)) ) | ~spl5_13),
% 0.19/0.53    inference(resolution,[],[f643,f102])).
% 0.19/0.53  fof(f102,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~v2_funct_2(X0,X2) | X1 = X2 | ~v5_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v2_funct_2(X0,X1) | ~v5_relat_1(X0,X1)) )),
% 0.19/0.53    inference(duplicate_literal_removal,[],[f99])).
% 0.19/0.53  fof(f99,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (X1 = X2 | ~v2_funct_2(X0,X2) | ~v5_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v2_funct_2(X0,X1) | ~v5_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.19/0.53    inference(superposition,[],[f61,f61])).
% 0.19/0.53  fof(f1010,plain,(
% 0.19/0.53    ~spl5_6 | ~spl5_2 | spl5_4),
% 0.19/0.53    inference(avatar_split_clause,[],[f959,f185,f146,f195])).
% 0.19/0.53  fof(f146,plain,(
% 0.19/0.53    spl5_2 <=> sK3 = sK4),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.53  fof(f185,plain,(
% 0.19/0.53    spl5_4 <=> sK4 = k2_funct_1(sK3)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.53  fof(f959,plain,(
% 0.19/0.53    sK3 != k2_funct_1(sK3) | (~spl5_2 | spl5_4)),
% 0.19/0.53    inference(backward_demodulation,[],[f186,f148])).
% 0.19/0.53  fof(f148,plain,(
% 0.19/0.53    sK3 = sK4 | ~spl5_2),
% 0.19/0.53    inference(avatar_component_clause,[],[f146])).
% 0.19/0.53  fof(f186,plain,(
% 0.19/0.53    sK4 != k2_funct_1(sK3) | spl5_4),
% 0.19/0.53    inference(avatar_component_clause,[],[f185])).
% 0.19/0.53  fof(f955,plain,(
% 0.19/0.53    spl5_2 | ~spl5_12 | ~spl5_13 | ~spl5_30),
% 0.19/0.53    inference(avatar_split_clause,[],[f954,f917,f313,f309,f146])).
% 0.19/0.53  fof(f917,plain,(
% 0.19/0.53    spl5_30 <=> k1_xboole_0 = k2_relat_1(sK4)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.19/0.53  fof(f954,plain,(
% 0.19/0.53    sK3 = sK4 | (~spl5_12 | ~spl5_13 | ~spl5_30)),
% 0.19/0.53    inference(subsumption_resolution,[],[f952,f86])).
% 0.19/0.53  fof(f952,plain,(
% 0.19/0.53    sK3 = sK4 | ~v1_relat_1(sK3) | (~spl5_12 | ~spl5_13 | ~spl5_30)),
% 0.19/0.53    inference(trivial_inequality_removal,[],[f950])).
% 0.19/0.53  fof(f950,plain,(
% 0.19/0.53    k1_xboole_0 != k1_xboole_0 | sK3 = sK4 | ~v1_relat_1(sK3) | (~spl5_12 | ~spl5_13 | ~spl5_30)),
% 0.19/0.53    inference(superposition,[],[f945,f750])).
% 0.19/0.53  fof(f945,plain,(
% 0.19/0.53    ( ! [X2] : (k1_xboole_0 != k2_relat_1(X2) | sK4 = X2 | ~v1_relat_1(X2)) ) | ~spl5_30),
% 0.19/0.53    inference(subsumption_resolution,[],[f942,f87])).
% 0.19/0.53  fof(f87,plain,(
% 0.19/0.53    v1_relat_1(sK4)),
% 0.19/0.53    inference(subsumption_resolution,[],[f85,f60])).
% 0.19/0.53  % (6247)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.53  fof(f85,plain,(
% 0.19/0.53    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))),
% 0.19/0.53    inference(resolution,[],[f59,f55])).
% 0.19/0.53  fof(f55,plain,(
% 0.19/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.19/0.53    inference(cnf_transformation,[],[f42])).
% 0.19/0.53  fof(f942,plain,(
% 0.19/0.53    ( ! [X2] : (sK4 = X2 | k1_xboole_0 != k2_relat_1(X2) | ~v1_relat_1(sK4) | ~v1_relat_1(X2)) ) | ~spl5_30),
% 0.19/0.53    inference(trivial_inequality_removal,[],[f939])).
% 0.19/0.53  fof(f939,plain,(
% 0.19/0.53    ( ! [X2] : (k1_xboole_0 != k1_xboole_0 | sK4 = X2 | k1_xboole_0 != k2_relat_1(X2) | ~v1_relat_1(sK4) | ~v1_relat_1(X2)) ) | ~spl5_30),
% 0.19/0.53    inference(superposition,[],[f58,f919])).
% 0.19/0.53  fof(f919,plain,(
% 0.19/0.53    k1_xboole_0 = k2_relat_1(sK4) | ~spl5_30),
% 0.19/0.53    inference(avatar_component_clause,[],[f917])).
% 0.19/0.53  fof(f928,plain,(
% 0.19/0.53    ~spl5_13 | spl5_29),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f927])).
% 0.19/0.53  fof(f927,plain,(
% 0.19/0.53    $false | (~spl5_13 | spl5_29)),
% 0.19/0.53    inference(subsumption_resolution,[],[f924,f582])).
% 0.19/0.53  fof(f582,plain,(
% 0.19/0.53    v5_relat_1(sK4,k1_xboole_0) | ~spl5_13),
% 0.19/0.53    inference(backward_demodulation,[],[f91,f315])).
% 0.19/0.53  fof(f91,plain,(
% 0.19/0.53    v5_relat_1(sK4,sK2)),
% 0.19/0.53    inference(resolution,[],[f71,f55])).
% 0.19/0.53  fof(f924,plain,(
% 0.19/0.53    ~v5_relat_1(sK4,k1_xboole_0) | (~spl5_13 | spl5_29)),
% 0.19/0.53    inference(resolution,[],[f923,f588])).
% 0.19/0.53  fof(f588,plain,(
% 0.19/0.53    v2_funct_2(sK4,k1_xboole_0) | ~spl5_13),
% 0.19/0.53    inference(backward_demodulation,[],[f117,f315])).
% 0.19/0.53  fof(f117,plain,(
% 0.19/0.53    v2_funct_2(sK4,sK2)),
% 0.19/0.53    inference(resolution,[],[f111,f74])).
% 0.19/0.53  fof(f111,plain,(
% 0.19/0.53    sP1(sK2,sK4)),
% 0.19/0.53    inference(subsumption_resolution,[],[f110,f52])).
% 0.19/0.53  fof(f52,plain,(
% 0.19/0.53    v1_funct_1(sK4)),
% 0.19/0.53    inference(cnf_transformation,[],[f42])).
% 0.19/0.53  fof(f110,plain,(
% 0.19/0.53    ~v1_funct_1(sK4) | sP1(sK2,sK4)),
% 0.19/0.53    inference(subsumption_resolution,[],[f106,f54])).
% 0.19/0.54  fof(f54,plain,(
% 0.19/0.54    v3_funct_2(sK4,sK2,sK2)),
% 0.19/0.54    inference(cnf_transformation,[],[f42])).
% 0.19/0.54  fof(f106,plain,(
% 0.19/0.54    ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | sP1(sK2,sK4)),
% 0.19/0.54    inference(resolution,[],[f75,f55])).
% 0.19/0.54  fof(f923,plain,(
% 0.19/0.54    ( ! [X0] : (~v2_funct_2(sK4,X0) | ~v5_relat_1(sK4,X0)) ) | spl5_29),
% 0.19/0.54    inference(subsumption_resolution,[],[f922,f87])).
% 0.19/0.54  fof(f922,plain,(
% 0.19/0.54    ( ! [X0] : (~v5_relat_1(sK4,X0) | ~v2_funct_2(sK4,X0) | ~v1_relat_1(sK4)) ) | spl5_29),
% 0.19/0.54    inference(duplicate_literal_removal,[],[f921])).
% 0.19/0.54  fof(f921,plain,(
% 0.19/0.54    ( ! [X0] : (~v5_relat_1(sK4,X0) | ~v2_funct_2(sK4,X0) | ~v5_relat_1(sK4,X0) | ~v1_relat_1(sK4)) ) | spl5_29),
% 0.19/0.54    inference(superposition,[],[f915,f61])).
% 0.19/0.54  fof(f915,plain,(
% 0.19/0.54    ~v5_relat_1(sK4,k2_relat_1(sK4)) | spl5_29),
% 0.19/0.54    inference(avatar_component_clause,[],[f913])).
% 0.19/0.54  fof(f913,plain,(
% 0.19/0.54    spl5_29 <=> v5_relat_1(sK4,k2_relat_1(sK4))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.19/0.54  fof(f920,plain,(
% 0.19/0.54    ~spl5_29 | spl5_30 | ~spl5_13),
% 0.19/0.54    inference(avatar_split_clause,[],[f911,f313,f917,f913])).
% 0.19/0.54  fof(f911,plain,(
% 0.19/0.54    k1_xboole_0 = k2_relat_1(sK4) | ~v5_relat_1(sK4,k2_relat_1(sK4)) | ~spl5_13),
% 0.19/0.54    inference(subsumption_resolution,[],[f910,f87])).
% 0.19/0.54  fof(f910,plain,(
% 0.19/0.54    k1_xboole_0 = k2_relat_1(sK4) | ~v5_relat_1(sK4,k2_relat_1(sK4)) | ~v1_relat_1(sK4) | ~spl5_13),
% 0.19/0.54    inference(duplicate_literal_removal,[],[f909])).
% 0.19/0.54  fof(f909,plain,(
% 0.19/0.54    k1_xboole_0 = k2_relat_1(sK4) | ~v5_relat_1(sK4,k2_relat_1(sK4)) | ~v5_relat_1(sK4,k2_relat_1(sK4)) | ~v1_relat_1(sK4) | ~spl5_13),
% 0.19/0.54    inference(resolution,[],[f642,f81])).
% 0.19/0.54  fof(f642,plain,(
% 0.19/0.54    ( ! [X0] : (~v2_funct_2(sK4,X0) | k1_xboole_0 = X0 | ~v5_relat_1(sK4,X0)) ) | ~spl5_13),
% 0.19/0.54    inference(subsumption_resolution,[],[f641,f87])).
% 0.19/0.54  fof(f641,plain,(
% 0.19/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_relat_1(sK4) | ~v2_funct_2(sK4,X0) | ~v5_relat_1(sK4,X0)) ) | ~spl5_13),
% 0.19/0.54    inference(subsumption_resolution,[],[f640,f582])).
% 0.19/0.54  fof(f640,plain,(
% 0.19/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~v5_relat_1(sK4,k1_xboole_0) | ~v1_relat_1(sK4) | ~v2_funct_2(sK4,X0) | ~v5_relat_1(sK4,X0)) ) | ~spl5_13),
% 0.19/0.54    inference(resolution,[],[f588,f102])).
% 0.19/0.54  fof(f568,plain,(
% 0.19/0.54    ~spl5_4),
% 0.19/0.54    inference(avatar_contradiction_clause,[],[f567])).
% 0.19/0.54  fof(f567,plain,(
% 0.19/0.54    $false | ~spl5_4),
% 0.19/0.54    inference(subsumption_resolution,[],[f537,f97])).
% 0.19/0.54  fof(f97,plain,(
% 0.19/0.54    r2_relset_1(sK2,sK2,sK4,sK4)),
% 0.19/0.54    inference(resolution,[],[f83,f55])).
% 0.19/0.54  fof(f83,plain,(
% 0.19/0.54    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.19/0.54    inference(duplicate_literal_removal,[],[f82])).
% 0.19/0.54  fof(f82,plain,(
% 0.19/0.54    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.54    inference(equality_resolution,[],[f80])).
% 0.19/0.54  fof(f80,plain,(
% 0.19/0.54    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f47])).
% 0.19/0.54  fof(f47,plain,(
% 0.19/0.54    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.54    inference(nnf_transformation,[],[f35])).
% 0.19/0.54  fof(f35,plain,(
% 0.19/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.54    inference(flattening,[],[f34])).
% 0.19/0.54  fof(f34,plain,(
% 0.19/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.54    inference(ennf_transformation,[],[f6])).
% 0.19/0.54  fof(f6,axiom,(
% 0.19/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.19/0.54  fof(f537,plain,(
% 0.19/0.54    ~r2_relset_1(sK2,sK2,sK4,sK4) | ~spl5_4),
% 0.19/0.54    inference(backward_demodulation,[],[f170,f187])).
% 0.19/0.54  fof(f187,plain,(
% 0.19/0.54    sK4 = k2_funct_1(sK3) | ~spl5_4),
% 0.19/0.54    inference(avatar_component_clause,[],[f185])).
% 0.19/0.54  fof(f170,plain,(
% 0.19/0.54    ~r2_relset_1(sK2,sK2,sK4,k2_funct_1(sK3))),
% 0.19/0.54    inference(backward_demodulation,[],[f57,f163])).
% 0.19/0.54  fof(f57,plain,(
% 0.19/0.54    ~r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))),
% 0.19/0.54    inference(cnf_transformation,[],[f42])).
% 0.19/0.54  fof(f525,plain,(
% 0.19/0.54    spl5_12),
% 0.19/0.54    inference(avatar_contradiction_clause,[],[f524])).
% 0.19/0.54  fof(f524,plain,(
% 0.19/0.54    $false | spl5_12),
% 0.19/0.54    inference(subsumption_resolution,[],[f521,f90])).
% 0.19/0.54  fof(f90,plain,(
% 0.19/0.54    v5_relat_1(sK3,sK2)),
% 0.19/0.54    inference(resolution,[],[f71,f51])).
% 0.19/0.54  fof(f521,plain,(
% 0.19/0.54    ~v5_relat_1(sK3,sK2) | spl5_12),
% 0.19/0.54    inference(resolution,[],[f519,f114])).
% 0.19/0.54  fof(f114,plain,(
% 0.19/0.54    v2_funct_2(sK3,sK2)),
% 0.19/0.54    inference(resolution,[],[f109,f74])).
% 0.19/0.54  fof(f109,plain,(
% 0.19/0.54    sP1(sK2,sK3)),
% 0.19/0.54    inference(subsumption_resolution,[],[f108,f48])).
% 0.19/0.54  fof(f108,plain,(
% 0.19/0.54    ~v1_funct_1(sK3) | sP1(sK2,sK3)),
% 0.19/0.54    inference(subsumption_resolution,[],[f105,f50])).
% 0.19/0.54  fof(f105,plain,(
% 0.19/0.54    ~v3_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3) | sP1(sK2,sK3)),
% 0.19/0.54    inference(resolution,[],[f75,f51])).
% 0.19/0.54  fof(f519,plain,(
% 0.19/0.54    ( ! [X0] : (~v2_funct_2(sK3,X0) | ~v5_relat_1(sK3,X0)) ) | spl5_12),
% 0.19/0.54    inference(subsumption_resolution,[],[f518,f86])).
% 0.19/0.54  fof(f518,plain,(
% 0.19/0.54    ( ! [X0] : (~v5_relat_1(sK3,X0) | ~v2_funct_2(sK3,X0) | ~v1_relat_1(sK3)) ) | spl5_12),
% 0.19/0.54    inference(duplicate_literal_removal,[],[f517])).
% 0.19/0.54  fof(f517,plain,(
% 0.19/0.54    ( ! [X0] : (~v5_relat_1(sK3,X0) | ~v2_funct_2(sK3,X0) | ~v5_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | spl5_12),
% 0.19/0.54    inference(superposition,[],[f516,f61])).
% 0.19/0.54  fof(f516,plain,(
% 0.19/0.54    ~v5_relat_1(sK3,k2_relat_1(sK3)) | spl5_12),
% 0.19/0.54    inference(subsumption_resolution,[],[f515,f86])).
% 0.19/0.54  fof(f515,plain,(
% 0.19/0.54    ~v5_relat_1(sK3,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | spl5_12),
% 0.19/0.54    inference(subsumption_resolution,[],[f514,f318])).
% 0.19/0.54  fof(f318,plain,(
% 0.19/0.54    sK2 != k2_relat_1(sK3) | spl5_12),
% 0.19/0.54    inference(subsumption_resolution,[],[f317,f51])).
% 0.19/0.54  fof(f317,plain,(
% 0.19/0.54    sK2 != k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | spl5_12),
% 0.19/0.54    inference(superposition,[],[f311,f69])).
% 0.19/0.54  fof(f311,plain,(
% 0.19/0.54    sK2 != k2_relset_1(sK2,sK2,sK3) | spl5_12),
% 0.19/0.54    inference(avatar_component_clause,[],[f309])).
% 0.19/0.54  fof(f514,plain,(
% 0.19/0.54    sK2 = k2_relat_1(sK3) | ~v5_relat_1(sK3,k2_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.19/0.54    inference(duplicate_literal_removal,[],[f513])).
% 0.19/0.54  fof(f513,plain,(
% 0.19/0.54    sK2 = k2_relat_1(sK3) | ~v5_relat_1(sK3,k2_relat_1(sK3)) | ~v5_relat_1(sK3,k2_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.19/0.54    inference(resolution,[],[f463,f81])).
% 0.19/0.54  fof(f463,plain,(
% 0.19/0.54    ( ! [X5] : (~v2_funct_2(sK3,X5) | sK2 = X5 | ~v5_relat_1(sK3,X5)) )),
% 0.19/0.54    inference(subsumption_resolution,[],[f462,f86])).
% 0.19/0.54  fof(f462,plain,(
% 0.19/0.54    ( ! [X5] : (sK2 = X5 | ~v1_relat_1(sK3) | ~v2_funct_2(sK3,X5) | ~v5_relat_1(sK3,X5)) )),
% 0.19/0.54    inference(subsumption_resolution,[],[f453,f90])).
% 0.19/0.54  fof(f453,plain,(
% 0.19/0.54    ( ! [X5] : (sK2 = X5 | ~v5_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | ~v2_funct_2(sK3,X5) | ~v5_relat_1(sK3,X5)) )),
% 0.19/0.54    inference(resolution,[],[f102,f114])).
% 0.19/0.54  fof(f316,plain,(
% 0.19/0.54    ~spl5_12 | spl5_4 | spl5_13),
% 0.19/0.54    inference(avatar_split_clause,[],[f307,f313,f185,f309])).
% 0.19/0.54  fof(f307,plain,(
% 0.19/0.54    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3)),
% 0.19/0.54    inference(subsumption_resolution,[],[f306,f48])).
% 0.19/0.54  fof(f306,plain,(
% 0.19/0.54    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~v1_funct_1(sK3)),
% 0.19/0.54    inference(subsumption_resolution,[],[f305,f49])).
% 0.19/0.54  fof(f305,plain,(
% 0.19/0.54    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.19/0.54    inference(subsumption_resolution,[],[f304,f51])).
% 0.19/0.54  fof(f304,plain,(
% 0.19/0.54    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.19/0.54    inference(subsumption_resolution,[],[f303,f52])).
% 0.19/0.54  fof(f303,plain,(
% 0.19/0.54    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.19/0.54    inference(subsumption_resolution,[],[f302,f53])).
% 0.19/0.54  fof(f53,plain,(
% 0.19/0.54    v1_funct_2(sK4,sK2,sK2)),
% 0.19/0.54    inference(cnf_transformation,[],[f42])).
% 0.19/0.54  fof(f302,plain,(
% 0.19/0.54    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.19/0.54    inference(subsumption_resolution,[],[f301,f55])).
% 0.19/0.54  fof(f301,plain,(
% 0.19/0.54    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.19/0.54    inference(duplicate_literal_removal,[],[f300])).
% 0.19/0.54  fof(f300,plain,(
% 0.19/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.19/0.54    inference(resolution,[],[f299,f56])).
% 0.19/0.54  fof(f56,plain,(
% 0.19/0.54    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2))),
% 0.19/0.54    inference(cnf_transformation,[],[f42])).
% 0.19/0.54  fof(f299,plain,(
% 0.19/0.54    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_funct_1(X2) = X3 | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.19/0.54    inference(subsumption_resolution,[],[f78,f76])).
% 0.19/0.54  fof(f76,plain,(
% 0.19/0.54    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | v2_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f31])).
% 0.19/0.54  fof(f31,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.19/0.54    inference(flattening,[],[f30])).
% 0.19/0.54  fof(f30,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.19/0.54    inference(ennf_transformation,[],[f11])).
% 0.19/0.54  fof(f11,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 0.19/0.54  fof(f78,plain,(
% 0.19/0.54    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f33])).
% 0.19/0.54  fof(f33,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.19/0.54    inference(flattening,[],[f32])).
% 0.19/0.54  fof(f32,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.19/0.54    inference(ennf_transformation,[],[f12])).
% 0.19/0.54  fof(f12,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 0.19/0.54  % SZS output end Proof for theBenchmark
% 0.19/0.54  % (6229)------------------------------
% 0.19/0.54  % (6229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (6229)Termination reason: Refutation
% 0.19/0.54  
% 0.19/0.54  % (6229)Memory used [KB]: 6524
% 0.19/0.54  % (6229)Time elapsed: 0.134 s
% 0.19/0.54  % (6229)------------------------------
% 0.19/0.54  % (6229)------------------------------
% 0.19/0.54  % (6224)Success in time 0.193 s
%------------------------------------------------------------------------------
