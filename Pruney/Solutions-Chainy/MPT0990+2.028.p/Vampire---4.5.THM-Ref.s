%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:33 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  226 (1019 expanded)
%              Number of leaves         :   31 ( 320 expanded)
%              Depth                    :   24
%              Number of atoms          :  920 (9395 expanded)
%              Number of equality atoms :  225 (3194 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f898,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f161,f164,f219,f229,f239,f317,f461,f715,f726,f884,f897])).

fof(f897,plain,
    ( ~ spl4_1
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f896])).

fof(f896,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f895,f179])).

fof(f179,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f136,f63])).

fof(f63,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f53,f52])).

fof(f52,plain,
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

fof(f53,plain,
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f136,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f59,f99])).

% (10279)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f895,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f894,f57])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f894,plain,
    ( ~ v1_funct_1(sK2)
    | sK1 != k2_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f893,f155])).

fof(f155,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f893,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK1 != k2_relat_1(sK2)
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f892,f106])).

fof(f106,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f91,f95])).

fof(f95,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f91,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f892,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK1 != k2_relat_1(sK2)
    | ~ spl4_11 ),
    inference(superposition,[],[f460,f365])).

fof(f365,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f362,f364])).

fof(f364,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f363,f94])).

fof(f94,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f363,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f352,f92])).

% (10271)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f352,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f64,f314])).

fof(f314,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f311,f60])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f311,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f139,f62])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k5_relat_1(sK2,X0) = k1_partfun1(sK0,sK1,X1,X2,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f137,f57])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k5_relat_1(sK2,X0) = k1_partfun1(sK0,sK1,X1,X2,sK2,X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f59,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f64,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f362,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f361,f57])).

fof(f361,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f360,f59])).

fof(f360,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f359,f60])).

fof(f359,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f354,f62])).

fof(f354,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f97,f314])).

fof(f97,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f460,plain,
    ( ! [X1] :
        ( ~ v2_funct_1(k5_relat_1(X1,sK3))
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k2_relat_1(X1) != sK1 )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl4_11
  <=> ! [X1] :
        ( k2_relat_1(X1) != sK1
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(X1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f884,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f883])).

fof(f883,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f866,f68])).

fof(f68,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f54])).

fof(f866,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(backward_demodulation,[],[f481,f863])).

fof(f863,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f862,f695])).

fof(f695,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f694])).

fof(f694,plain,
    ( spl4_16
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f862,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f861,f699])).

fof(f699,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f698])).

fof(f698,plain,
    ( spl4_17
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f861,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f858,f490])).

fof(f490,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f489,f105])).

fof(f105,plain,(
    ! [X0] : k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f81,f95,f95])).

fof(f81,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

fof(f489,plain,
    ( k2_funct_1(k6_partfun1(sK0)) = k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f488,f365])).

fof(f488,plain,
    ( k2_funct_1(k5_relat_1(sK2,sK3)) = k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f487,f302])).

fof(f302,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl4_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f487,plain,
    ( k2_funct_1(k5_relat_1(sK2,sK3)) = k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f469,f60])).

fof(f469,plain,
    ( k2_funct_1(k5_relat_1(sK2,sK3)) = k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_10 ),
    inference(resolution,[],[f457,f230])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | k2_funct_1(k5_relat_1(sK2,X0)) = k5_relat_1(k2_funct_1(X0),k2_funct_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f122,f155])).

fof(f122,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k5_relat_1(sK2,X0)) = k5_relat_1(k2_funct_1(X0),k2_funct_1(sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f115,f57])).

fof(f115,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k5_relat_1(sK2,X0)) = k5_relat_1(k2_funct_1(X0),k2_funct_1(sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f65,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f65,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f457,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f455])).

fof(f455,plain,
    ( spl4_10
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f858,plain,
    ( sK2 = k2_funct_1(sK3)
    | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(trivial_inequality_removal,[],[f857])).

fof(f857,plain,
    ( sK1 != sK1
    | sK2 = k2_funct_1(sK3)
    | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(superposition,[],[f844,f479])).

fof(f479,plain,
    ( sK1 = k2_relat_1(k2_funct_1(sK3))
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f478,f180])).

fof(f180,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f141,f134])).

fof(f134,plain,(
    sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(global_subsumption,[],[f62,f133])).

fof(f133,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f132,f66])).

fof(f66,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f54])).

fof(f132,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f61,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f61,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f141,plain,(
    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f62,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f478,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f477,f302])).

fof(f477,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f465,f60])).

fof(f465,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(resolution,[],[f457,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f844,plain,
    ( ! [X2] :
        ( k2_relat_1(X2) != sK1
        | sK2 = X2
        | k6_partfun1(sK0) != k5_relat_1(X2,k2_funct_1(sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f843,f194])).

fof(f194,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f193,f170])).

fof(f170,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f135,f131])).

fof(f131,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f59,f130])).

fof(f130,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f129,f67])).

fof(f67,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f54])).

fof(f129,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f58,f82])).

fof(f58,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f135,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f59,f101])).

fof(f193,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f125,f155])).

fof(f125,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f118,f57])).

fof(f118,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f65,f74])).

fof(f843,plain,
    ( ! [X2] :
        ( sK2 = X2
        | k2_relat_1(X2) != sK1
        | k5_relat_1(X2,k2_funct_1(sK2)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f842,f209])).

fof(f209,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl4_3
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f842,plain,
    ( ! [X2] :
        ( sK2 = X2
        | k2_relat_1(X2) != sK1
        | k5_relat_1(X2,k2_funct_1(sK2)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f841,f213])).

fof(f213,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl4_4
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f841,plain,
    ( ! [X2] :
        ( sK2 = X2
        | k2_relat_1(X2) != sK1
        | k5_relat_1(X2,k2_funct_1(sK2)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f192,f218])).

fof(f218,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl4_5
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f192,plain,
    ( ! [X2] :
        ( sK2 = X2
        | k2_relat_1(X2) != sK1
        | k5_relat_1(X2,k2_funct_1(sK2)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
        | ~ v2_funct_1(k2_funct_1(sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f191,f160])).

fof(f160,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl4_2
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f191,plain,
    ( ! [X2] :
        ( k2_relat_1(X2) != sK1
        | k5_relat_1(X2,k2_funct_1(sK2)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
        | k2_funct_1(k2_funct_1(sK2)) = X2
        | ~ v2_funct_1(k2_funct_1(sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl4_1 ),
    inference(superposition,[],[f102,f188])).

fof(f188,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f187,f179])).

fof(f187,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f124,f155])).

fof(f124,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f117,f57])).

fof(f117,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f65,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f69,f95])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f481,plain,
    ( sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f480,f302])).

fof(f480,plain,
    ( sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f466,f60])).

fof(f466,plain,
    ( sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(resolution,[],[f457,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f726,plain,
    ( ~ spl4_6
    | spl4_17 ),
    inference(avatar_contradiction_clause,[],[f725])).

fof(f725,plain,
    ( $false
    | ~ spl4_6
    | spl4_17 ),
    inference(subsumption_resolution,[],[f724,f302])).

fof(f724,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f719,f60])).

fof(f719,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_17 ),
    inference(resolution,[],[f700,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f700,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f698])).

fof(f715,plain,
    ( ~ spl4_6
    | spl4_16 ),
    inference(avatar_contradiction_clause,[],[f714])).

fof(f714,plain,
    ( $false
    | ~ spl4_6
    | spl4_16 ),
    inference(subsumption_resolution,[],[f713,f302])).

fof(f713,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_16 ),
    inference(subsumption_resolution,[],[f707,f60])).

fof(f707,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_16 ),
    inference(resolution,[],[f696,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f696,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f694])).

fof(f461,plain,
    ( spl4_10
    | spl4_11
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f441,f301,f459,f455])).

fof(f441,plain,
    ( ! [X1] :
        ( k2_relat_1(X1) != sK1
        | v2_funct_1(sK3)
        | ~ v2_funct_1(k5_relat_1(X1,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f185,f302])).

fof(f185,plain,(
    ! [X1] :
      ( k2_relat_1(X1) != sK1
      | v2_funct_1(sK3)
      | ~ v2_funct_1(k5_relat_1(X1,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f182,f60])).

fof(f182,plain,(
    ! [X1] :
      ( k2_relat_1(X1) != sK1
      | v2_funct_1(sK3)
      | ~ v2_funct_1(k5_relat_1(X1,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f89,f180])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

% (10269)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f317,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | spl4_6 ),
    inference(resolution,[],[f315,f62])).

fof(f315,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_6 ),
    inference(resolution,[],[f303,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f303,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f301])).

fof(f239,plain,
    ( ~ spl4_1
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl4_1
    | spl4_4 ),
    inference(subsumption_resolution,[],[f237,f155])).

fof(f237,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f232,f57])).

fof(f232,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_4 ),
    inference(resolution,[],[f214,f77])).

fof(f214,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f212])).

fof(f229,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl4_1
    | spl4_3 ),
    inference(subsumption_resolution,[],[f227,f155])).

fof(f227,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f221,f57])).

fof(f221,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_3 ),
    inference(resolution,[],[f210,f76])).

fof(f210,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f208])).

fof(f219,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f206,f154,f216,f212,f208])).

fof(f206,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f205,f106])).

fof(f205,plain,
    ( ~ v2_funct_1(k6_partfun1(sK1))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f204,f199])).

fof(f199,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f198,f179])).

fof(f198,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f127,f155])).

fof(f127,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f120,f57])).

fof(f120,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f65,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f72,f95])).

fof(f72,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f204,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f203])).

fof(f203,plain,
    ( sK0 != sK0
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(superposition,[],[f175,f194])).

fof(f175,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != sK0
        | v2_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(X0,sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f174,f155])).

fof(f174,plain,(
    ! [X0] :
      ( k2_relat_1(X0) != sK0
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X0,sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f171,f57])).

fof(f171,plain,(
    ! [X0] :
      ( k2_relat_1(X0) != sK0
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X0,sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f88,f170])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f164,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f162,f59])).

fof(f162,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_1 ),
    inference(resolution,[],[f156,f100])).

fof(f156,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f154])).

fof(f161,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f126,f158,f154])).

fof(f126,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f119,f57])).

fof(f119,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f65,f75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:03:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.56  % (10270)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.52/0.57  % (10276)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.52/0.58  % (10282)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.52/0.58  % (10288)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.52/0.58  % (10272)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.52/0.58  % (10277)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.52/0.58  % (10275)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.52/0.58  % (10283)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.52/0.58  % (10284)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.73/0.59  % (10297)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.73/0.59  % (10293)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.73/0.59  % (10285)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.73/0.59  % (10294)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.73/0.59  % (10286)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.73/0.59  % (10298)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.73/0.59  % (10286)Refutation not found, incomplete strategy% (10286)------------------------------
% 1.73/0.59  % (10286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.59  % (10290)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.73/0.60  % (10291)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.73/0.60  % (10286)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.60  
% 1.73/0.60  % (10286)Memory used [KB]: 10746
% 1.73/0.60  % (10286)Time elapsed: 0.153 s
% 1.73/0.60  % (10286)------------------------------
% 1.73/0.60  % (10286)------------------------------
% 1.73/0.61  % (10280)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.73/0.62  % (10287)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.73/0.62  % (10268)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.73/0.63  % (10292)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.73/0.63  % (10295)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.73/0.64  % (10299)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.73/0.64  % (10294)Refutation found. Thanks to Tanya!
% 1.73/0.64  % SZS status Theorem for theBenchmark
% 1.73/0.64  % (10274)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.73/0.64  % SZS output start Proof for theBenchmark
% 1.73/0.64  fof(f898,plain,(
% 1.73/0.64    $false),
% 1.73/0.64    inference(avatar_sat_refutation,[],[f161,f164,f219,f229,f239,f317,f461,f715,f726,f884,f897])).
% 1.73/0.64  fof(f897,plain,(
% 1.73/0.64    ~spl4_1 | ~spl4_11),
% 1.73/0.64    inference(avatar_contradiction_clause,[],[f896])).
% 1.73/0.65  fof(f896,plain,(
% 1.73/0.65    $false | (~spl4_1 | ~spl4_11)),
% 1.73/0.65    inference(subsumption_resolution,[],[f895,f179])).
% 1.73/0.65  fof(f179,plain,(
% 1.73/0.65    sK1 = k2_relat_1(sK2)),
% 1.73/0.65    inference(forward_demodulation,[],[f136,f63])).
% 1.73/0.65  fof(f63,plain,(
% 1.73/0.65    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.73/0.65    inference(cnf_transformation,[],[f54])).
% 1.73/0.65  fof(f54,plain,(
% 1.73/0.65    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.73/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f53,f52])).
% 1.73/0.65  fof(f52,plain,(
% 1.73/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.73/0.65    introduced(choice_axiom,[])).
% 1.73/0.65  fof(f53,plain,(
% 1.73/0.65    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.73/0.65    introduced(choice_axiom,[])).
% 1.73/0.65  fof(f24,plain,(
% 1.73/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.73/0.65    inference(flattening,[],[f23])).
% 1.73/0.65  fof(f23,plain,(
% 1.73/0.65    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.73/0.65    inference(ennf_transformation,[],[f21])).
% 1.73/0.65  fof(f21,negated_conjecture,(
% 1.73/0.65    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.73/0.65    inference(negated_conjecture,[],[f20])).
% 1.73/0.65  fof(f20,conjecture,(
% 1.73/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.73/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.73/0.65  fof(f136,plain,(
% 1.73/0.65    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.73/0.65    inference(resolution,[],[f59,f99])).
% 1.73/0.65  % (10279)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.73/0.65  fof(f99,plain,(
% 1.73/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.73/0.65    inference(cnf_transformation,[],[f49])).
% 1.73/0.65  fof(f49,plain,(
% 1.73/0.65    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.73/0.65    inference(ennf_transformation,[],[f13])).
% 1.73/0.65  fof(f13,axiom,(
% 1.73/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.73/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.73/0.65  fof(f59,plain,(
% 1.73/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.73/0.65    inference(cnf_transformation,[],[f54])).
% 1.73/0.65  fof(f895,plain,(
% 1.73/0.65    sK1 != k2_relat_1(sK2) | (~spl4_1 | ~spl4_11)),
% 1.73/0.65    inference(subsumption_resolution,[],[f894,f57])).
% 1.73/0.65  fof(f57,plain,(
% 1.73/0.65    v1_funct_1(sK2)),
% 1.73/0.65    inference(cnf_transformation,[],[f54])).
% 1.73/0.65  fof(f894,plain,(
% 1.73/0.65    ~v1_funct_1(sK2) | sK1 != k2_relat_1(sK2) | (~spl4_1 | ~spl4_11)),
% 1.73/0.65    inference(subsumption_resolution,[],[f893,f155])).
% 1.73/0.65  fof(f155,plain,(
% 1.73/0.65    v1_relat_1(sK2) | ~spl4_1),
% 1.73/0.65    inference(avatar_component_clause,[],[f154])).
% 1.73/0.65  fof(f154,plain,(
% 1.73/0.65    spl4_1 <=> v1_relat_1(sK2)),
% 1.73/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.73/0.65  fof(f893,plain,(
% 1.73/0.65    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK1 != k2_relat_1(sK2) | ~spl4_11),
% 1.73/0.65    inference(subsumption_resolution,[],[f892,f106])).
% 1.73/0.65  fof(f106,plain,(
% 1.73/0.65    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.73/0.65    inference(definition_unfolding,[],[f91,f95])).
% 1.73/0.65  fof(f95,plain,(
% 1.73/0.65    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.73/0.65    inference(cnf_transformation,[],[f19])).
% 1.73/0.65  fof(f19,axiom,(
% 1.73/0.65    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.73/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.73/0.65  fof(f91,plain,(
% 1.73/0.65    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.73/0.65    inference(cnf_transformation,[],[f2])).
% 1.73/0.65  fof(f2,axiom,(
% 1.73/0.65    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.73/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.73/0.65  fof(f892,plain,(
% 1.73/0.65    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK1 != k2_relat_1(sK2) | ~spl4_11),
% 1.73/0.65    inference(superposition,[],[f460,f365])).
% 1.73/0.65  fof(f365,plain,(
% 1.73/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.73/0.65    inference(global_subsumption,[],[f362,f364])).
% 1.73/0.65  fof(f364,plain,(
% 1.73/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.73/0.65    inference(subsumption_resolution,[],[f363,f94])).
% 1.73/0.65  fof(f94,plain,(
% 1.73/0.65    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.73/0.65    inference(cnf_transformation,[],[f22])).
% 1.73/0.65  fof(f22,plain,(
% 1.73/0.65    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.73/0.65    inference(pure_predicate_removal,[],[f17])).
% 1.73/0.65  fof(f17,axiom,(
% 1.73/0.65    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.73/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.73/0.65  fof(f363,plain,(
% 1.73/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.73/0.65    inference(resolution,[],[f352,f92])).
% 1.73/0.65  % (10271)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.73/0.65  fof(f92,plain,(
% 1.73/0.65    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.73/0.65    inference(cnf_transformation,[],[f56])).
% 1.73/0.65  fof(f56,plain,(
% 1.73/0.65    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.73/0.65    inference(nnf_transformation,[],[f44])).
% 1.73/0.65  fof(f44,plain,(
% 1.73/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.73/0.65    inference(flattening,[],[f43])).
% 1.73/0.65  fof(f43,plain,(
% 1.73/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.73/0.65    inference(ennf_transformation,[],[f14])).
% 1.73/0.65  fof(f14,axiom,(
% 1.73/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.73/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.73/0.65  fof(f352,plain,(
% 1.73/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.73/0.65    inference(backward_demodulation,[],[f64,f314])).
% 1.73/0.65  fof(f314,plain,(
% 1.73/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.73/0.65    inference(subsumption_resolution,[],[f311,f60])).
% 1.73/0.65  fof(f60,plain,(
% 1.73/0.65    v1_funct_1(sK3)),
% 1.73/0.65    inference(cnf_transformation,[],[f54])).
% 1.73/0.65  fof(f311,plain,(
% 1.73/0.65    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.73/0.65    inference(resolution,[],[f139,f62])).
% 1.73/0.65  fof(f62,plain,(
% 1.73/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.73/0.65    inference(cnf_transformation,[],[f54])).
% 1.73/0.65  fof(f139,plain,(
% 1.73/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k5_relat_1(sK2,X0) = k1_partfun1(sK0,sK1,X1,X2,sK2,X0)) )),
% 1.73/0.65    inference(subsumption_resolution,[],[f137,f57])).
% 1.73/0.65  fof(f137,plain,(
% 1.73/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k5_relat_1(sK2,X0) = k1_partfun1(sK0,sK1,X1,X2,sK2,X0) | ~v1_funct_1(sK2)) )),
% 1.73/0.65    inference(resolution,[],[f59,f98])).
% 1.73/0.65  fof(f98,plain,(
% 1.73/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 1.73/0.65    inference(cnf_transformation,[],[f48])).
% 1.73/0.65  fof(f48,plain,(
% 1.73/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.73/0.65    inference(flattening,[],[f47])).
% 1.73/0.65  fof(f47,plain,(
% 1.73/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.73/0.65    inference(ennf_transformation,[],[f18])).
% 1.73/0.65  fof(f18,axiom,(
% 1.73/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.73/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.73/0.65  fof(f64,plain,(
% 1.73/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.73/0.65    inference(cnf_transformation,[],[f54])).
% 1.73/0.65  fof(f362,plain,(
% 1.73/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.73/0.65    inference(subsumption_resolution,[],[f361,f57])).
% 1.73/0.65  fof(f361,plain,(
% 1.73/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.73/0.65    inference(subsumption_resolution,[],[f360,f59])).
% 1.73/0.65  fof(f360,plain,(
% 1.73/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.73/0.65    inference(subsumption_resolution,[],[f359,f60])).
% 1.73/0.65  fof(f359,plain,(
% 1.73/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.73/0.65    inference(subsumption_resolution,[],[f354,f62])).
% 1.73/0.65  fof(f354,plain,(
% 1.73/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.73/0.65    inference(superposition,[],[f97,f314])).
% 1.73/0.65  fof(f97,plain,(
% 1.73/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.73/0.65    inference(cnf_transformation,[],[f46])).
% 1.73/0.65  fof(f46,plain,(
% 1.73/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.73/0.65    inference(flattening,[],[f45])).
% 1.73/0.65  fof(f45,plain,(
% 1.73/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.73/0.65    inference(ennf_transformation,[],[f16])).
% 1.73/0.65  fof(f16,axiom,(
% 1.73/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.73/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.73/0.65  fof(f460,plain,(
% 1.73/0.65    ( ! [X1] : (~v2_funct_1(k5_relat_1(X1,sK3)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X1) != sK1) ) | ~spl4_11),
% 1.73/0.65    inference(avatar_component_clause,[],[f459])).
% 1.73/0.65  fof(f459,plain,(
% 1.73/0.65    spl4_11 <=> ! [X1] : (k2_relat_1(X1) != sK1 | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,sK3)))),
% 1.73/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.73/0.65  fof(f884,plain,(
% 1.73/0.65    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_10 | ~spl4_16 | ~spl4_17),
% 1.73/0.65    inference(avatar_contradiction_clause,[],[f883])).
% 1.73/0.65  fof(f883,plain,(
% 1.73/0.65    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_10 | ~spl4_16 | ~spl4_17)),
% 1.73/0.65    inference(subsumption_resolution,[],[f866,f68])).
% 1.73/0.65  fof(f68,plain,(
% 1.73/0.65    k2_funct_1(sK2) != sK3),
% 1.73/0.65    inference(cnf_transformation,[],[f54])).
% 1.73/0.65  fof(f866,plain,(
% 1.73/0.65    k2_funct_1(sK2) = sK3 | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_10 | ~spl4_16 | ~spl4_17)),
% 1.73/0.65    inference(backward_demodulation,[],[f481,f863])).
% 1.73/0.65  fof(f863,plain,(
% 1.73/0.65    sK2 = k2_funct_1(sK3) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_10 | ~spl4_16 | ~spl4_17)),
% 1.73/0.65    inference(subsumption_resolution,[],[f862,f695])).
% 1.73/0.65  fof(f695,plain,(
% 1.73/0.65    v1_relat_1(k2_funct_1(sK3)) | ~spl4_16),
% 1.73/0.65    inference(avatar_component_clause,[],[f694])).
% 1.73/0.65  fof(f694,plain,(
% 1.73/0.65    spl4_16 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.73/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.73/0.65  fof(f862,plain,(
% 1.73/0.65    sK2 = k2_funct_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_10 | ~spl4_17)),
% 1.73/0.65    inference(subsumption_resolution,[],[f861,f699])).
% 1.73/0.65  fof(f699,plain,(
% 1.73/0.65    v1_funct_1(k2_funct_1(sK3)) | ~spl4_17),
% 1.73/0.65    inference(avatar_component_clause,[],[f698])).
% 1.73/0.65  fof(f698,plain,(
% 1.73/0.65    spl4_17 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.73/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.73/0.65  fof(f861,plain,(
% 1.73/0.65    sK2 = k2_funct_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_10)),
% 1.73/0.65    inference(subsumption_resolution,[],[f858,f490])).
% 1.73/0.65  fof(f490,plain,(
% 1.73/0.65    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) | (~spl4_1 | ~spl4_6 | ~spl4_10)),
% 1.73/0.65    inference(forward_demodulation,[],[f489,f105])).
% 1.73/0.65  fof(f105,plain,(
% 1.73/0.65    ( ! [X0] : (k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))) )),
% 1.73/0.65    inference(definition_unfolding,[],[f81,f95,f95])).
% 1.73/0.65  fof(f81,plain,(
% 1.73/0.65    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 1.73/0.65    inference(cnf_transformation,[],[f10])).
% 1.73/0.65  fof(f10,axiom,(
% 1.73/0.65    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 1.73/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).
% 1.73/0.65  fof(f489,plain,(
% 1.73/0.65    k2_funct_1(k6_partfun1(sK0)) = k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) | (~spl4_1 | ~spl4_6 | ~spl4_10)),
% 1.73/0.65    inference(forward_demodulation,[],[f488,f365])).
% 1.73/0.65  fof(f488,plain,(
% 1.73/0.65    k2_funct_1(k5_relat_1(sK2,sK3)) = k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) | (~spl4_1 | ~spl4_6 | ~spl4_10)),
% 1.73/0.65    inference(subsumption_resolution,[],[f487,f302])).
% 1.73/0.65  fof(f302,plain,(
% 1.73/0.65    v1_relat_1(sK3) | ~spl4_6),
% 1.73/0.65    inference(avatar_component_clause,[],[f301])).
% 1.73/0.65  fof(f301,plain,(
% 1.73/0.65    spl4_6 <=> v1_relat_1(sK3)),
% 1.73/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.73/0.65  fof(f487,plain,(
% 1.73/0.65    k2_funct_1(k5_relat_1(sK2,sK3)) = k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_10)),
% 1.73/0.65    inference(subsumption_resolution,[],[f469,f60])).
% 1.73/0.65  fof(f469,plain,(
% 1.73/0.65    k2_funct_1(k5_relat_1(sK2,sK3)) = k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_10)),
% 1.73/0.65    inference(resolution,[],[f457,f230])).
% 1.73/0.65  fof(f230,plain,(
% 1.73/0.65    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k5_relat_1(sK2,X0)) = k5_relat_1(k2_funct_1(X0),k2_funct_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl4_1),
% 1.73/0.65    inference(subsumption_resolution,[],[f122,f155])).
% 1.73/0.65  fof(f122,plain,(
% 1.73/0.65    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k5_relat_1(sK2,X0)) = k5_relat_1(k2_funct_1(X0),k2_funct_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 1.73/0.65    inference(subsumption_resolution,[],[f115,f57])).
% 1.73/0.65  fof(f115,plain,(
% 1.73/0.65    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k5_relat_1(sK2,X0)) = k5_relat_1(k2_funct_1(X0),k2_funct_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.73/0.65    inference(resolution,[],[f65,f70])).
% 1.73/0.65  fof(f70,plain,(
% 1.73/0.65    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v2_funct_1(X0) | k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.73/0.65    inference(cnf_transformation,[],[f28])).
% 1.73/0.65  fof(f28,plain,(
% 1.73/0.65    ! [X0] : (! [X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.73/0.65    inference(flattening,[],[f27])).
% 1.73/0.65  fof(f27,plain,(
% 1.73/0.65    ! [X0] : (! [X1] : ((k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.73/0.65    inference(ennf_transformation,[],[f9])).
% 1.73/0.65  fof(f9,axiom,(
% 1.73/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 1.73/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).
% 1.73/0.65  fof(f65,plain,(
% 1.73/0.65    v2_funct_1(sK2)),
% 1.73/0.65    inference(cnf_transformation,[],[f54])).
% 1.73/0.65  fof(f457,plain,(
% 1.73/0.65    v2_funct_1(sK3) | ~spl4_10),
% 1.73/0.65    inference(avatar_component_clause,[],[f455])).
% 1.73/0.65  fof(f455,plain,(
% 1.73/0.65    spl4_10 <=> v2_funct_1(sK3)),
% 1.73/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.73/0.65  fof(f858,plain,(
% 1.73/0.65    sK2 = k2_funct_1(sK3) | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_10)),
% 1.73/0.65    inference(trivial_inequality_removal,[],[f857])).
% 1.73/0.65  fof(f857,plain,(
% 1.73/0.65    sK1 != sK1 | sK2 = k2_funct_1(sK3) | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_10)),
% 1.73/0.65    inference(superposition,[],[f844,f479])).
% 1.73/0.65  fof(f479,plain,(
% 1.73/0.65    sK1 = k2_relat_1(k2_funct_1(sK3)) | (~spl4_6 | ~spl4_10)),
% 1.73/0.65    inference(forward_demodulation,[],[f478,f180])).
% 1.73/0.65  fof(f180,plain,(
% 1.73/0.65    sK1 = k1_relat_1(sK3)),
% 1.73/0.65    inference(forward_demodulation,[],[f141,f134])).
% 1.73/0.65  fof(f134,plain,(
% 1.73/0.65    sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.73/0.65    inference(global_subsumption,[],[f62,f133])).
% 1.73/0.65  fof(f133,plain,(
% 1.73/0.65    sK1 = k1_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.73/0.65    inference(subsumption_resolution,[],[f132,f66])).
% 1.73/0.65  fof(f66,plain,(
% 1.73/0.65    k1_xboole_0 != sK0),
% 1.73/0.65    inference(cnf_transformation,[],[f54])).
% 1.73/0.65  fof(f132,plain,(
% 1.73/0.65    sK1 = k1_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.73/0.65    inference(resolution,[],[f61,f82])).
% 1.73/0.65  fof(f82,plain,(
% 1.73/0.65    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.73/0.65    inference(cnf_transformation,[],[f55])).
% 1.73/0.65  fof(f55,plain,(
% 1.73/0.65    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.73/0.65    inference(nnf_transformation,[],[f40])).
% 1.73/0.65  fof(f40,plain,(
% 1.73/0.65    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.73/0.65    inference(flattening,[],[f39])).
% 1.73/0.65  fof(f39,plain,(
% 1.73/0.65    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.73/0.65    inference(ennf_transformation,[],[f15])).
% 1.73/0.65  fof(f15,axiom,(
% 1.73/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.73/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.73/0.65  fof(f61,plain,(
% 1.73/0.65    v1_funct_2(sK3,sK1,sK0)),
% 1.73/0.65    inference(cnf_transformation,[],[f54])).
% 1.73/0.65  fof(f141,plain,(
% 1.73/0.65    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)),
% 1.73/0.65    inference(resolution,[],[f62,f101])).
% 1.73/0.65  fof(f101,plain,(
% 1.73/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.73/0.65    inference(cnf_transformation,[],[f51])).
% 1.73/0.65  fof(f51,plain,(
% 1.73/0.65    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.73/0.65    inference(ennf_transformation,[],[f12])).
% 1.73/0.65  fof(f12,axiom,(
% 1.73/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.73/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.73/0.65  fof(f478,plain,(
% 1.73/0.65    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | (~spl4_6 | ~spl4_10)),
% 1.73/0.65    inference(subsumption_resolution,[],[f477,f302])).
% 1.73/0.65  fof(f477,plain,(
% 1.73/0.65    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~spl4_10),
% 1.73/0.65    inference(subsumption_resolution,[],[f465,f60])).
% 1.73/0.65  fof(f465,plain,(
% 1.73/0.65    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_10),
% 1.73/0.65    inference(resolution,[],[f457,f74])).
% 1.73/0.65  fof(f74,plain,(
% 1.73/0.65    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.73/0.65    inference(cnf_transformation,[],[f32])).
% 1.73/0.65  fof(f32,plain,(
% 1.73/0.65    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.73/0.65    inference(flattening,[],[f31])).
% 1.73/0.65  fof(f31,plain,(
% 1.73/0.65    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.73/0.65    inference(ennf_transformation,[],[f5])).
% 1.73/0.65  fof(f5,axiom,(
% 1.73/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.73/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.73/0.65  fof(f844,plain,(
% 1.73/0.65    ( ! [X2] : (k2_relat_1(X2) != sK1 | sK2 = X2 | k6_partfun1(sK0) != k5_relat_1(X2,k2_funct_1(sK2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.73/0.65    inference(forward_demodulation,[],[f843,f194])).
% 1.73/0.65  fof(f194,plain,(
% 1.73/0.65    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 1.73/0.65    inference(forward_demodulation,[],[f193,f170])).
% 1.73/0.65  fof(f170,plain,(
% 1.73/0.65    sK0 = k1_relat_1(sK2)),
% 1.73/0.65    inference(forward_demodulation,[],[f135,f131])).
% 1.73/0.65  fof(f131,plain,(
% 1.73/0.65    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.73/0.65    inference(global_subsumption,[],[f59,f130])).
% 1.73/0.65  fof(f130,plain,(
% 1.73/0.65    sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.73/0.65    inference(subsumption_resolution,[],[f129,f67])).
% 1.73/0.65  fof(f67,plain,(
% 1.73/0.65    k1_xboole_0 != sK1),
% 1.73/0.65    inference(cnf_transformation,[],[f54])).
% 1.73/0.65  fof(f129,plain,(
% 1.73/0.65    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.73/0.65    inference(resolution,[],[f58,f82])).
% 1.73/0.65  fof(f58,plain,(
% 1.73/0.65    v1_funct_2(sK2,sK0,sK1)),
% 1.73/0.65    inference(cnf_transformation,[],[f54])).
% 1.73/0.65  fof(f135,plain,(
% 1.73/0.65    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.73/0.65    inference(resolution,[],[f59,f101])).
% 1.73/0.65  fof(f193,plain,(
% 1.73/0.65    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 1.73/0.65    inference(subsumption_resolution,[],[f125,f155])).
% 1.73/0.65  fof(f125,plain,(
% 1.73/0.65    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.73/0.65    inference(subsumption_resolution,[],[f118,f57])).
% 1.73/0.65  fof(f118,plain,(
% 1.73/0.65    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.73/0.65    inference(resolution,[],[f65,f74])).
% 1.73/0.65  fof(f843,plain,(
% 1.73/0.65    ( ! [X2] : (sK2 = X2 | k2_relat_1(X2) != sK1 | k5_relat_1(X2,k2_funct_1(sK2)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.73/0.65    inference(subsumption_resolution,[],[f842,f209])).
% 1.73/0.65  fof(f209,plain,(
% 1.73/0.65    v1_relat_1(k2_funct_1(sK2)) | ~spl4_3),
% 1.73/0.65    inference(avatar_component_clause,[],[f208])).
% 1.73/0.65  fof(f208,plain,(
% 1.73/0.65    spl4_3 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.73/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.73/0.66  fof(f842,plain,(
% 1.73/0.66    ( ! [X2] : (sK2 = X2 | k2_relat_1(X2) != sK1 | k5_relat_1(X2,k2_funct_1(sK2)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.73/0.66    inference(subsumption_resolution,[],[f841,f213])).
% 1.73/0.66  fof(f213,plain,(
% 1.73/0.66    v1_funct_1(k2_funct_1(sK2)) | ~spl4_4),
% 1.73/0.66    inference(avatar_component_clause,[],[f212])).
% 1.73/0.66  fof(f212,plain,(
% 1.73/0.66    spl4_4 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.73/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.73/0.66  fof(f841,plain,(
% 1.73/0.66    ( ! [X2] : (sK2 = X2 | k2_relat_1(X2) != sK1 | k5_relat_1(X2,k2_funct_1(sK2)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl4_1 | ~spl4_2 | ~spl4_5)),
% 1.73/0.66    inference(subsumption_resolution,[],[f192,f218])).
% 1.73/0.66  fof(f218,plain,(
% 1.73/0.66    v2_funct_1(k2_funct_1(sK2)) | ~spl4_5),
% 1.73/0.66    inference(avatar_component_clause,[],[f216])).
% 1.73/0.66  fof(f216,plain,(
% 1.73/0.66    spl4_5 <=> v2_funct_1(k2_funct_1(sK2))),
% 1.73/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.73/0.66  fof(f192,plain,(
% 1.73/0.66    ( ! [X2] : (sK2 = X2 | k2_relat_1(X2) != sK1 | k5_relat_1(X2,k2_funct_1(sK2)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2))) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl4_1 | ~spl4_2)),
% 1.73/0.66    inference(forward_demodulation,[],[f191,f160])).
% 1.73/0.66  fof(f160,plain,(
% 1.73/0.66    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl4_2),
% 1.73/0.66    inference(avatar_component_clause,[],[f158])).
% 1.73/0.66  fof(f158,plain,(
% 1.73/0.66    spl4_2 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.73/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.73/0.66  fof(f191,plain,(
% 1.73/0.66    ( ! [X2] : (k2_relat_1(X2) != sK1 | k5_relat_1(X2,k2_funct_1(sK2)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2))) | k2_funct_1(k2_funct_1(sK2)) = X2 | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | ~spl4_1),
% 1.73/0.66    inference(superposition,[],[f102,f188])).
% 1.73/0.66  fof(f188,plain,(
% 1.73/0.66    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 1.73/0.66    inference(forward_demodulation,[],[f187,f179])).
% 1.73/0.66  fof(f187,plain,(
% 1.73/0.66    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 1.73/0.66    inference(subsumption_resolution,[],[f124,f155])).
% 1.73/0.66  fof(f124,plain,(
% 1.73/0.66    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.73/0.66    inference(subsumption_resolution,[],[f117,f57])).
% 1.73/0.66  fof(f117,plain,(
% 1.73/0.66    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.73/0.66    inference(resolution,[],[f65,f73])).
% 1.73/0.66  fof(f73,plain,(
% 1.73/0.66    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.73/0.66    inference(cnf_transformation,[],[f32])).
% 1.73/0.66  fof(f102,plain,(
% 1.73/0.66    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.73/0.66    inference(definition_unfolding,[],[f69,f95])).
% 1.73/0.66  fof(f69,plain,(
% 1.73/0.66    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.73/0.66    inference(cnf_transformation,[],[f26])).
% 1.73/0.66  fof(f26,plain,(
% 1.73/0.66    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.73/0.66    inference(flattening,[],[f25])).
% 1.73/0.66  fof(f25,plain,(
% 1.73/0.66    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.73/0.66    inference(ennf_transformation,[],[f7])).
% 1.73/0.66  fof(f7,axiom,(
% 1.73/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.73/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.73/0.66  fof(f481,plain,(
% 1.73/0.66    sK3 = k2_funct_1(k2_funct_1(sK3)) | (~spl4_6 | ~spl4_10)),
% 1.73/0.66    inference(subsumption_resolution,[],[f480,f302])).
% 1.73/0.66  fof(f480,plain,(
% 1.73/0.66    sK3 = k2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~spl4_10),
% 1.73/0.66    inference(subsumption_resolution,[],[f466,f60])).
% 1.73/0.66  fof(f466,plain,(
% 1.73/0.66    sK3 = k2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_10),
% 1.73/0.66    inference(resolution,[],[f457,f75])).
% 1.73/0.66  fof(f75,plain,(
% 1.73/0.66    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.73/0.66    inference(cnf_transformation,[],[f34])).
% 1.73/0.66  fof(f34,plain,(
% 1.73/0.66    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.73/0.66    inference(flattening,[],[f33])).
% 1.73/0.66  fof(f33,plain,(
% 1.73/0.66    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.73/0.66    inference(ennf_transformation,[],[f8])).
% 1.73/0.66  fof(f8,axiom,(
% 1.73/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.73/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 1.73/0.66  fof(f726,plain,(
% 1.73/0.66    ~spl4_6 | spl4_17),
% 1.73/0.66    inference(avatar_contradiction_clause,[],[f725])).
% 1.73/0.66  fof(f725,plain,(
% 1.73/0.66    $false | (~spl4_6 | spl4_17)),
% 1.73/0.66    inference(subsumption_resolution,[],[f724,f302])).
% 1.73/0.66  fof(f724,plain,(
% 1.73/0.66    ~v1_relat_1(sK3) | spl4_17),
% 1.73/0.66    inference(subsumption_resolution,[],[f719,f60])).
% 1.73/0.66  fof(f719,plain,(
% 1.73/0.66    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_17),
% 1.73/0.66    inference(resolution,[],[f700,f77])).
% 1.73/0.66  fof(f77,plain,(
% 1.73/0.66    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.73/0.66    inference(cnf_transformation,[],[f36])).
% 1.73/0.66  fof(f36,plain,(
% 1.73/0.66    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.73/0.66    inference(flattening,[],[f35])).
% 1.73/0.66  fof(f35,plain,(
% 1.73/0.66    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.73/0.66    inference(ennf_transformation,[],[f1])).
% 1.73/0.66  fof(f1,axiom,(
% 1.73/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.73/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.73/0.66  fof(f700,plain,(
% 1.73/0.66    ~v1_funct_1(k2_funct_1(sK3)) | spl4_17),
% 1.73/0.66    inference(avatar_component_clause,[],[f698])).
% 1.73/0.66  fof(f715,plain,(
% 1.73/0.66    ~spl4_6 | spl4_16),
% 1.73/0.66    inference(avatar_contradiction_clause,[],[f714])).
% 1.73/0.66  fof(f714,plain,(
% 1.73/0.66    $false | (~spl4_6 | spl4_16)),
% 1.73/0.66    inference(subsumption_resolution,[],[f713,f302])).
% 1.73/0.66  fof(f713,plain,(
% 1.73/0.66    ~v1_relat_1(sK3) | spl4_16),
% 1.73/0.66    inference(subsumption_resolution,[],[f707,f60])).
% 1.73/0.66  fof(f707,plain,(
% 1.73/0.66    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_16),
% 1.73/0.66    inference(resolution,[],[f696,f76])).
% 1.73/0.66  fof(f76,plain,(
% 1.73/0.66    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.73/0.66    inference(cnf_transformation,[],[f36])).
% 1.73/0.66  fof(f696,plain,(
% 1.73/0.66    ~v1_relat_1(k2_funct_1(sK3)) | spl4_16),
% 1.73/0.66    inference(avatar_component_clause,[],[f694])).
% 1.73/0.66  fof(f461,plain,(
% 1.73/0.66    spl4_10 | spl4_11 | ~spl4_6),
% 1.73/0.66    inference(avatar_split_clause,[],[f441,f301,f459,f455])).
% 1.73/0.66  fof(f441,plain,(
% 1.73/0.66    ( ! [X1] : (k2_relat_1(X1) != sK1 | v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(X1,sK3)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl4_6),
% 1.73/0.66    inference(subsumption_resolution,[],[f185,f302])).
% 1.73/0.66  fof(f185,plain,(
% 1.73/0.66    ( ! [X1] : (k2_relat_1(X1) != sK1 | v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(X1,sK3)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK3)) )),
% 1.73/0.66    inference(subsumption_resolution,[],[f182,f60])).
% 1.73/0.66  fof(f182,plain,(
% 1.73/0.66    ( ! [X1] : (k2_relat_1(X1) != sK1 | v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(X1,sK3)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.73/0.66    inference(superposition,[],[f89,f180])).
% 1.73/0.66  fof(f89,plain,(
% 1.73/0.66    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.73/0.66    inference(cnf_transformation,[],[f42])).
% 1.73/0.66  fof(f42,plain,(
% 1.73/0.66    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.73/0.66    inference(flattening,[],[f41])).
% 1.73/0.66  fof(f41,plain,(
% 1.73/0.66    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.73/0.66    inference(ennf_transformation,[],[f4])).
% 1.73/0.66  % (10269)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.73/0.66  fof(f4,axiom,(
% 1.73/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.73/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 1.73/0.66  fof(f317,plain,(
% 1.73/0.66    spl4_6),
% 1.73/0.66    inference(avatar_contradiction_clause,[],[f316])).
% 1.73/0.66  fof(f316,plain,(
% 1.73/0.66    $false | spl4_6),
% 1.73/0.66    inference(resolution,[],[f315,f62])).
% 1.73/0.66  fof(f315,plain,(
% 1.73/0.66    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_6),
% 1.73/0.66    inference(resolution,[],[f303,f100])).
% 1.73/0.66  fof(f100,plain,(
% 1.73/0.66    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.73/0.66    inference(cnf_transformation,[],[f50])).
% 1.73/0.66  fof(f50,plain,(
% 1.73/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.73/0.66    inference(ennf_transformation,[],[f11])).
% 1.73/0.66  fof(f11,axiom,(
% 1.73/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.73/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.73/0.66  fof(f303,plain,(
% 1.73/0.66    ~v1_relat_1(sK3) | spl4_6),
% 1.73/0.66    inference(avatar_component_clause,[],[f301])).
% 1.73/0.66  fof(f239,plain,(
% 1.73/0.66    ~spl4_1 | spl4_4),
% 1.73/0.66    inference(avatar_contradiction_clause,[],[f238])).
% 1.73/0.66  fof(f238,plain,(
% 1.73/0.66    $false | (~spl4_1 | spl4_4)),
% 1.73/0.66    inference(subsumption_resolution,[],[f237,f155])).
% 1.73/0.66  fof(f237,plain,(
% 1.73/0.66    ~v1_relat_1(sK2) | spl4_4),
% 1.73/0.66    inference(subsumption_resolution,[],[f232,f57])).
% 1.73/0.66  fof(f232,plain,(
% 1.73/0.66    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_4),
% 1.73/0.66    inference(resolution,[],[f214,f77])).
% 1.73/0.66  fof(f214,plain,(
% 1.73/0.66    ~v1_funct_1(k2_funct_1(sK2)) | spl4_4),
% 1.73/0.66    inference(avatar_component_clause,[],[f212])).
% 1.73/0.66  fof(f229,plain,(
% 1.73/0.66    ~spl4_1 | spl4_3),
% 1.73/0.66    inference(avatar_contradiction_clause,[],[f228])).
% 1.73/0.66  fof(f228,plain,(
% 1.73/0.66    $false | (~spl4_1 | spl4_3)),
% 1.73/0.66    inference(subsumption_resolution,[],[f227,f155])).
% 1.73/0.66  fof(f227,plain,(
% 1.73/0.66    ~v1_relat_1(sK2) | spl4_3),
% 1.73/0.66    inference(subsumption_resolution,[],[f221,f57])).
% 1.73/0.66  fof(f221,plain,(
% 1.73/0.66    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_3),
% 1.73/0.66    inference(resolution,[],[f210,f76])).
% 1.73/0.66  fof(f210,plain,(
% 1.73/0.66    ~v1_relat_1(k2_funct_1(sK2)) | spl4_3),
% 1.73/0.66    inference(avatar_component_clause,[],[f208])).
% 1.73/0.66  fof(f219,plain,(
% 1.73/0.66    ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_1),
% 1.73/0.66    inference(avatar_split_clause,[],[f206,f154,f216,f212,f208])).
% 1.73/0.66  fof(f206,plain,(
% 1.73/0.66    v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 1.73/0.66    inference(subsumption_resolution,[],[f205,f106])).
% 1.73/0.66  fof(f205,plain,(
% 1.73/0.66    ~v2_funct_1(k6_partfun1(sK1)) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 1.73/0.66    inference(forward_demodulation,[],[f204,f199])).
% 1.73/0.66  fof(f199,plain,(
% 1.73/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~spl4_1),
% 1.73/0.66    inference(forward_demodulation,[],[f198,f179])).
% 1.73/0.66  fof(f198,plain,(
% 1.73/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) | ~spl4_1),
% 1.73/0.66    inference(subsumption_resolution,[],[f127,f155])).
% 1.73/0.66  fof(f127,plain,(
% 1.73/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.73/0.66    inference(subsumption_resolution,[],[f120,f57])).
% 1.73/0.66  fof(f120,plain,(
% 1.73/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.73/0.66    inference(resolution,[],[f65,f103])).
% 1.73/0.66  fof(f103,plain,(
% 1.73/0.66    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.73/0.66    inference(definition_unfolding,[],[f72,f95])).
% 1.73/0.66  fof(f72,plain,(
% 1.73/0.66    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.73/0.66    inference(cnf_transformation,[],[f30])).
% 1.73/0.66  fof(f30,plain,(
% 1.73/0.66    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.73/0.66    inference(flattening,[],[f29])).
% 1.73/0.66  fof(f29,plain,(
% 1.73/0.66    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.73/0.66    inference(ennf_transformation,[],[f6])).
% 1.73/0.66  fof(f6,axiom,(
% 1.73/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.73/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.73/0.66  fof(f204,plain,(
% 1.73/0.66    v2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 1.73/0.66    inference(trivial_inequality_removal,[],[f203])).
% 1.73/0.66  fof(f203,plain,(
% 1.73/0.66    sK0 != sK0 | v2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 1.73/0.66    inference(superposition,[],[f175,f194])).
% 1.73/0.66  fof(f175,plain,(
% 1.73/0.66    ( ! [X0] : (k2_relat_1(X0) != sK0 | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl4_1),
% 1.73/0.66    inference(subsumption_resolution,[],[f174,f155])).
% 1.73/0.66  fof(f174,plain,(
% 1.73/0.66    ( ! [X0] : (k2_relat_1(X0) != sK0 | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 1.73/0.66    inference(subsumption_resolution,[],[f171,f57])).
% 1.73/0.66  fof(f171,plain,(
% 1.73/0.66    ( ! [X0] : (k2_relat_1(X0) != sK0 | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.73/0.66    inference(superposition,[],[f88,f170])).
% 1.73/0.66  fof(f88,plain,(
% 1.73/0.66    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.73/0.66    inference(cnf_transformation,[],[f42])).
% 1.73/0.66  fof(f164,plain,(
% 1.73/0.66    spl4_1),
% 1.73/0.66    inference(avatar_contradiction_clause,[],[f163])).
% 1.73/0.66  fof(f163,plain,(
% 1.73/0.66    $false | spl4_1),
% 1.73/0.66    inference(resolution,[],[f162,f59])).
% 1.73/0.66  fof(f162,plain,(
% 1.73/0.66    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_1),
% 1.73/0.66    inference(resolution,[],[f156,f100])).
% 1.73/0.66  fof(f156,plain,(
% 1.73/0.66    ~v1_relat_1(sK2) | spl4_1),
% 1.73/0.66    inference(avatar_component_clause,[],[f154])).
% 1.73/0.66  fof(f161,plain,(
% 1.73/0.66    ~spl4_1 | spl4_2),
% 1.73/0.66    inference(avatar_split_clause,[],[f126,f158,f154])).
% 1.73/0.66  fof(f126,plain,(
% 1.73/0.66    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.73/0.66    inference(subsumption_resolution,[],[f119,f57])).
% 1.73/0.66  fof(f119,plain,(
% 1.73/0.66    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.73/0.66    inference(resolution,[],[f65,f75])).
% 1.73/0.66  % SZS output end Proof for theBenchmark
% 1.73/0.66  % (10294)------------------------------
% 1.73/0.66  % (10294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.66  % (10296)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.73/0.66  % (10294)Termination reason: Refutation
% 1.73/0.66  
% 1.73/0.66  % (10294)Memory used [KB]: 11129
% 1.73/0.66  % (10294)Time elapsed: 0.217 s
% 1.73/0.66  % (10294)------------------------------
% 1.73/0.66  % (10294)------------------------------
% 1.73/0.67  % (10260)Success in time 0.302 s
%------------------------------------------------------------------------------
