%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:57 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 669 expanded)
%              Number of leaves         :   30 ( 210 expanded)
%              Depth                    :   22
%              Number of atoms          :  519 (4174 expanded)
%              Number of equality atoms :   83 ( 181 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1207,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f962,f975,f1044,f1111,f1149,f1178])).

fof(f1178,plain,
    ( spl4_2
    | ~ spl4_46 ),
    inference(avatar_contradiction_clause,[],[f1177])).

fof(f1177,plain,
    ( $false
    | spl4_2
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f1176,f130])).

fof(f130,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f128,f75])).

fof(f75,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f128,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f74,f59])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f46,f45])).

fof(f45,plain,
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

fof(f46,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f1176,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f1164,f114])).

fof(f114,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1164,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_46 ),
    inference(superposition,[],[f226,f974])).

fof(f974,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f972])).

fof(f972,plain,
    ( spl4_46
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f226,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f101,f176])).

fof(f176,plain,(
    ! [X2] :
      ( v5_relat_1(X2,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f80,f102])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f101,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f1149,plain,(
    spl4_45 ),
    inference(avatar_contradiction_clause,[],[f1148])).

fof(f1148,plain,
    ( $false
    | spl4_45 ),
    inference(subsumption_resolution,[],[f1147,f130])).

fof(f1147,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_45 ),
    inference(subsumption_resolution,[],[f1146,f215])).

fof(f215,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f87,f59])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1146,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | spl4_45 ),
    inference(resolution,[],[f970,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f970,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl4_45 ),
    inference(avatar_component_clause,[],[f968])).

fof(f968,plain,
    ( spl4_45
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f1111,plain,
    ( spl4_1
    | spl4_43
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f1110,f948,f944,f108])).

fof(f108,plain,
    ( spl4_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f944,plain,
    ( spl4_43
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f948,plain,
    ( spl4_44
  <=> v2_funct_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f1110,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2) ),
    inference(global_subsumption,[],[f54,f55,f58,f56,f59,f57,f927])).

fof(f927,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f88,f674])).

fof(f674,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f669,f54])).

fof(f669,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f406,f56])).

fof(f406,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | k1_partfun1(X7,X8,sK1,sK0,X9,sK3) = k5_relat_1(X9,sK3)
      | ~ v1_funct_1(X9) ) ),
    inference(subsumption_resolution,[],[f403,f57])).

fof(f403,plain,(
    ! [X8,X7,X9] :
      ( k1_partfun1(X7,X8,sK1,sK0,X9,sK3) = k5_relat_1(X9,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ v1_funct_1(X9) ) ),
    inference(resolution,[],[f92,f59])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f58,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f55,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f1044,plain,
    ( spl4_1
    | ~ spl4_43 ),
    inference(avatar_contradiction_clause,[],[f1043])).

fof(f1043,plain,
    ( $false
    | spl4_1
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f1022,f117])).

fof(f117,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f97,f95])).

fof(f95,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f63,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f97,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f67,f64])).

fof(f67,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1022,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl4_1
    | ~ spl4_43 ),
    inference(backward_demodulation,[],[f110,f1010])).

fof(f1010,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f1007,f129])).

fof(f129,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f127,f75])).

fof(f127,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f74,f56])).

fof(f1007,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl4_43 ),
    inference(resolution,[],[f987,f488])).

fof(f488,plain,(
    ! [X0] :
      ( ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f485])).

fof(f485,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f484,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f484,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f191,f217])).

fof(f217,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f212,f146])).

fof(f146,plain,(
    ! [X2] :
      ( ~ v4_relat_1(k1_xboole_0,X2)
      | r1_tarski(k1_xboole_0,X2) ) ),
    inference(subsumption_resolution,[],[f144,f116])).

fof(f116,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f98,f95])).

fof(f98,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f66,f64])).

fof(f66,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f144,plain,(
    ! [X2] :
      ( r1_tarski(k1_xboole_0,X2)
      | ~ v4_relat_1(k1_xboole_0,X2)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f77,f120])).

fof(f120,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f100,f95])).

fof(f100,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f68,f64])).

fof(f68,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f212,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f211,f131])).

fof(f131,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f122,f123])).

fof(f123,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f121,f62])).

fof(f62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k2_zfmisc_1(X1,X0) ) ),
    inference(resolution,[],[f76,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f122,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f96,f95])).

fof(f96,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f65,f64])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X1,X0) ) ),
    inference(superposition,[],[f86,f123])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f191,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(extensionality_resolution,[],[f85,f71])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f987,plain,
    ( v4_relat_1(sK2,k1_xboole_0)
    | ~ spl4_43 ),
    inference(backward_demodulation,[],[f209,f946])).

fof(f946,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f944])).

fof(f209,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f86,f56])).

fof(f110,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f975,plain,
    ( ~ spl4_45
    | spl4_46 ),
    inference(avatar_split_clause,[],[f966,f972,f968])).

fof(f966,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),sK0) ),
    inference(forward_demodulation,[],[f965,f99])).

fof(f99,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f69,f64])).

fof(f69,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f965,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f964,f99])).

fof(f964,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f963,f130])).

fof(f963,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f958,f129])).

fof(f958,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f233,f953])).

fof(f953,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f931,f952])).

fof(f952,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f924,f336])).

fof(f336,plain,(
    ! [X0,X1] :
      ( ~ r2_relset_1(X0,X0,X1,k6_partfun1(X0))
      | k6_partfun1(X0) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(resolution,[],[f90,f96])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f924,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f60,f674])).

fof(f60,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f931,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f930,f54])).

fof(f930,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f929,f56])).

fof(f929,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f928,f57])).

fof(f928,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f925,f59])).

fof(f925,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f94,f674])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f233,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(X3)
      | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f73,f85])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f962,plain,(
    spl4_44 ),
    inference(avatar_contradiction_clause,[],[f961])).

fof(f961,plain,
    ( $false
    | spl4_44 ),
    inference(subsumption_resolution,[],[f954,f97])).

fof(f954,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_44 ),
    inference(backward_demodulation,[],[f950,f953])).

fof(f950,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_44 ),
    inference(avatar_component_clause,[],[f948])).

fof(f115,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f61,f112,f108])).

fof(f61,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:09:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.52  % (1903)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (1900)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (1918)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.26/0.54  % (1905)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.54  % (1923)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.26/0.54  % (1914)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.26/0.54  % (1904)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.26/0.54  % (1920)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.26/0.54  % (1921)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.26/0.54  % (1902)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.26/0.55  % (1912)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.26/0.55  % (1906)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.26/0.55  % (1908)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.26/0.55  % (1909)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.26/0.55  % (1907)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.26/0.55  % (1909)Refutation not found, incomplete strategy% (1909)------------------------------
% 1.26/0.55  % (1909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.55  % (1909)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.55  
% 1.26/0.55  % (1909)Memory used [KB]: 10874
% 1.26/0.55  % (1909)Time elapsed: 0.134 s
% 1.26/0.55  % (1909)------------------------------
% 1.26/0.55  % (1909)------------------------------
% 1.26/0.55  % (1913)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.26/0.55  % (1929)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.40/0.56  % (1910)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.40/0.56  % (1925)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.40/0.56  % (1924)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.40/0.56  % (1919)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.40/0.56  % (1928)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.40/0.56  % (1911)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.40/0.56  % (1916)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.40/0.56  % (1927)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.40/0.56  % (1915)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.40/0.57  % (1901)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.40/0.57  % (1915)Refutation not found, incomplete strategy% (1915)------------------------------
% 1.40/0.57  % (1915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (1915)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (1915)Memory used [KB]: 10746
% 1.40/0.57  % (1915)Time elapsed: 0.156 s
% 1.40/0.57  % (1915)------------------------------
% 1.40/0.57  % (1915)------------------------------
% 1.40/0.57  % (1930)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.40/0.57  % (1917)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.40/0.57  % (1898)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.40/0.58  % (1929)Refutation not found, incomplete strategy% (1929)------------------------------
% 1.40/0.58  % (1929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.58  % (1929)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.58  
% 1.40/0.58  % (1929)Memory used [KB]: 10874
% 1.40/0.58  % (1929)Time elapsed: 0.166 s
% 1.40/0.58  % (1929)------------------------------
% 1.40/0.58  % (1929)------------------------------
% 1.40/0.60  % (1905)Refutation found. Thanks to Tanya!
% 1.40/0.60  % SZS status Theorem for theBenchmark
% 1.40/0.60  % SZS output start Proof for theBenchmark
% 1.40/0.60  fof(f1207,plain,(
% 1.40/0.60    $false),
% 1.40/0.60    inference(avatar_sat_refutation,[],[f115,f962,f975,f1044,f1111,f1149,f1178])).
% 1.40/0.60  fof(f1178,plain,(
% 1.40/0.60    spl4_2 | ~spl4_46),
% 1.40/0.60    inference(avatar_contradiction_clause,[],[f1177])).
% 1.40/0.60  fof(f1177,plain,(
% 1.40/0.60    $false | (spl4_2 | ~spl4_46)),
% 1.40/0.60    inference(subsumption_resolution,[],[f1176,f130])).
% 1.40/0.60  fof(f130,plain,(
% 1.40/0.60    v1_relat_1(sK3)),
% 1.40/0.60    inference(subsumption_resolution,[],[f128,f75])).
% 1.40/0.60  fof(f75,plain,(
% 1.40/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.40/0.60    inference(cnf_transformation,[],[f8])).
% 1.40/0.60  fof(f8,axiom,(
% 1.40/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.40/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.40/0.60  fof(f128,plain,(
% 1.40/0.60    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.40/0.60    inference(resolution,[],[f74,f59])).
% 1.40/0.60  fof(f59,plain,(
% 1.40/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.40/0.60    inference(cnf_transformation,[],[f47])).
% 1.40/0.60  fof(f47,plain,(
% 1.40/0.60    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.40/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f46,f45])).
% 1.40/0.60  fof(f45,plain,(
% 1.40/0.60    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.40/0.60    introduced(choice_axiom,[])).
% 1.40/0.60  fof(f46,plain,(
% 1.40/0.60    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.40/0.60    introduced(choice_axiom,[])).
% 1.40/0.60  fof(f25,plain,(
% 1.40/0.60    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.40/0.60    inference(flattening,[],[f24])).
% 1.40/0.60  fof(f24,plain,(
% 1.40/0.60    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.40/0.60    inference(ennf_transformation,[],[f23])).
% 1.40/0.60  fof(f23,negated_conjecture,(
% 1.40/0.60    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.40/0.60    inference(negated_conjecture,[],[f22])).
% 1.40/0.60  fof(f22,conjecture,(
% 1.40/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.40/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 1.40/0.60  fof(f74,plain,(
% 1.40/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.40/0.60    inference(cnf_transformation,[],[f30])).
% 1.40/0.60  fof(f30,plain,(
% 1.40/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.40/0.60    inference(ennf_transformation,[],[f5])).
% 1.40/0.60  fof(f5,axiom,(
% 1.40/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.40/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.40/0.60  fof(f1176,plain,(
% 1.40/0.60    ~v1_relat_1(sK3) | (spl4_2 | ~spl4_46)),
% 1.40/0.60    inference(subsumption_resolution,[],[f1164,f114])).
% 1.40/0.60  fof(f114,plain,(
% 1.40/0.60    ~v2_funct_2(sK3,sK0) | spl4_2),
% 1.40/0.60    inference(avatar_component_clause,[],[f112])).
% 1.40/0.60  fof(f112,plain,(
% 1.40/0.60    spl4_2 <=> v2_funct_2(sK3,sK0)),
% 1.40/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.40/0.61  fof(f1164,plain,(
% 1.40/0.61    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_46),
% 1.40/0.61    inference(superposition,[],[f226,f974])).
% 1.40/0.61  fof(f974,plain,(
% 1.40/0.61    sK0 = k2_relat_1(sK3) | ~spl4_46),
% 1.40/0.61    inference(avatar_component_clause,[],[f972])).
% 1.40/0.61  fof(f972,plain,(
% 1.40/0.61    spl4_46 <=> sK0 = k2_relat_1(sK3)),
% 1.40/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.40/0.61  fof(f226,plain,(
% 1.40/0.61    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.40/0.61    inference(subsumption_resolution,[],[f101,f176])).
% 1.40/0.61  fof(f176,plain,(
% 1.40/0.61    ( ! [X2] : (v5_relat_1(X2,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.40/0.61    inference(resolution,[],[f80,f102])).
% 1.40/0.61  fof(f102,plain,(
% 1.40/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.40/0.61    inference(equality_resolution,[],[f84])).
% 1.40/0.61  fof(f84,plain,(
% 1.40/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.40/0.61    inference(cnf_transformation,[],[f52])).
% 1.40/0.61  fof(f52,plain,(
% 1.40/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.61    inference(flattening,[],[f51])).
% 1.40/0.61  fof(f51,plain,(
% 1.40/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.61    inference(nnf_transformation,[],[f3])).
% 1.40/0.61  fof(f3,axiom,(
% 1.40/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.40/0.61  fof(f80,plain,(
% 1.40/0.61    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.40/0.61    inference(cnf_transformation,[],[f49])).
% 1.40/0.61  fof(f49,plain,(
% 1.40/0.61    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.40/0.61    inference(nnf_transformation,[],[f33])).
% 1.40/0.61  fof(f33,plain,(
% 1.40/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.40/0.61    inference(ennf_transformation,[],[f7])).
% 1.40/0.61  fof(f7,axiom,(
% 1.40/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.40/0.61  fof(f101,plain,(
% 1.40/0.61    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.40/0.61    inference(equality_resolution,[],[f82])).
% 1.40/0.61  fof(f82,plain,(
% 1.40/0.61    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.40/0.61    inference(cnf_transformation,[],[f50])).
% 1.40/0.61  fof(f50,plain,(
% 1.40/0.61    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.40/0.61    inference(nnf_transformation,[],[f35])).
% 1.40/0.61  fof(f35,plain,(
% 1.40/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.40/0.61    inference(flattening,[],[f34])).
% 1.40/0.61  fof(f34,plain,(
% 1.40/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.40/0.61    inference(ennf_transformation,[],[f17])).
% 1.40/0.61  fof(f17,axiom,(
% 1.40/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.40/0.61  fof(f1149,plain,(
% 1.40/0.61    spl4_45),
% 1.40/0.61    inference(avatar_contradiction_clause,[],[f1148])).
% 1.40/0.61  fof(f1148,plain,(
% 1.40/0.61    $false | spl4_45),
% 1.40/0.61    inference(subsumption_resolution,[],[f1147,f130])).
% 1.40/0.61  fof(f1147,plain,(
% 1.40/0.61    ~v1_relat_1(sK3) | spl4_45),
% 1.40/0.61    inference(subsumption_resolution,[],[f1146,f215])).
% 1.40/0.61  fof(f215,plain,(
% 1.40/0.61    v5_relat_1(sK3,sK0)),
% 1.40/0.61    inference(resolution,[],[f87,f59])).
% 1.40/0.61  fof(f87,plain,(
% 1.40/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.40/0.61    inference(cnf_transformation,[],[f36])).
% 1.40/0.61  fof(f36,plain,(
% 1.40/0.61    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.61    inference(ennf_transformation,[],[f14])).
% 1.40/0.61  fof(f14,axiom,(
% 1.40/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.40/0.61  fof(f1146,plain,(
% 1.40/0.61    ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | spl4_45),
% 1.40/0.61    inference(resolution,[],[f970,f79])).
% 1.40/0.61  fof(f79,plain,(
% 1.40/0.61    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.40/0.61    inference(cnf_transformation,[],[f49])).
% 1.40/0.61  fof(f970,plain,(
% 1.40/0.61    ~r1_tarski(k2_relat_1(sK3),sK0) | spl4_45),
% 1.40/0.61    inference(avatar_component_clause,[],[f968])).
% 1.40/0.61  fof(f968,plain,(
% 1.40/0.61    spl4_45 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 1.40/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 1.40/0.61  fof(f1111,plain,(
% 1.40/0.61    spl4_1 | spl4_43 | ~spl4_44),
% 1.40/0.61    inference(avatar_split_clause,[],[f1110,f948,f944,f108])).
% 1.40/0.61  fof(f108,plain,(
% 1.40/0.61    spl4_1 <=> v2_funct_1(sK2)),
% 1.40/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.40/0.61  fof(f944,plain,(
% 1.40/0.61    spl4_43 <=> k1_xboole_0 = sK0),
% 1.40/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.40/0.61  fof(f948,plain,(
% 1.40/0.61    spl4_44 <=> v2_funct_1(k5_relat_1(sK2,sK3))),
% 1.40/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.40/0.61  fof(f1110,plain,(
% 1.40/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK2)),
% 1.40/0.61    inference(global_subsumption,[],[f54,f55,f58,f56,f59,f57,f927])).
% 1.40/0.61  fof(f927,plain,(
% 1.40/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.40/0.61    inference(superposition,[],[f88,f674])).
% 1.40/0.61  fof(f674,plain,(
% 1.40/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.40/0.61    inference(subsumption_resolution,[],[f669,f54])).
% 1.40/0.61  fof(f669,plain,(
% 1.40/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 1.40/0.61    inference(resolution,[],[f406,f56])).
% 1.40/0.61  fof(f406,plain,(
% 1.40/0.61    ( ! [X8,X7,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | k1_partfun1(X7,X8,sK1,sK0,X9,sK3) = k5_relat_1(X9,sK3) | ~v1_funct_1(X9)) )),
% 1.40/0.61    inference(subsumption_resolution,[],[f403,f57])).
% 1.40/0.61  fof(f403,plain,(
% 1.40/0.61    ( ! [X8,X7,X9] : (k1_partfun1(X7,X8,sK1,sK0,X9,sK3) = k5_relat_1(X9,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~v1_funct_1(X9)) )),
% 1.40/0.61    inference(resolution,[],[f92,f59])).
% 1.40/0.61  fof(f92,plain,(
% 1.40/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.40/0.61    inference(cnf_transformation,[],[f42])).
% 1.40/0.61  fof(f42,plain,(
% 1.40/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.40/0.61    inference(flattening,[],[f41])).
% 1.40/0.61  fof(f41,plain,(
% 1.40/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.40/0.61    inference(ennf_transformation,[],[f19])).
% 1.40/0.61  fof(f19,axiom,(
% 1.40/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.40/0.61  fof(f88,plain,(
% 1.40/0.61    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.40/0.61    inference(cnf_transformation,[],[f38])).
% 1.40/0.61  fof(f38,plain,(
% 1.40/0.61    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.40/0.61    inference(flattening,[],[f37])).
% 1.40/0.61  fof(f37,plain,(
% 1.40/0.61    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.40/0.61    inference(ennf_transformation,[],[f21])).
% 1.40/0.61  fof(f21,axiom,(
% 1.40/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 1.40/0.61  fof(f57,plain,(
% 1.40/0.61    v1_funct_1(sK3)),
% 1.40/0.61    inference(cnf_transformation,[],[f47])).
% 1.40/0.61  fof(f56,plain,(
% 1.40/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.40/0.61    inference(cnf_transformation,[],[f47])).
% 1.40/0.61  fof(f58,plain,(
% 1.40/0.61    v1_funct_2(sK3,sK1,sK0)),
% 1.40/0.61    inference(cnf_transformation,[],[f47])).
% 1.40/0.61  fof(f55,plain,(
% 1.40/0.61    v1_funct_2(sK2,sK0,sK1)),
% 1.40/0.61    inference(cnf_transformation,[],[f47])).
% 1.40/0.61  fof(f54,plain,(
% 1.40/0.61    v1_funct_1(sK2)),
% 1.40/0.61    inference(cnf_transformation,[],[f47])).
% 1.40/0.61  fof(f1044,plain,(
% 1.40/0.61    spl4_1 | ~spl4_43),
% 1.40/0.61    inference(avatar_contradiction_clause,[],[f1043])).
% 1.40/0.61  fof(f1043,plain,(
% 1.40/0.61    $false | (spl4_1 | ~spl4_43)),
% 1.40/0.61    inference(subsumption_resolution,[],[f1022,f117])).
% 1.40/0.61  fof(f117,plain,(
% 1.40/0.61    v2_funct_1(k1_xboole_0)),
% 1.40/0.61    inference(superposition,[],[f97,f95])).
% 1.40/0.61  fof(f95,plain,(
% 1.40/0.61    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.40/0.61    inference(definition_unfolding,[],[f63,f64])).
% 1.40/0.61  fof(f64,plain,(
% 1.40/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.40/0.61    inference(cnf_transformation,[],[f20])).
% 1.40/0.61  fof(f20,axiom,(
% 1.40/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.40/0.61  fof(f63,plain,(
% 1.40/0.61    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.40/0.61    inference(cnf_transformation,[],[f12])).
% 1.40/0.61  fof(f12,axiom,(
% 1.40/0.61    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 1.40/0.61  fof(f97,plain,(
% 1.40/0.61    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.40/0.61    inference(definition_unfolding,[],[f67,f64])).
% 1.40/0.61  fof(f67,plain,(
% 1.40/0.61    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.40/0.61    inference(cnf_transformation,[],[f13])).
% 1.40/0.61  fof(f13,axiom,(
% 1.40/0.61    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.40/0.61  fof(f1022,plain,(
% 1.40/0.61    ~v2_funct_1(k1_xboole_0) | (spl4_1 | ~spl4_43)),
% 1.40/0.61    inference(backward_demodulation,[],[f110,f1010])).
% 1.40/0.61  fof(f1010,plain,(
% 1.40/0.61    k1_xboole_0 = sK2 | ~spl4_43),
% 1.40/0.61    inference(subsumption_resolution,[],[f1007,f129])).
% 1.40/0.61  fof(f129,plain,(
% 1.40/0.61    v1_relat_1(sK2)),
% 1.40/0.61    inference(subsumption_resolution,[],[f127,f75])).
% 1.40/0.61  fof(f127,plain,(
% 1.40/0.61    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.40/0.61    inference(resolution,[],[f74,f56])).
% 1.40/0.61  fof(f1007,plain,(
% 1.40/0.61    ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl4_43),
% 1.40/0.61    inference(resolution,[],[f987,f488])).
% 1.40/0.61  fof(f488,plain,(
% 1.40/0.61    ( ! [X0] : (~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.40/0.61    inference(duplicate_literal_removal,[],[f485])).
% 1.40/0.61  fof(f485,plain,(
% 1.40/0.61    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_relat_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.40/0.61    inference(resolution,[],[f484,f77])).
% 1.40/0.61  fof(f77,plain,(
% 1.40/0.61    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.40/0.61    inference(cnf_transformation,[],[f48])).
% 1.40/0.61  fof(f48,plain,(
% 1.40/0.61    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.40/0.61    inference(nnf_transformation,[],[f32])).
% 1.40/0.61  fof(f32,plain,(
% 1.40/0.61    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.40/0.61    inference(ennf_transformation,[],[f6])).
% 1.40/0.61  fof(f6,axiom,(
% 1.40/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.40/0.61  fof(f484,plain,(
% 1.40/0.61    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_xboole_0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.40/0.61    inference(subsumption_resolution,[],[f191,f217])).
% 1.40/0.61  fof(f217,plain,(
% 1.40/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.40/0.61    inference(resolution,[],[f212,f146])).
% 1.40/0.61  fof(f146,plain,(
% 1.40/0.61    ( ! [X2] : (~v4_relat_1(k1_xboole_0,X2) | r1_tarski(k1_xboole_0,X2)) )),
% 1.40/0.61    inference(subsumption_resolution,[],[f144,f116])).
% 1.40/0.61  fof(f116,plain,(
% 1.40/0.61    v1_relat_1(k1_xboole_0)),
% 1.40/0.61    inference(superposition,[],[f98,f95])).
% 1.40/0.61  fof(f98,plain,(
% 1.40/0.61    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 1.40/0.61    inference(definition_unfolding,[],[f66,f64])).
% 1.40/0.61  fof(f66,plain,(
% 1.40/0.61    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.40/0.61    inference(cnf_transformation,[],[f13])).
% 1.40/0.61  fof(f144,plain,(
% 1.40/0.61    ( ! [X2] : (r1_tarski(k1_xboole_0,X2) | ~v4_relat_1(k1_xboole_0,X2) | ~v1_relat_1(k1_xboole_0)) )),
% 1.40/0.61    inference(superposition,[],[f77,f120])).
% 1.40/0.61  fof(f120,plain,(
% 1.40/0.61    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.40/0.61    inference(superposition,[],[f100,f95])).
% 1.40/0.61  fof(f100,plain,(
% 1.40/0.61    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.40/0.61    inference(definition_unfolding,[],[f68,f64])).
% 1.40/0.61  fof(f68,plain,(
% 1.40/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.40/0.61    inference(cnf_transformation,[],[f11])).
% 1.40/0.61  fof(f11,axiom,(
% 1.40/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.40/0.61  fof(f212,plain,(
% 1.40/0.61    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 1.40/0.61    inference(resolution,[],[f211,f131])).
% 1.40/0.61  fof(f131,plain,(
% 1.40/0.61    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.40/0.61    inference(backward_demodulation,[],[f122,f123])).
% 1.40/0.61  fof(f123,plain,(
% 1.40/0.61    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.40/0.61    inference(resolution,[],[f121,f62])).
% 1.40/0.61  fof(f62,plain,(
% 1.40/0.61    v1_xboole_0(k1_xboole_0)),
% 1.40/0.61    inference(cnf_transformation,[],[f1])).
% 1.40/0.61  fof(f1,axiom,(
% 1.40/0.61    v1_xboole_0(k1_xboole_0)),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.40/0.61  fof(f121,plain,(
% 1.40/0.61    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X1,X0)) )),
% 1.40/0.61    inference(resolution,[],[f76,f70])).
% 1.40/0.61  fof(f70,plain,(
% 1.40/0.61    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.40/0.61    inference(cnf_transformation,[],[f26])).
% 1.40/0.62  fof(f26,plain,(
% 1.40/0.62    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.40/0.62    inference(ennf_transformation,[],[f2])).
% 1.40/0.62  fof(f2,axiom,(
% 1.40/0.62    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.40/0.62  fof(f76,plain,(
% 1.40/0.62    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f31])).
% 1.40/0.62  fof(f31,plain,(
% 1.40/0.62    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 1.40/0.62    inference(ennf_transformation,[],[f4])).
% 1.40/0.62  fof(f4,axiom,(
% 1.40/0.62    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 1.40/0.62  fof(f122,plain,(
% 1.40/0.62    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.40/0.62    inference(superposition,[],[f96,f95])).
% 1.40/0.62  fof(f96,plain,(
% 1.40/0.62    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.40/0.62    inference(definition_unfolding,[],[f65,f64])).
% 1.40/0.62  fof(f65,plain,(
% 1.40/0.62    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.40/0.62    inference(cnf_transformation,[],[f16])).
% 1.40/0.62  fof(f16,axiom,(
% 1.40/0.62    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.40/0.62  fof(f211,plain,(
% 1.40/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)) )),
% 1.40/0.62    inference(superposition,[],[f86,f123])).
% 1.40/0.62  fof(f86,plain,(
% 1.40/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f36])).
% 1.40/0.62  fof(f191,plain,(
% 1.40/0.62    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.40/0.62    inference(extensionality_resolution,[],[f85,f71])).
% 1.40/0.62  fof(f71,plain,(
% 1.40/0.62    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f28])).
% 1.40/0.62  fof(f28,plain,(
% 1.40/0.62    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.40/0.62    inference(flattening,[],[f27])).
% 1.40/0.62  fof(f27,plain,(
% 1.40/0.62    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.40/0.62    inference(ennf_transformation,[],[f10])).
% 1.40/0.62  fof(f10,axiom,(
% 1.40/0.62    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.40/0.62  fof(f85,plain,(
% 1.40/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f52])).
% 1.40/0.62  fof(f987,plain,(
% 1.40/0.62    v4_relat_1(sK2,k1_xboole_0) | ~spl4_43),
% 1.40/0.62    inference(backward_demodulation,[],[f209,f946])).
% 1.40/0.62  fof(f946,plain,(
% 1.40/0.62    k1_xboole_0 = sK0 | ~spl4_43),
% 1.40/0.62    inference(avatar_component_clause,[],[f944])).
% 1.40/0.62  fof(f209,plain,(
% 1.40/0.62    v4_relat_1(sK2,sK0)),
% 1.40/0.62    inference(resolution,[],[f86,f56])).
% 1.40/0.62  fof(f110,plain,(
% 1.40/0.62    ~v2_funct_1(sK2) | spl4_1),
% 1.40/0.62    inference(avatar_component_clause,[],[f108])).
% 1.40/0.62  fof(f975,plain,(
% 1.40/0.62    ~spl4_45 | spl4_46),
% 1.40/0.62    inference(avatar_split_clause,[],[f966,f972,f968])).
% 1.40/0.62  fof(f966,plain,(
% 1.40/0.62    sK0 = k2_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),sK0)),
% 1.40/0.62    inference(forward_demodulation,[],[f965,f99])).
% 1.40/0.62  fof(f99,plain,(
% 1.40/0.62    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.40/0.62    inference(definition_unfolding,[],[f69,f64])).
% 1.40/0.62  fof(f69,plain,(
% 1.40/0.62    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.40/0.62    inference(cnf_transformation,[],[f11])).
% 1.40/0.62  fof(f965,plain,(
% 1.40/0.62    ~r1_tarski(k2_relat_1(sK3),sK0) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))),
% 1.40/0.62    inference(forward_demodulation,[],[f964,f99])).
% 1.40/0.62  fof(f964,plain,(
% 1.40/0.62    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))),
% 1.40/0.62    inference(subsumption_resolution,[],[f963,f130])).
% 1.40/0.62  fof(f963,plain,(
% 1.40/0.62    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.40/0.62    inference(subsumption_resolution,[],[f958,f129])).
% 1.40/0.62  fof(f958,plain,(
% 1.40/0.62    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | ~v1_relat_1(sK2) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.40/0.62    inference(superposition,[],[f233,f953])).
% 1.40/0.62  fof(f953,plain,(
% 1.40/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.40/0.62    inference(global_subsumption,[],[f931,f952])).
% 1.40/0.62  fof(f952,plain,(
% 1.40/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.40/0.62    inference(resolution,[],[f924,f336])).
% 1.40/0.62  fof(f336,plain,(
% 1.40/0.62    ( ! [X0,X1] : (~r2_relset_1(X0,X0,X1,k6_partfun1(X0)) | k6_partfun1(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.40/0.62    inference(resolution,[],[f90,f96])).
% 1.40/0.62  fof(f90,plain,(
% 1.40/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.62    inference(cnf_transformation,[],[f53])).
% 1.40/0.62  fof(f53,plain,(
% 1.40/0.62    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.62    inference(nnf_transformation,[],[f40])).
% 1.40/0.62  fof(f40,plain,(
% 1.40/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.62    inference(flattening,[],[f39])).
% 1.40/0.62  fof(f39,plain,(
% 1.40/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.40/0.62    inference(ennf_transformation,[],[f15])).
% 1.40/0.62  fof(f15,axiom,(
% 1.40/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.40/0.62  fof(f924,plain,(
% 1.40/0.62    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.40/0.62    inference(backward_demodulation,[],[f60,f674])).
% 1.40/0.62  fof(f60,plain,(
% 1.40/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.40/0.62    inference(cnf_transformation,[],[f47])).
% 1.40/0.62  fof(f931,plain,(
% 1.40/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.40/0.62    inference(subsumption_resolution,[],[f930,f54])).
% 1.40/0.62  fof(f930,plain,(
% 1.40/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.40/0.62    inference(subsumption_resolution,[],[f929,f56])).
% 1.40/0.62  fof(f929,plain,(
% 1.40/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.40/0.62    inference(subsumption_resolution,[],[f928,f57])).
% 1.40/0.62  fof(f928,plain,(
% 1.40/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.40/0.62    inference(subsumption_resolution,[],[f925,f59])).
% 1.40/0.62  fof(f925,plain,(
% 1.40/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.40/0.62    inference(superposition,[],[f94,f674])).
% 1.40/0.62  fof(f94,plain,(
% 1.40/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f44])).
% 1.40/0.62  fof(f44,plain,(
% 1.40/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.40/0.62    inference(flattening,[],[f43])).
% 1.40/0.62  fof(f43,plain,(
% 1.40/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.40/0.62    inference(ennf_transformation,[],[f18])).
% 1.40/0.62  fof(f18,axiom,(
% 1.40/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.40/0.62  fof(f233,plain,(
% 1.40/0.62    ( ! [X2,X3] : (~r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(X3) | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2)) | ~v1_relat_1(X2)) )),
% 1.40/0.62    inference(resolution,[],[f73,f85])).
% 1.40/0.62  fof(f73,plain,(
% 1.40/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f29])).
% 1.40/0.62  fof(f29,plain,(
% 1.40/0.62    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.40/0.62    inference(ennf_transformation,[],[f9])).
% 1.40/0.62  fof(f9,axiom,(
% 1.40/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.40/0.62  fof(f962,plain,(
% 1.40/0.62    spl4_44),
% 1.40/0.62    inference(avatar_contradiction_clause,[],[f961])).
% 1.40/0.62  fof(f961,plain,(
% 1.40/0.62    $false | spl4_44),
% 1.40/0.62    inference(subsumption_resolution,[],[f954,f97])).
% 1.40/0.62  fof(f954,plain,(
% 1.40/0.62    ~v2_funct_1(k6_partfun1(sK0)) | spl4_44),
% 1.40/0.62    inference(backward_demodulation,[],[f950,f953])).
% 1.40/0.62  fof(f950,plain,(
% 1.40/0.62    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_44),
% 1.40/0.62    inference(avatar_component_clause,[],[f948])).
% 1.40/0.62  fof(f115,plain,(
% 1.40/0.62    ~spl4_1 | ~spl4_2),
% 1.40/0.62    inference(avatar_split_clause,[],[f61,f112,f108])).
% 1.40/0.62  fof(f61,plain,(
% 1.40/0.62    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.40/0.62    inference(cnf_transformation,[],[f47])).
% 1.40/0.62  % SZS output end Proof for theBenchmark
% 1.40/0.62  % (1905)------------------------------
% 1.40/0.62  % (1905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.62  % (1905)Termination reason: Refutation
% 1.40/0.62  
% 1.40/0.62  % (1905)Memory used [KB]: 11513
% 1.40/0.62  % (1905)Time elapsed: 0.193 s
% 1.40/0.62  % (1905)------------------------------
% 1.40/0.62  % (1905)------------------------------
% 1.40/0.62  % (1894)Success in time 0.254 s
%------------------------------------------------------------------------------
