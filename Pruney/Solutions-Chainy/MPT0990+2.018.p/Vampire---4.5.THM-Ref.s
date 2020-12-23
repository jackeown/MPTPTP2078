%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:31 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 444 expanded)
%              Number of leaves         :   23 ( 134 expanded)
%              Depth                    :   23
%              Number of atoms          :  449 (3678 expanded)
%              Number of equality atoms :  123 (1232 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1687,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f173,f1686])).

fof(f1686,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f1685])).

fof(f1685,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f1684,f65])).

fof(f65,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f50,f49])).

fof(f49,plain,
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

fof(f50,plain,
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f1684,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f1683,f490])).

fof(f490,plain,(
    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(subsumption_resolution,[],[f486,f110])).

fof(f110,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f86,f59])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f486,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(resolution,[],[f196,f120])).

fof(f120,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f88,f59])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k6_partfun1(X0),X1) = X1 ) ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f104,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f83,f66])).

fof(f66,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f1683,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f1682,f506])).

fof(f506,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_1 ),
    inference(resolution,[],[f493,f185])).

fof(f185,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_relat_1(sK2),X2)
        | k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X2)) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f183,f151])).

fof(f151,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl4_1
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f183,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(sK2),X2)
      | k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X2))
      | ~ v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(superposition,[],[f103,f178])).

fof(f178,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f177,f109])).

fof(f109,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f86,f56])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f177,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f175,f54])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f175,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f78,f62])).

fof(f62,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f82,f66])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f493,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(superposition,[],[f108,f491])).

fof(f491,plain,(
    k1_relat_1(sK2) = k10_relat_1(k6_partfun1(sK0),k1_relat_1(sK2)) ),
    inference(superposition,[],[f208,f489])).

fof(f489,plain,(
    sK2 = k5_relat_1(k6_partfun1(sK0),sK2) ),
    inference(subsumption_resolution,[],[f485,f109])).

fof(f485,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k5_relat_1(k6_partfun1(sK0),sK2) ),
    inference(resolution,[],[f196,f119])).

fof(f119,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f88,f56])).

fof(f208,plain,(
    ! [X1] : k1_relat_1(k5_relat_1(k6_partfun1(X1),sK2)) = k10_relat_1(k6_partfun1(X1),k1_relat_1(sK2)) ),
    inference(resolution,[],[f202,f97])).

fof(f97,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f68,f66])).

fof(f68,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f202,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | k1_relat_1(k5_relat_1(X5,sK2)) = k10_relat_1(X5,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f73,f109])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f108,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_partfun1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f107,f97])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_partfun1(X0),X1),X0)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f81,f99])).

fof(f99,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f70,f66])).

fof(f70,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f1682,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f1677,f267])).

fof(f267,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(forward_demodulation,[],[f266,f244])).

fof(f244,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f241,f60])).

fof(f60,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f241,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f87,f56])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f266,plain,(
    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f265,f109])).

fof(f265,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f263,f54])).

fof(f263,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f101,f62])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f80,f66])).

fof(f80,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
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
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f1677,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3)
    | ~ spl4_1 ),
    inference(resolution,[],[f1291,f151])).

fof(f1291,plain,(
    ! [X16] :
      ( ~ v1_relat_1(X16)
      | k5_relat_1(k5_relat_1(X16,sK2),sK3) = k5_relat_1(X16,k6_partfun1(sK0)) ) ),
    inference(forward_demodulation,[],[f1289,f853])).

fof(f853,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f843,f852])).

fof(f852,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f830,f294])).

fof(f294,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f90,f95])).

fof(f95,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f67,f66])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f830,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f61,f706])).

fof(f706,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f702,f54])).

fof(f702,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f335,f56])).

fof(f335,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f332,f57])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f332,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f92,f59])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f61,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f843,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f842,f54])).

fof(f842,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f841,f56])).

fof(f841,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f840,f57])).

fof(f840,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f832,f59])).

fof(f832,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f94,f706])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1289,plain,(
    ! [X16] :
      ( k5_relat_1(k5_relat_1(X16,sK2),sK3) = k5_relat_1(X16,k5_relat_1(sK2,sK3))
      | ~ v1_relat_1(X16) ) ),
    inference(resolution,[],[f284,f109])).

fof(f284,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | k5_relat_1(k5_relat_1(X10,X11),sK3) = k5_relat_1(X10,k5_relat_1(X11,sK3))
      | ~ v1_relat_1(X10) ) ),
    inference(resolution,[],[f74,f110])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f173,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f171,f109])).

fof(f171,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f170,f54])).

fof(f170,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(resolution,[],[f152,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f152,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:43:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (1211662336)
% 0.14/0.37  ipcrm: permission denied for id (1215496194)
% 0.14/0.37  ipcrm: permission denied for id (1217658883)
% 0.14/0.37  ipcrm: permission denied for id (1215561732)
% 0.14/0.37  ipcrm: permission denied for id (1217691653)
% 0.14/0.37  ipcrm: permission denied for id (1217724422)
% 0.14/0.38  ipcrm: permission denied for id (1211858952)
% 0.14/0.38  ipcrm: permission denied for id (1217822730)
% 0.14/0.38  ipcrm: permission denied for id (1211957259)
% 0.14/0.38  ipcrm: permission denied for id (1211990028)
% 0.14/0.38  ipcrm: permission denied for id (1212055567)
% 0.14/0.39  ipcrm: permission denied for id (1212088336)
% 0.14/0.39  ipcrm: permission denied for id (1212121105)
% 0.14/0.39  ipcrm: permission denied for id (1215823890)
% 0.21/0.39  ipcrm: permission denied for id (1212186643)
% 0.21/0.39  ipcrm: permission denied for id (1212219412)
% 0.21/0.39  ipcrm: permission denied for id (1215856661)
% 0.21/0.39  ipcrm: permission denied for id (1215889430)
% 0.21/0.39  ipcrm: permission denied for id (1212317719)
% 0.21/0.40  ipcrm: permission denied for id (1215954968)
% 0.21/0.40  ipcrm: permission denied for id (1212383257)
% 0.21/0.40  ipcrm: permission denied for id (1212416026)
% 0.21/0.40  ipcrm: permission denied for id (1212514331)
% 0.21/0.40  ipcrm: permission denied for id (1212481564)
% 0.21/0.40  ipcrm: permission denied for id (1212547101)
% 0.21/0.40  ipcrm: permission denied for id (1215987742)
% 0.21/0.40  ipcrm: permission denied for id (1216020511)
% 0.21/0.40  ipcrm: permission denied for id (1217921056)
% 0.21/0.41  ipcrm: permission denied for id (1212678177)
% 0.21/0.41  ipcrm: permission denied for id (1216086050)
% 0.21/0.41  ipcrm: permission denied for id (1217953827)
% 0.21/0.41  ipcrm: permission denied for id (1216151588)
% 0.21/0.41  ipcrm: permission denied for id (1216184357)
% 0.21/0.41  ipcrm: permission denied for id (1212809254)
% 0.21/0.41  ipcrm: permission denied for id (1217986599)
% 0.21/0.41  ipcrm: permission denied for id (1218019368)
% 0.21/0.42  ipcrm: permission denied for id (1216282665)
% 0.21/0.42  ipcrm: permission denied for id (1218084907)
% 0.21/0.42  ipcrm: permission denied for id (1212973101)
% 0.21/0.42  ipcrm: permission denied for id (1216413742)
% 0.21/0.42  ipcrm: permission denied for id (1213038639)
% 0.21/0.42  ipcrm: permission denied for id (1213071408)
% 0.21/0.43  ipcrm: permission denied for id (1213104177)
% 0.21/0.43  ipcrm: permission denied for id (1213136946)
% 0.21/0.43  ipcrm: permission denied for id (1213169715)
% 0.21/0.43  ipcrm: permission denied for id (1218150452)
% 0.21/0.43  ipcrm: permission denied for id (1216479285)
% 0.21/0.43  ipcrm: permission denied for id (1213268022)
% 0.21/0.43  ipcrm: permission denied for id (1213300791)
% 0.21/0.44  ipcrm: permission denied for id (1213333561)
% 0.21/0.44  ipcrm: permission denied for id (1213366330)
% 0.21/0.44  ipcrm: permission denied for id (1218215995)
% 0.21/0.44  ipcrm: permission denied for id (1213431868)
% 0.21/0.44  ipcrm: permission denied for id (1216577597)
% 0.21/0.44  ipcrm: permission denied for id (1216610366)
% 0.21/0.44  ipcrm: permission denied for id (1213530175)
% 0.21/0.44  ipcrm: permission denied for id (1216643136)
% 0.21/0.45  ipcrm: permission denied for id (1213595713)
% 0.21/0.45  ipcrm: permission denied for id (1218248770)
% 0.21/0.45  ipcrm: permission denied for id (1213661251)
% 0.21/0.45  ipcrm: permission denied for id (1213694020)
% 0.21/0.45  ipcrm: permission denied for id (1216708677)
% 0.21/0.45  ipcrm: permission denied for id (1216741446)
% 0.21/0.46  ipcrm: permission denied for id (1213792327)
% 0.21/0.46  ipcrm: permission denied for id (1213825096)
% 0.21/0.46  ipcrm: permission denied for id (1213857865)
% 0.21/0.46  ipcrm: permission denied for id (1216774218)
% 0.21/0.46  ipcrm: permission denied for id (1216806987)
% 0.21/0.46  ipcrm: permission denied for id (1213956172)
% 0.21/0.46  ipcrm: permission denied for id (1213988941)
% 0.21/0.47  ipcrm: permission denied for id (1214021710)
% 0.21/0.47  ipcrm: permission denied for id (1214054479)
% 0.21/0.47  ipcrm: permission denied for id (1218281552)
% 0.21/0.47  ipcrm: permission denied for id (1218314321)
% 0.21/0.47  ipcrm: permission denied for id (1218347090)
% 0.21/0.47  ipcrm: permission denied for id (1214087251)
% 0.21/0.48  ipcrm: permission denied for id (1214120020)
% 0.21/0.48  ipcrm: permission denied for id (1218379861)
% 0.21/0.48  ipcrm: permission denied for id (1214152790)
% 0.21/0.48  ipcrm: permission denied for id (1214185560)
% 0.21/0.48  ipcrm: permission denied for id (1217003609)
% 0.21/0.48  ipcrm: permission denied for id (1214218330)
% 0.21/0.49  ipcrm: permission denied for id (1214251099)
% 0.21/0.49  ipcrm: permission denied for id (1214283868)
% 0.21/0.49  ipcrm: permission denied for id (1218445405)
% 0.21/0.49  ipcrm: permission denied for id (1218543710)
% 0.21/0.49  ipcrm: permission denied for id (1214382175)
% 0.21/0.49  ipcrm: permission denied for id (1217101920)
% 0.21/0.50  ipcrm: permission denied for id (1214447713)
% 0.21/0.50  ipcrm: permission denied for id (1218510946)
% 0.21/0.50  ipcrm: permission denied for id (1218576483)
% 0.21/0.50  ipcrm: permission denied for id (1217200228)
% 0.21/0.50  ipcrm: permission denied for id (1214578789)
% 0.21/0.50  ipcrm: permission denied for id (1217232998)
% 0.21/0.50  ipcrm: permission denied for id (1214644327)
% 0.21/0.51  ipcrm: permission denied for id (1217265768)
% 0.21/0.51  ipcrm: permission denied for id (1214709865)
% 0.21/0.51  ipcrm: permission denied for id (1217298538)
% 0.21/0.51  ipcrm: permission denied for id (1217331307)
% 0.21/0.51  ipcrm: permission denied for id (1214808172)
% 0.21/0.51  ipcrm: permission denied for id (1217364077)
% 0.21/0.52  ipcrm: permission denied for id (1218642031)
% 0.21/0.52  ipcrm: permission denied for id (1214939248)
% 0.21/0.52  ipcrm: permission denied for id (1214972017)
% 0.21/0.52  ipcrm: permission denied for id (1215004786)
% 0.21/0.52  ipcrm: permission denied for id (1217462387)
% 0.21/0.52  ipcrm: permission denied for id (1215070324)
% 0.21/0.52  ipcrm: permission denied for id (1215103093)
% 0.21/0.52  ipcrm: permission denied for id (1215135862)
% 0.21/0.53  ipcrm: permission denied for id (1215168631)
% 0.21/0.53  ipcrm: permission denied for id (1215201400)
% 0.21/0.53  ipcrm: permission denied for id (1218707578)
% 0.21/0.53  ipcrm: permission denied for id (1215299707)
% 0.36/0.53  ipcrm: permission denied for id (1215332476)
% 0.36/0.53  ipcrm: permission denied for id (1217560701)
% 0.36/0.53  ipcrm: permission denied for id (1217593470)
% 0.36/0.53  ipcrm: permission denied for id (1215430783)
% 0.39/0.66  % (18145)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.39/0.67  % (18157)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.39/0.67  % (18151)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.39/0.67  % (18147)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.39/0.68  % (18153)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.39/0.68  % (18149)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.39/0.68  % (18152)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.39/0.68  % (18162)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.39/0.69  % (18159)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.39/0.69  % (18148)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.39/0.69  % (18155)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.39/0.69  % (18166)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.39/0.69  % (18170)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.39/0.69  % (18173)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.39/0.69  % (18161)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.39/0.69  % (18172)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.39/0.69  % (18161)Refutation not found, incomplete strategy% (18161)------------------------------
% 0.39/0.69  % (18161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.69  % (18161)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.69  
% 0.39/0.69  % (18161)Memory used [KB]: 10746
% 0.39/0.69  % (18161)Time elapsed: 0.102 s
% 0.39/0.69  % (18161)------------------------------
% 0.39/0.69  % (18161)------------------------------
% 0.39/0.70  % (18164)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.39/0.70  % (18160)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.39/0.70  % (18146)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.39/0.70  % (18167)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.39/0.70  % (18165)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.39/0.70  % (18169)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.39/0.70  % (18174)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.39/0.70  % (18154)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.39/0.70  % (18156)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.39/0.70  % (18163)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.39/0.71  % (18168)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.39/0.71  % (18158)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.39/0.71  % (18150)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.39/0.71  % (18171)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.43/0.77  % (18151)Refutation found. Thanks to Tanya!
% 0.43/0.77  % SZS status Theorem for theBenchmark
% 0.43/0.77  % SZS output start Proof for theBenchmark
% 0.43/0.77  fof(f1687,plain,(
% 0.43/0.77    $false),
% 0.43/0.77    inference(avatar_sat_refutation,[],[f173,f1686])).
% 0.43/0.77  fof(f1686,plain,(
% 0.43/0.77    ~spl4_1),
% 0.43/0.77    inference(avatar_contradiction_clause,[],[f1685])).
% 0.43/0.77  fof(f1685,plain,(
% 0.43/0.77    $false | ~spl4_1),
% 0.43/0.77    inference(subsumption_resolution,[],[f1684,f65])).
% 0.43/0.77  fof(f65,plain,(
% 0.43/0.77    k2_funct_1(sK2) != sK3),
% 0.43/0.77    inference(cnf_transformation,[],[f51])).
% 0.43/0.77  fof(f51,plain,(
% 0.43/0.77    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.43/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f50,f49])).
% 0.43/0.77  fof(f49,plain,(
% 0.43/0.77    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.43/0.77    introduced(choice_axiom,[])).
% 0.43/0.77  fof(f50,plain,(
% 0.43/0.77    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.43/0.77    introduced(choice_axiom,[])).
% 0.43/0.77  fof(f24,plain,(
% 0.43/0.77    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.43/0.77    inference(flattening,[],[f23])).
% 0.43/0.77  fof(f23,plain,(
% 0.43/0.77    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.43/0.77    inference(ennf_transformation,[],[f22])).
% 0.43/0.77  fof(f22,negated_conjecture,(
% 0.43/0.77    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.43/0.77    inference(negated_conjecture,[],[f21])).
% 0.43/0.77  fof(f21,conjecture,(
% 0.43/0.77    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 0.43/0.77  fof(f1684,plain,(
% 0.43/0.77    k2_funct_1(sK2) = sK3 | ~spl4_1),
% 0.43/0.77    inference(forward_demodulation,[],[f1683,f490])).
% 0.43/0.77  fof(f490,plain,(
% 0.43/0.77    sK3 = k5_relat_1(k6_partfun1(sK1),sK3)),
% 0.43/0.77    inference(subsumption_resolution,[],[f486,f110])).
% 0.43/0.77  fof(f110,plain,(
% 0.43/0.77    v1_relat_1(sK3)),
% 0.43/0.77    inference(resolution,[],[f86,f59])).
% 0.43/0.77  fof(f59,plain,(
% 0.43/0.77    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.43/0.77    inference(cnf_transformation,[],[f51])).
% 0.43/0.77  fof(f86,plain,(
% 0.43/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.43/0.77    inference(cnf_transformation,[],[f40])).
% 0.43/0.77  fof(f40,plain,(
% 0.43/0.77    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.43/0.77    inference(ennf_transformation,[],[f13])).
% 0.43/0.77  fof(f13,axiom,(
% 0.43/0.77    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.43/0.77  fof(f486,plain,(
% 0.43/0.77    ~v1_relat_1(sK3) | sK3 = k5_relat_1(k6_partfun1(sK1),sK3)),
% 0.43/0.77    inference(resolution,[],[f196,f120])).
% 0.43/0.77  fof(f120,plain,(
% 0.43/0.77    v4_relat_1(sK3,sK1)),
% 0.43/0.77    inference(resolution,[],[f88,f59])).
% 0.43/0.77  fof(f88,plain,(
% 0.43/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.43/0.77    inference(cnf_transformation,[],[f42])).
% 0.43/0.77  fof(f42,plain,(
% 0.43/0.77    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.43/0.77    inference(ennf_transformation,[],[f14])).
% 0.43/0.77  fof(f14,axiom,(
% 0.43/0.77    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.43/0.77  fof(f196,plain,(
% 0.43/0.77    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k5_relat_1(k6_partfun1(X0),X1) = X1) )),
% 0.43/0.77    inference(duplicate_literal_removal,[],[f192])).
% 0.43/0.77  fof(f192,plain,(
% 0.43/0.77    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.43/0.77    inference(resolution,[],[f104,f84])).
% 0.43/0.77  fof(f84,plain,(
% 0.43/0.77    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.43/0.77    inference(cnf_transformation,[],[f52])).
% 0.43/0.77  fof(f52,plain,(
% 0.43/0.77    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.43/0.77    inference(nnf_transformation,[],[f39])).
% 0.43/0.77  fof(f39,plain,(
% 0.43/0.77    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.43/0.77    inference(ennf_transformation,[],[f1])).
% 0.43/0.77  fof(f1,axiom,(
% 0.43/0.77    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.43/0.77  fof(f104,plain,(
% 0.43/0.77    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_partfun1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 0.43/0.77    inference(definition_unfolding,[],[f83,f66])).
% 0.43/0.77  fof(f66,plain,(
% 0.43/0.77    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.43/0.77    inference(cnf_transformation,[],[f20])).
% 0.43/0.77  fof(f20,axiom,(
% 0.43/0.77    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.43/0.77  fof(f83,plain,(
% 0.43/0.77    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.43/0.77    inference(cnf_transformation,[],[f38])).
% 0.43/0.77  fof(f38,plain,(
% 0.43/0.77    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.43/0.77    inference(flattening,[],[f37])).
% 0.43/0.77  fof(f37,plain,(
% 0.43/0.77    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.43/0.77    inference(ennf_transformation,[],[f6])).
% 0.43/0.77  fof(f6,axiom,(
% 0.43/0.77    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.43/0.77  fof(f1683,plain,(
% 0.43/0.77    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_1),
% 0.43/0.77    inference(forward_demodulation,[],[f1682,f506])).
% 0.43/0.77  fof(f506,plain,(
% 0.43/0.77    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_1),
% 0.43/0.77    inference(resolution,[],[f493,f185])).
% 0.43/0.77  fof(f185,plain,(
% 0.43/0.77    ( ! [X2] : (~r1_tarski(k1_relat_1(sK2),X2) | k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X2))) ) | ~spl4_1),
% 0.43/0.77    inference(subsumption_resolution,[],[f183,f151])).
% 0.43/0.77  fof(f151,plain,(
% 0.43/0.77    v1_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 0.43/0.77    inference(avatar_component_clause,[],[f150])).
% 0.43/0.77  fof(f150,plain,(
% 0.43/0.77    spl4_1 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.43/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.43/0.77  fof(f183,plain,(
% 0.43/0.77    ( ! [X2] : (~r1_tarski(k1_relat_1(sK2),X2) | k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X2)) | ~v1_relat_1(k2_funct_1(sK2))) )),
% 0.43/0.77    inference(superposition,[],[f103,f178])).
% 0.43/0.77  fof(f178,plain,(
% 0.43/0.77    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)),
% 0.43/0.77    inference(subsumption_resolution,[],[f177,f109])).
% 0.43/0.77  fof(f109,plain,(
% 0.43/0.77    v1_relat_1(sK2)),
% 0.43/0.77    inference(resolution,[],[f86,f56])).
% 0.43/0.77  fof(f56,plain,(
% 0.43/0.77    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.43/0.77    inference(cnf_transformation,[],[f51])).
% 0.43/0.77  fof(f177,plain,(
% 0.43/0.77    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.43/0.77    inference(subsumption_resolution,[],[f175,f54])).
% 0.43/0.77  fof(f54,plain,(
% 0.43/0.77    v1_funct_1(sK2)),
% 0.43/0.77    inference(cnf_transformation,[],[f51])).
% 0.43/0.77  fof(f175,plain,(
% 0.43/0.77    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.43/0.77    inference(resolution,[],[f78,f62])).
% 0.43/0.77  fof(f62,plain,(
% 0.43/0.77    v2_funct_1(sK2)),
% 0.43/0.77    inference(cnf_transformation,[],[f51])).
% 0.43/0.77  fof(f78,plain,(
% 0.43/0.77    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.43/0.77    inference(cnf_transformation,[],[f31])).
% 0.43/0.77  fof(f31,plain,(
% 0.43/0.77    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.43/0.77    inference(flattening,[],[f30])).
% 0.43/0.77  fof(f30,plain,(
% 0.43/0.77    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.43/0.77    inference(ennf_transformation,[],[f11])).
% 0.43/0.77  fof(f11,axiom,(
% 0.43/0.77    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.43/0.77  fof(f103,plain,(
% 0.43/0.77    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 0.43/0.77    inference(definition_unfolding,[],[f82,f66])).
% 0.43/0.77  fof(f82,plain,(
% 0.43/0.77    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.43/0.77    inference(cnf_transformation,[],[f36])).
% 0.43/0.77  fof(f36,plain,(
% 0.43/0.77    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.43/0.77    inference(flattening,[],[f35])).
% 0.43/0.77  fof(f35,plain,(
% 0.43/0.77    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.43/0.77    inference(ennf_transformation,[],[f7])).
% 0.43/0.77  fof(f7,axiom,(
% 0.43/0.77    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.43/0.77  fof(f493,plain,(
% 0.43/0.77    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.43/0.77    inference(superposition,[],[f108,f491])).
% 0.43/0.77  fof(f491,plain,(
% 0.43/0.77    k1_relat_1(sK2) = k10_relat_1(k6_partfun1(sK0),k1_relat_1(sK2))),
% 0.43/0.77    inference(superposition,[],[f208,f489])).
% 0.43/0.77  fof(f489,plain,(
% 0.43/0.77    sK2 = k5_relat_1(k6_partfun1(sK0),sK2)),
% 0.43/0.77    inference(subsumption_resolution,[],[f485,f109])).
% 0.43/0.77  fof(f485,plain,(
% 0.43/0.77    ~v1_relat_1(sK2) | sK2 = k5_relat_1(k6_partfun1(sK0),sK2)),
% 0.43/0.77    inference(resolution,[],[f196,f119])).
% 0.43/0.77  fof(f119,plain,(
% 0.43/0.77    v4_relat_1(sK2,sK0)),
% 0.43/0.77    inference(resolution,[],[f88,f56])).
% 0.43/0.77  fof(f208,plain,(
% 0.43/0.77    ( ! [X1] : (k1_relat_1(k5_relat_1(k6_partfun1(X1),sK2)) = k10_relat_1(k6_partfun1(X1),k1_relat_1(sK2))) )),
% 0.43/0.77    inference(resolution,[],[f202,f97])).
% 0.43/0.77  fof(f97,plain,(
% 0.43/0.77    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.43/0.77    inference(definition_unfolding,[],[f68,f66])).
% 0.43/0.77  fof(f68,plain,(
% 0.43/0.77    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.43/0.77    inference(cnf_transformation,[],[f10])).
% 0.43/0.77  fof(f10,axiom,(
% 0.43/0.77    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.43/0.77  fof(f202,plain,(
% 0.43/0.77    ( ! [X5] : (~v1_relat_1(X5) | k1_relat_1(k5_relat_1(X5,sK2)) = k10_relat_1(X5,k1_relat_1(sK2))) )),
% 0.43/0.77    inference(resolution,[],[f73,f109])).
% 0.43/0.77  fof(f73,plain,(
% 0.43/0.77    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.43/0.77    inference(cnf_transformation,[],[f26])).
% 0.43/0.77  fof(f26,plain,(
% 0.43/0.77    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.43/0.77    inference(ennf_transformation,[],[f3])).
% 0.43/0.77  fof(f3,axiom,(
% 0.43/0.77    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.43/0.77  fof(f108,plain,(
% 0.43/0.77    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_partfun1(X0),X1),X0)) )),
% 0.43/0.77    inference(subsumption_resolution,[],[f107,f97])).
% 0.43/0.77  fof(f107,plain,(
% 0.43/0.77    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_partfun1(X0),X1),X0) | ~v1_relat_1(k6_partfun1(X0))) )),
% 0.43/0.77    inference(superposition,[],[f81,f99])).
% 0.43/0.77  fof(f99,plain,(
% 0.43/0.77    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.43/0.77    inference(definition_unfolding,[],[f70,f66])).
% 0.43/0.77  fof(f70,plain,(
% 0.43/0.77    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.43/0.77    inference(cnf_transformation,[],[f5])).
% 0.43/0.77  fof(f5,axiom,(
% 0.43/0.77    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.43/0.77  fof(f81,plain,(
% 0.43/0.77    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.43/0.77    inference(cnf_transformation,[],[f34])).
% 0.43/0.77  fof(f34,plain,(
% 0.43/0.77    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.43/0.77    inference(ennf_transformation,[],[f2])).
% 0.43/0.77  fof(f2,axiom,(
% 0.43/0.77    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.43/0.77  fof(f1682,plain,(
% 0.43/0.77    k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_1),
% 0.43/0.77    inference(forward_demodulation,[],[f1677,f267])).
% 0.43/0.77  fof(f267,plain,(
% 0.43/0.77    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 0.43/0.77    inference(forward_demodulation,[],[f266,f244])).
% 0.43/0.77  fof(f244,plain,(
% 0.43/0.77    sK1 = k2_relat_1(sK2)),
% 0.43/0.77    inference(forward_demodulation,[],[f241,f60])).
% 0.43/0.77  fof(f60,plain,(
% 0.43/0.77    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.43/0.77    inference(cnf_transformation,[],[f51])).
% 0.43/0.77  fof(f241,plain,(
% 0.43/0.77    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.43/0.77    inference(resolution,[],[f87,f56])).
% 0.43/0.77  fof(f87,plain,(
% 0.43/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.43/0.77    inference(cnf_transformation,[],[f41])).
% 0.43/0.77  fof(f41,plain,(
% 0.43/0.77    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.43/0.77    inference(ennf_transformation,[],[f15])).
% 0.43/0.77  fof(f15,axiom,(
% 0.43/0.77    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.43/0.77  fof(f266,plain,(
% 0.43/0.77    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 0.43/0.77    inference(subsumption_resolution,[],[f265,f109])).
% 0.43/0.77  fof(f265,plain,(
% 0.43/0.77    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_relat_1(sK2)),
% 0.43/0.77    inference(subsumption_resolution,[],[f263,f54])).
% 0.43/0.77  fof(f263,plain,(
% 0.43/0.77    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.43/0.77    inference(resolution,[],[f101,f62])).
% 0.43/0.77  fof(f101,plain,(
% 0.43/0.77    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.43/0.77    inference(definition_unfolding,[],[f80,f66])).
% 0.43/0.77  fof(f80,plain,(
% 0.43/0.77    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.43/0.77    inference(cnf_transformation,[],[f33])).
% 0.43/0.77  fof(f33,plain,(
% 0.43/0.77    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.43/0.77    inference(flattening,[],[f32])).
% 0.43/0.77  fof(f32,plain,(
% 0.43/0.77    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.43/0.77    inference(ennf_transformation,[],[f12])).
% 0.43/0.77  fof(f12,axiom,(
% 0.43/0.77    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.43/0.77  fof(f1677,plain,(
% 0.43/0.77    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) | ~spl4_1),
% 0.43/0.77    inference(resolution,[],[f1291,f151])).
% 0.43/0.77  fof(f1291,plain,(
% 0.43/0.77    ( ! [X16] : (~v1_relat_1(X16) | k5_relat_1(k5_relat_1(X16,sK2),sK3) = k5_relat_1(X16,k6_partfun1(sK0))) )),
% 0.43/0.77    inference(forward_demodulation,[],[f1289,f853])).
% 0.43/0.77  fof(f853,plain,(
% 0.43/0.77    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 0.43/0.77    inference(global_subsumption,[],[f843,f852])).
% 0.43/0.77  fof(f852,plain,(
% 0.43/0.77    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.43/0.77    inference(resolution,[],[f830,f294])).
% 0.43/0.77  fof(f294,plain,(
% 0.43/0.77    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 0.43/0.77    inference(resolution,[],[f90,f95])).
% 0.43/0.77  fof(f95,plain,(
% 0.43/0.77    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.43/0.77    inference(definition_unfolding,[],[f67,f66])).
% 0.43/0.77  fof(f67,plain,(
% 0.43/0.77    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.43/0.77    inference(cnf_transformation,[],[f17])).
% 0.43/0.77  fof(f17,axiom,(
% 0.43/0.77    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 0.43/0.77  fof(f90,plain,(
% 0.43/0.77    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.43/0.77    inference(cnf_transformation,[],[f53])).
% 0.43/0.77  fof(f53,plain,(
% 0.43/0.77    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.43/0.77    inference(nnf_transformation,[],[f44])).
% 0.43/0.77  fof(f44,plain,(
% 0.43/0.77    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.43/0.77    inference(flattening,[],[f43])).
% 0.43/0.77  fof(f43,plain,(
% 0.43/0.77    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.43/0.77    inference(ennf_transformation,[],[f16])).
% 0.43/0.77  fof(f16,axiom,(
% 0.43/0.77    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.43/0.77  fof(f830,plain,(
% 0.43/0.77    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 0.43/0.77    inference(backward_demodulation,[],[f61,f706])).
% 0.43/0.77  fof(f706,plain,(
% 0.43/0.77    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 0.43/0.77    inference(subsumption_resolution,[],[f702,f54])).
% 0.43/0.77  fof(f702,plain,(
% 0.43/0.77    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 0.43/0.77    inference(resolution,[],[f335,f56])).
% 0.43/0.77  fof(f335,plain,(
% 0.43/0.77    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(X5)) )),
% 0.43/0.77    inference(subsumption_resolution,[],[f332,f57])).
% 0.43/0.77  fof(f57,plain,(
% 0.43/0.77    v1_funct_1(sK3)),
% 0.43/0.77    inference(cnf_transformation,[],[f51])).
% 0.43/0.77  fof(f332,plain,(
% 0.43/0.77    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 0.43/0.77    inference(resolution,[],[f92,f59])).
% 0.43/0.77  fof(f92,plain,(
% 0.43/0.77    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.43/0.77    inference(cnf_transformation,[],[f46])).
% 0.43/0.77  fof(f46,plain,(
% 0.43/0.77    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.43/0.77    inference(flattening,[],[f45])).
% 0.43/0.77  fof(f45,plain,(
% 0.43/0.77    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.43/0.77    inference(ennf_transformation,[],[f19])).
% 0.43/0.77  fof(f19,axiom,(
% 0.43/0.77    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.43/0.77  fof(f61,plain,(
% 0.43/0.77    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.43/0.77    inference(cnf_transformation,[],[f51])).
% 0.43/0.77  fof(f843,plain,(
% 0.43/0.77    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.43/0.77    inference(subsumption_resolution,[],[f842,f54])).
% 0.43/0.77  fof(f842,plain,(
% 0.43/0.77    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 0.43/0.77    inference(subsumption_resolution,[],[f841,f56])).
% 0.43/0.77  fof(f841,plain,(
% 0.43/0.77    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 0.43/0.77    inference(subsumption_resolution,[],[f840,f57])).
% 0.43/0.77  fof(f840,plain,(
% 0.43/0.77    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 0.43/0.77    inference(subsumption_resolution,[],[f832,f59])).
% 0.43/0.77  fof(f832,plain,(
% 0.43/0.77    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 0.43/0.77    inference(superposition,[],[f94,f706])).
% 0.43/0.77  fof(f94,plain,(
% 0.43/0.77    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.43/0.77    inference(cnf_transformation,[],[f48])).
% 0.43/0.77  fof(f48,plain,(
% 0.43/0.77    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.43/0.77    inference(flattening,[],[f47])).
% 0.43/0.77  fof(f47,plain,(
% 0.43/0.77    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.43/0.77    inference(ennf_transformation,[],[f18])).
% 0.43/0.77  fof(f18,axiom,(
% 0.43/0.77    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.43/0.77  fof(f1289,plain,(
% 0.43/0.77    ( ! [X16] : (k5_relat_1(k5_relat_1(X16,sK2),sK3) = k5_relat_1(X16,k5_relat_1(sK2,sK3)) | ~v1_relat_1(X16)) )),
% 0.43/0.77    inference(resolution,[],[f284,f109])).
% 0.43/0.77  fof(f284,plain,(
% 0.43/0.77    ( ! [X10,X11] : (~v1_relat_1(X11) | k5_relat_1(k5_relat_1(X10,X11),sK3) = k5_relat_1(X10,k5_relat_1(X11,sK3)) | ~v1_relat_1(X10)) )),
% 0.43/0.77    inference(resolution,[],[f74,f110])).
% 0.43/0.77  fof(f74,plain,(
% 0.43/0.77    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.43/0.77    inference(cnf_transformation,[],[f27])).
% 0.43/0.77  fof(f27,plain,(
% 0.43/0.77    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.43/0.77    inference(ennf_transformation,[],[f4])).
% 0.43/0.77  fof(f4,axiom,(
% 0.43/0.77    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.43/0.77  fof(f173,plain,(
% 0.43/0.77    spl4_1),
% 0.43/0.77    inference(avatar_contradiction_clause,[],[f172])).
% 0.43/0.77  fof(f172,plain,(
% 0.43/0.77    $false | spl4_1),
% 0.43/0.77    inference(subsumption_resolution,[],[f171,f109])).
% 0.43/0.77  fof(f171,plain,(
% 0.43/0.77    ~v1_relat_1(sK2) | spl4_1),
% 0.43/0.77    inference(subsumption_resolution,[],[f170,f54])).
% 0.43/0.77  fof(f170,plain,(
% 0.43/0.77    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_1),
% 0.43/0.77    inference(resolution,[],[f152,f75])).
% 0.43/0.77  fof(f75,plain,(
% 0.43/0.77    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.43/0.77    inference(cnf_transformation,[],[f29])).
% 0.43/0.77  fof(f29,plain,(
% 0.43/0.77    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.43/0.77    inference(flattening,[],[f28])).
% 0.43/0.77  fof(f28,plain,(
% 0.43/0.77    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.43/0.77    inference(ennf_transformation,[],[f9])).
% 0.43/0.77  fof(f9,axiom,(
% 0.43/0.77    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.43/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.43/0.77  fof(f152,plain,(
% 0.43/0.77    ~v1_relat_1(k2_funct_1(sK2)) | spl4_1),
% 0.43/0.77    inference(avatar_component_clause,[],[f150])).
% 0.43/0.77  % SZS output end Proof for theBenchmark
% 0.43/0.77  % (18151)------------------------------
% 0.43/0.77  % (18151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.43/0.77  % (18151)Termination reason: Refutation
% 0.43/0.77  
% 0.43/0.77  % (18151)Memory used [KB]: 12153
% 0.43/0.77  % (18151)Time elapsed: 0.185 s
% 0.43/0.77  % (18151)------------------------------
% 0.43/0.77  % (18151)------------------------------
% 0.43/0.79  % (17978)Success in time 0.421 s
%------------------------------------------------------------------------------
