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
% DateTime   : Thu Dec  3 13:01:43 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 446 expanded)
%              Number of leaves         :   26 ( 142 expanded)
%              Depth                    :   19
%              Number of atoms          :  535 (3130 expanded)
%              Number of equality atoms :   57 (  74 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f479,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f209,f241,f383,f408,f455,f478])).

fof(f478,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f477])).

fof(f477,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f100,f287])).

fof(f287,plain,(
    v2_funct_2(sK3,sK0) ),
    inference(subsumption_resolution,[],[f286,f103])).

fof(f103,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f73,f54])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f42,f41])).

fof(f41,plain,
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

fof(f42,plain,
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f286,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f275,f125])).

fof(f125,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f76,f54])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f275,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f88,f273])).

fof(f273,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f141,f272])).

fof(f272,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f271,f52])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f271,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f270,f53])).

fof(f53,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f270,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f269,f54])).

fof(f269,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f268,f49])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f268,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f267,f50])).

fof(f50,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f267,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f266,f51])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f266,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f77,f55])).

fof(f55,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f141,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f74,f54])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f88,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f100,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f455,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | spl4_1
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f453,f84])).

fof(f84,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f60,f57])).

fof(f57,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f60,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f453,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f452,f353])).

fof(f353,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f295,f208])).

fof(f208,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl4_4
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f295,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f291,f49])).

fof(f291,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f214,f51])).

fof(f214,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f211,f52])).

fof(f211,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f80,f54])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f452,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_1
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f451,f103])).

fof(f451,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK3)
    | spl4_1
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f450,f52])).

fof(f450,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_1
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f449,f102])).

fof(f102,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f51])).

fof(f449,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_1
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f448,f49])).

fof(f448,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_1
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f445,f96])).

fof(f96,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f445,plain,
    ( v2_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_11 ),
    inference(resolution,[],[f378,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | v2_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
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
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

fof(f378,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl4_11
  <=> r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f408,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | spl4_12 ),
    inference(subsumption_resolution,[],[f406,f102])).

fof(f406,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_12 ),
    inference(subsumption_resolution,[],[f405,f121])).

fof(f121,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f75,f51])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f405,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl4_12 ),
    inference(resolution,[],[f382,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f382,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f380])).

fof(f380,plain,
    ( spl4_12
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f383,plain,
    ( spl4_11
    | ~ spl4_12
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f374,f206,f380,f376])).

fof(f374,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f373,f87])).

fof(f87,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f61,f57])).

fof(f61,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f373,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f372,f103])).

fof(f372,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f371,f52])).

fof(f371,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f370,f102])).

fof(f370,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f365,f49])).

fof(f365,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(superposition,[],[f162,f353])).

fof(f162,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k1_relat_1(X4),k1_relat_1(k5_relat_1(X4,X5)))
      | r1_tarski(k2_relat_1(X4),k1_relat_1(X5))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(subsumption_resolution,[],[f159,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f159,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k1_relat_1(k5_relat_1(X4,X5)),k1_relat_1(X4))
      | ~ r1_tarski(k1_relat_1(X4),k1_relat_1(k5_relat_1(X4,X5)))
      | r1_tarski(k2_relat_1(X4),k1_relat_1(X5))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(extensionality_resolution,[],[f72,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f241,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f239,f49])).

fof(f239,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f238,f51])).

fof(f238,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f237,f52])).

fof(f237,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f224,f54])).

fof(f224,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_3 ),
    inference(resolution,[],[f82,f204])).

fof(f204,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl4_3
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f209,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f199,f206,f202])).

fof(f199,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f183,f55])).

fof(f183,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f78,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f58,f57])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f101,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f56,f98,f94])).

fof(f56,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:06:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (5193)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.50  % (5201)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (5216)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.50  % (5208)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.50  % (5199)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (5197)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (5194)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (5198)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (5195)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (5215)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (5196)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (5222)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (5211)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.34/0.53  % (5214)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.34/0.53  % (5203)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.34/0.53  % (5217)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.34/0.53  % (5206)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.34/0.53  % (5220)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.54  % (5218)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.34/0.54  % (5212)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.34/0.54  % (5213)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.34/0.54  % (5204)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.34/0.54  % (5207)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.34/0.54  % (5202)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.34/0.54  % (5203)Refutation not found, incomplete strategy% (5203)------------------------------
% 1.34/0.54  % (5203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (5209)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.54  % (5221)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.54  % (5205)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.47/0.55  % (5221)Refutation not found, incomplete strategy% (5221)------------------------------
% 1.47/0.55  % (5221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (5221)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (5221)Memory used [KB]: 10874
% 1.47/0.55  % (5221)Time elapsed: 0.147 s
% 1.47/0.55  % (5221)------------------------------
% 1.47/0.55  % (5221)------------------------------
% 1.47/0.55  % (5209)Refutation not found, incomplete strategy% (5209)------------------------------
% 1.47/0.55  % (5209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (5209)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (5209)Memory used [KB]: 10746
% 1.47/0.55  % (5209)Time elapsed: 0.147 s
% 1.47/0.55  % (5209)------------------------------
% 1.47/0.55  % (5209)------------------------------
% 1.47/0.55  % (5210)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.47/0.55  % (5199)Refutation found. Thanks to Tanya!
% 1.47/0.55  % SZS status Theorem for theBenchmark
% 1.47/0.55  % SZS output start Proof for theBenchmark
% 1.47/0.55  fof(f479,plain,(
% 1.47/0.55    $false),
% 1.47/0.55    inference(avatar_sat_refutation,[],[f101,f209,f241,f383,f408,f455,f478])).
% 1.47/0.55  fof(f478,plain,(
% 1.47/0.55    spl4_2),
% 1.47/0.55    inference(avatar_contradiction_clause,[],[f477])).
% 1.47/0.55  fof(f477,plain,(
% 1.47/0.55    $false | spl4_2),
% 1.47/0.55    inference(subsumption_resolution,[],[f100,f287])).
% 1.47/0.55  fof(f287,plain,(
% 1.47/0.55    v2_funct_2(sK3,sK0)),
% 1.47/0.55    inference(subsumption_resolution,[],[f286,f103])).
% 1.47/0.55  fof(f103,plain,(
% 1.47/0.55    v1_relat_1(sK3)),
% 1.47/0.55    inference(resolution,[],[f73,f54])).
% 1.47/0.55  fof(f54,plain,(
% 1.47/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.47/0.55    inference(cnf_transformation,[],[f43])).
% 1.47/0.55  fof(f43,plain,(
% 1.47/0.55    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.47/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f42,f41])).
% 1.47/0.55  fof(f41,plain,(
% 1.47/0.55    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f42,plain,(
% 1.47/0.55    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f21,plain,(
% 1.47/0.55    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.47/0.55    inference(flattening,[],[f20])).
% 1.47/0.55  fof(f20,plain,(
% 1.47/0.55    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.47/0.55    inference(ennf_transformation,[],[f19])).
% 1.47/0.55  fof(f19,negated_conjecture,(
% 1.47/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.47/0.55    inference(negated_conjecture,[],[f18])).
% 1.47/0.55  fof(f18,conjecture,(
% 1.47/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 1.47/0.55  fof(f73,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f30])).
% 1.47/0.55  fof(f30,plain,(
% 1.47/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.55    inference(ennf_transformation,[],[f8])).
% 1.47/0.55  fof(f8,axiom,(
% 1.47/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.47/0.55  fof(f286,plain,(
% 1.47/0.55    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3)),
% 1.47/0.55    inference(subsumption_resolution,[],[f275,f125])).
% 1.47/0.55  fof(f125,plain,(
% 1.47/0.55    v5_relat_1(sK3,sK0)),
% 1.47/0.55    inference(resolution,[],[f76,f54])).
% 1.47/0.55  fof(f76,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f32])).
% 1.47/0.55  fof(f32,plain,(
% 1.47/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.55    inference(ennf_transformation,[],[f9])).
% 1.47/0.55  fof(f9,axiom,(
% 1.47/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.47/0.55  fof(f275,plain,(
% 1.47/0.55    ~v5_relat_1(sK3,sK0) | v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3)),
% 1.47/0.55    inference(superposition,[],[f88,f273])).
% 1.47/0.55  fof(f273,plain,(
% 1.47/0.55    sK0 = k2_relat_1(sK3)),
% 1.47/0.55    inference(backward_demodulation,[],[f141,f272])).
% 1.47/0.55  fof(f272,plain,(
% 1.47/0.55    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.47/0.55    inference(subsumption_resolution,[],[f271,f52])).
% 1.47/0.55  fof(f52,plain,(
% 1.47/0.55    v1_funct_1(sK3)),
% 1.47/0.55    inference(cnf_transformation,[],[f43])).
% 1.47/0.55  fof(f271,plain,(
% 1.47/0.55    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.47/0.55    inference(subsumption_resolution,[],[f270,f53])).
% 1.47/0.55  fof(f53,plain,(
% 1.47/0.55    v1_funct_2(sK3,sK1,sK0)),
% 1.47/0.55    inference(cnf_transformation,[],[f43])).
% 1.47/0.55  fof(f270,plain,(
% 1.47/0.55    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.47/0.55    inference(subsumption_resolution,[],[f269,f54])).
% 1.47/0.55  fof(f269,plain,(
% 1.47/0.55    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.47/0.55    inference(subsumption_resolution,[],[f268,f49])).
% 1.47/0.55  fof(f49,plain,(
% 1.47/0.55    v1_funct_1(sK2)),
% 1.47/0.55    inference(cnf_transformation,[],[f43])).
% 1.47/0.55  fof(f268,plain,(
% 1.47/0.55    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.47/0.55    inference(subsumption_resolution,[],[f267,f50])).
% 1.47/0.55  fof(f50,plain,(
% 1.47/0.55    v1_funct_2(sK2,sK0,sK1)),
% 1.47/0.55    inference(cnf_transformation,[],[f43])).
% 1.47/0.55  fof(f267,plain,(
% 1.47/0.55    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.47/0.55    inference(subsumption_resolution,[],[f266,f51])).
% 1.47/0.55  fof(f51,plain,(
% 1.47/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.47/0.55    inference(cnf_transformation,[],[f43])).
% 1.47/0.55  fof(f266,plain,(
% 1.47/0.55    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.47/0.55    inference(resolution,[],[f77,f55])).
% 1.47/0.55  fof(f55,plain,(
% 1.47/0.55    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.47/0.55    inference(cnf_transformation,[],[f43])).
% 1.47/0.55  fof(f77,plain,(
% 1.47/0.55    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  fof(f34,plain,(
% 1.47/0.55    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.47/0.55    inference(flattening,[],[f33])).
% 1.47/0.55  fof(f33,plain,(
% 1.47/0.55    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.47/0.55    inference(ennf_transformation,[],[f17])).
% 1.47/0.55  fof(f17,axiom,(
% 1.47/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.47/0.55  fof(f141,plain,(
% 1.47/0.55    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 1.47/0.55    inference(resolution,[],[f74,f54])).
% 1.47/0.55  fof(f74,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f31])).
% 1.47/0.55  fof(f31,plain,(
% 1.47/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.55    inference(ennf_transformation,[],[f10])).
% 1.47/0.55  fof(f10,axiom,(
% 1.47/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.47/0.55  fof(f88,plain,(
% 1.47/0.55    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.47/0.55    inference(equality_resolution,[],[f69])).
% 1.47/0.55  fof(f69,plain,(
% 1.47/0.55    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f45])).
% 1.47/0.55  fof(f45,plain,(
% 1.47/0.55    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.47/0.55    inference(nnf_transformation,[],[f29])).
% 1.47/0.55  fof(f29,plain,(
% 1.47/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.47/0.55    inference(flattening,[],[f28])).
% 1.47/0.55  fof(f28,plain,(
% 1.47/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.47/0.55    inference(ennf_transformation,[],[f13])).
% 1.47/0.55  fof(f13,axiom,(
% 1.47/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.47/0.55  fof(f100,plain,(
% 1.47/0.55    ~v2_funct_2(sK3,sK0) | spl4_2),
% 1.47/0.55    inference(avatar_component_clause,[],[f98])).
% 1.47/0.55  fof(f98,plain,(
% 1.47/0.55    spl4_2 <=> v2_funct_2(sK3,sK0)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.47/0.55  fof(f455,plain,(
% 1.47/0.55    spl4_1 | ~spl4_4 | ~spl4_11),
% 1.47/0.55    inference(avatar_contradiction_clause,[],[f454])).
% 1.47/0.55  fof(f454,plain,(
% 1.47/0.55    $false | (spl4_1 | ~spl4_4 | ~spl4_11)),
% 1.47/0.55    inference(subsumption_resolution,[],[f453,f84])).
% 1.47/0.55  fof(f84,plain,(
% 1.47/0.55    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.47/0.55    inference(definition_unfolding,[],[f60,f57])).
% 1.47/0.55  fof(f57,plain,(
% 1.47/0.55    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f16])).
% 1.47/0.55  fof(f16,axiom,(
% 1.47/0.55    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.47/0.55  fof(f60,plain,(
% 1.47/0.55    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.47/0.55    inference(cnf_transformation,[],[f5])).
% 1.47/0.55  fof(f5,axiom,(
% 1.47/0.55    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.47/0.55  fof(f453,plain,(
% 1.47/0.55    ~v2_funct_1(k6_partfun1(sK0)) | (spl4_1 | ~spl4_4 | ~spl4_11)),
% 1.47/0.55    inference(forward_demodulation,[],[f452,f353])).
% 1.47/0.55  fof(f353,plain,(
% 1.47/0.55    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_4),
% 1.47/0.55    inference(forward_demodulation,[],[f295,f208])).
% 1.47/0.55  fof(f208,plain,(
% 1.47/0.55    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl4_4),
% 1.47/0.55    inference(avatar_component_clause,[],[f206])).
% 1.47/0.55  fof(f206,plain,(
% 1.47/0.55    spl4_4 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.47/0.55  fof(f295,plain,(
% 1.47/0.55    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.47/0.55    inference(subsumption_resolution,[],[f291,f49])).
% 1.47/0.55  fof(f291,plain,(
% 1.47/0.55    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 1.47/0.55    inference(resolution,[],[f214,f51])).
% 1.47/0.55  fof(f214,plain,(
% 1.47/0.55    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(X5)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f211,f52])).
% 1.47/0.55  fof(f211,plain,(
% 1.47/0.55    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 1.47/0.55    inference(resolution,[],[f80,f54])).
% 1.47/0.55  fof(f80,plain,(
% 1.47/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f38])).
% 1.47/0.55  fof(f38,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.47/0.55    inference(flattening,[],[f37])).
% 1.47/0.55  fof(f37,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.47/0.55    inference(ennf_transformation,[],[f15])).
% 1.47/0.55  fof(f15,axiom,(
% 1.47/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.47/0.55  fof(f452,plain,(
% 1.47/0.55    ~v2_funct_1(k5_relat_1(sK2,sK3)) | (spl4_1 | ~spl4_11)),
% 1.47/0.55    inference(subsumption_resolution,[],[f451,f103])).
% 1.47/0.55  fof(f451,plain,(
% 1.47/0.55    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_relat_1(sK3) | (spl4_1 | ~spl4_11)),
% 1.47/0.55    inference(subsumption_resolution,[],[f450,f52])).
% 1.47/0.55  fof(f450,plain,(
% 1.47/0.55    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (spl4_1 | ~spl4_11)),
% 1.47/0.55    inference(subsumption_resolution,[],[f449,f102])).
% 1.47/0.55  fof(f102,plain,(
% 1.47/0.55    v1_relat_1(sK2)),
% 1.47/0.55    inference(resolution,[],[f73,f51])).
% 1.47/0.55  fof(f449,plain,(
% 1.47/0.55    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (spl4_1 | ~spl4_11)),
% 1.47/0.55    inference(subsumption_resolution,[],[f448,f49])).
% 1.47/0.55  fof(f448,plain,(
% 1.47/0.55    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (spl4_1 | ~spl4_11)),
% 1.47/0.55    inference(subsumption_resolution,[],[f445,f96])).
% 1.47/0.55  fof(f96,plain,(
% 1.47/0.55    ~v2_funct_1(sK2) | spl4_1),
% 1.47/0.55    inference(avatar_component_clause,[],[f94])).
% 1.47/0.55  fof(f94,plain,(
% 1.47/0.55    spl4_1 <=> v2_funct_1(sK2)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.47/0.55  fof(f445,plain,(
% 1.47/0.55    v2_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_11),
% 1.47/0.55    inference(resolution,[],[f378,f65])).
% 1.47/0.55  fof(f65,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f26])).
% 1.47/0.55  fof(f26,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.47/0.55    inference(flattening,[],[f25])).
% 1.47/0.55  fof(f25,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f7])).
% 1.47/0.55  fof(f7,axiom,(
% 1.47/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).
% 1.47/0.55  fof(f378,plain,(
% 1.47/0.55    r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~spl4_11),
% 1.47/0.55    inference(avatar_component_clause,[],[f376])).
% 1.47/0.55  fof(f376,plain,(
% 1.47/0.55    spl4_11 <=> r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.47/0.55  fof(f408,plain,(
% 1.47/0.55    spl4_12),
% 1.47/0.55    inference(avatar_contradiction_clause,[],[f407])).
% 1.47/0.55  fof(f407,plain,(
% 1.47/0.55    $false | spl4_12),
% 1.47/0.55    inference(subsumption_resolution,[],[f406,f102])).
% 1.47/0.55  fof(f406,plain,(
% 1.47/0.55    ~v1_relat_1(sK2) | spl4_12),
% 1.47/0.55    inference(subsumption_resolution,[],[f405,f121])).
% 1.47/0.55  fof(f121,plain,(
% 1.47/0.55    v4_relat_1(sK2,sK0)),
% 1.47/0.55    inference(resolution,[],[f75,f51])).
% 1.47/0.55  fof(f75,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f32])).
% 1.47/0.55  fof(f405,plain,(
% 1.47/0.55    ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl4_12),
% 1.47/0.55    inference(resolution,[],[f382,f66])).
% 1.47/0.55  fof(f66,plain,(
% 1.47/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f44])).
% 1.47/0.55  fof(f44,plain,(
% 1.47/0.55    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.47/0.55    inference(nnf_transformation,[],[f27])).
% 1.47/0.55  fof(f27,plain,(
% 1.47/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.47/0.55    inference(ennf_transformation,[],[f2])).
% 1.47/0.55  fof(f2,axiom,(
% 1.47/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.47/0.55  fof(f382,plain,(
% 1.47/0.55    ~r1_tarski(k1_relat_1(sK2),sK0) | spl4_12),
% 1.47/0.55    inference(avatar_component_clause,[],[f380])).
% 1.47/0.55  fof(f380,plain,(
% 1.47/0.55    spl4_12 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.47/0.55  fof(f383,plain,(
% 1.47/0.55    spl4_11 | ~spl4_12 | ~spl4_4),
% 1.47/0.55    inference(avatar_split_clause,[],[f374,f206,f380,f376])).
% 1.47/0.55  fof(f374,plain,(
% 1.47/0.55    ~r1_tarski(k1_relat_1(sK2),sK0) | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~spl4_4),
% 1.47/0.55    inference(forward_demodulation,[],[f373,f87])).
% 1.47/0.55  fof(f87,plain,(
% 1.47/0.55    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.47/0.55    inference(definition_unfolding,[],[f61,f57])).
% 1.47/0.55  fof(f61,plain,(
% 1.47/0.55    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.47/0.55    inference(cnf_transformation,[],[f4])).
% 1.47/0.55  fof(f4,axiom,(
% 1.47/0.55    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.47/0.55  fof(f373,plain,(
% 1.47/0.55    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~spl4_4),
% 1.47/0.55    inference(subsumption_resolution,[],[f372,f103])).
% 1.47/0.55  fof(f372,plain,(
% 1.47/0.55    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl4_4),
% 1.47/0.55    inference(subsumption_resolution,[],[f371,f52])).
% 1.47/0.55  fof(f371,plain,(
% 1.47/0.55    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_4),
% 1.47/0.55    inference(subsumption_resolution,[],[f370,f102])).
% 1.47/0.55  fof(f370,plain,(
% 1.47/0.55    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_4),
% 1.47/0.55    inference(subsumption_resolution,[],[f365,f49])).
% 1.47/0.55  fof(f365,plain,(
% 1.47/0.55    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_4),
% 1.47/0.55    inference(superposition,[],[f162,f353])).
% 1.47/0.55  fof(f162,plain,(
% 1.47/0.55    ( ! [X4,X5] : (~r1_tarski(k1_relat_1(X4),k1_relat_1(k5_relat_1(X4,X5))) | r1_tarski(k2_relat_1(X4),k1_relat_1(X5)) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f159,f63])).
% 1.47/0.55  fof(f63,plain,(
% 1.47/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f22])).
% 1.47/0.55  fof(f22,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.47/0.55    inference(ennf_transformation,[],[f3])).
% 1.47/0.55  fof(f3,axiom,(
% 1.47/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 1.47/0.55  fof(f159,plain,(
% 1.47/0.55    ( ! [X4,X5] : (~r1_tarski(k1_relat_1(k5_relat_1(X4,X5)),k1_relat_1(X4)) | ~r1_tarski(k1_relat_1(X4),k1_relat_1(k5_relat_1(X4,X5))) | r1_tarski(k2_relat_1(X4),k1_relat_1(X5)) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 1.47/0.55    inference(extensionality_resolution,[],[f72,f64])).
% 1.47/0.55  fof(f64,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f24])).
% 1.47/0.55  fof(f24,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.47/0.55    inference(flattening,[],[f23])).
% 1.47/0.55  fof(f23,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f6])).
% 1.47/0.55  fof(f6,axiom,(
% 1.47/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 1.47/0.55  fof(f72,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f47])).
% 1.47/0.55  fof(f47,plain,(
% 1.47/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.55    inference(flattening,[],[f46])).
% 1.47/0.55  fof(f46,plain,(
% 1.47/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.55    inference(nnf_transformation,[],[f1])).
% 1.47/0.55  fof(f1,axiom,(
% 1.47/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.47/0.55  fof(f241,plain,(
% 1.47/0.55    spl4_3),
% 1.47/0.55    inference(avatar_contradiction_clause,[],[f240])).
% 1.47/0.55  fof(f240,plain,(
% 1.47/0.55    $false | spl4_3),
% 1.47/0.55    inference(subsumption_resolution,[],[f239,f49])).
% 1.47/0.55  fof(f239,plain,(
% 1.47/0.55    ~v1_funct_1(sK2) | spl4_3),
% 1.47/0.55    inference(subsumption_resolution,[],[f238,f51])).
% 1.47/0.55  fof(f238,plain,(
% 1.47/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_3),
% 1.47/0.55    inference(subsumption_resolution,[],[f237,f52])).
% 1.47/0.55  fof(f237,plain,(
% 1.47/0.55    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_3),
% 1.47/0.55    inference(subsumption_resolution,[],[f224,f54])).
% 1.47/0.55  fof(f224,plain,(
% 1.47/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_3),
% 1.47/0.55    inference(resolution,[],[f82,f204])).
% 1.47/0.55  fof(f204,plain,(
% 1.47/0.55    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_3),
% 1.47/0.55    inference(avatar_component_clause,[],[f202])).
% 1.47/0.55  fof(f202,plain,(
% 1.47/0.55    spl4_3 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.47/0.55  fof(f82,plain,(
% 1.47/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f40])).
% 1.47/0.55  fof(f40,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.47/0.55    inference(flattening,[],[f39])).
% 1.47/0.55  fof(f39,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.47/0.55    inference(ennf_transformation,[],[f14])).
% 1.47/0.55  fof(f14,axiom,(
% 1.47/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.47/0.55  fof(f209,plain,(
% 1.47/0.55    ~spl4_3 | spl4_4),
% 1.47/0.55    inference(avatar_split_clause,[],[f199,f206,f202])).
% 1.47/0.55  fof(f199,plain,(
% 1.47/0.55    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.47/0.55    inference(resolution,[],[f183,f55])).
% 1.47/0.55  fof(f183,plain,(
% 1.47/0.55    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.47/0.55    inference(resolution,[],[f78,f83])).
% 1.47/0.55  fof(f83,plain,(
% 1.47/0.55    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.47/0.55    inference(definition_unfolding,[],[f58,f57])).
% 1.47/0.55  fof(f58,plain,(
% 1.47/0.55    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.47/0.55    inference(cnf_transformation,[],[f12])).
% 1.47/0.55  fof(f12,axiom,(
% 1.47/0.55    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.47/0.55  fof(f78,plain,(
% 1.47/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.47/0.55    inference(cnf_transformation,[],[f48])).
% 1.47/0.55  fof(f48,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.55    inference(nnf_transformation,[],[f36])).
% 1.47/0.55  fof(f36,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.55    inference(flattening,[],[f35])).
% 1.47/0.55  fof(f35,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.47/0.55    inference(ennf_transformation,[],[f11])).
% 1.47/0.55  fof(f11,axiom,(
% 1.47/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.47/0.55  fof(f101,plain,(
% 1.47/0.55    ~spl4_1 | ~spl4_2),
% 1.47/0.55    inference(avatar_split_clause,[],[f56,f98,f94])).
% 1.47/0.55  fof(f56,plain,(
% 1.47/0.55    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.47/0.55    inference(cnf_transformation,[],[f43])).
% 1.47/0.55  % SZS output end Proof for theBenchmark
% 1.47/0.55  % (5199)------------------------------
% 1.47/0.55  % (5199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (5199)Termination reason: Refutation
% 1.47/0.55  
% 1.47/0.55  % (5199)Memory used [KB]: 11001
% 1.47/0.55  % (5199)Time elapsed: 0.134 s
% 1.47/0.55  % (5199)------------------------------
% 1.47/0.55  % (5199)------------------------------
% 1.47/0.55  % (5192)Success in time 0.197 s
%------------------------------------------------------------------------------
