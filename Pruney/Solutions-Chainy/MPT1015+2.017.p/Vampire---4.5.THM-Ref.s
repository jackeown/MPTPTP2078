%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:28 EST 2020

% Result     : Theorem 6.28s
% Output     : Refutation 6.28s
% Verified   : 
% Statistics : Number of formulae       :  271 (5424 expanded)
%              Number of leaves         :   29 (1645 expanded)
%              Depth                    :  106
%              Number of atoms          : 1361 (40934 expanded)
%              Number of equality atoms :  285 (1445 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2576,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f76,f2253,f136])).

fof(f136,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f124])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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

fof(f2253,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,sK4) ),
    inference(backward_demodulation,[],[f79,f2251])).

fof(f2251,plain,(
    k6_partfun1(sK2) = sK4 ),
    inference(resolution,[],[f2244,f73])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))
    & v2_funct_1(sK3)
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f59,f58])).

fof(f58,plain,
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
          ( ~ r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2))
          & v2_funct_1(sK3)
          & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
          & v1_funct_2(X2,sK2,sK2)
          & v1_funct_1(X2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2))
        & v2_funct_1(sK3)
        & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
        & v1_funct_2(X2,sK2,sK2)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))
      & v2_funct_1(sK3)
      & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK4,sK2,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

fof(f2244,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k6_partfun1(sK2) = sK4 ) ),
    inference(resolution,[],[f2207,f107])).

fof(f107,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f2207,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | k6_partfun1(sK2) = sK4 ) ),
    inference(resolution,[],[f2198,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f2198,plain,
    ( ~ v1_relat_1(sK3)
    | k6_partfun1(sK2) = sK4 ),
    inference(subsumption_resolution,[],[f2197,f71])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f2197,plain,
    ( k6_partfun1(sK2) = sK4
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f2146,f78])).

fof(f78,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f2146,plain,
    ( k6_partfun1(sK2) = sK4
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f2132,f138])).

fof(f138,plain,(
    ! [X1] :
      ( sP0(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f103,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_funct_1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f103,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f33,f56,f55])).

fof(f55,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
              | k1_relat_1(X1) != k1_relat_1(X2)
              | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
              | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                    & k1_relat_1(X1) = k1_relat_1(X2)
                    & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                    & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) )
                 => X1 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).

fof(f2132,plain,
    ( ~ sP0(sK3)
    | k6_partfun1(sK2) = sK4 ),
    inference(resolution,[],[f2131,f82])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f2131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP0(sK3)
      | k6_partfun1(sK2) = sK4 ) ),
    inference(subsumption_resolution,[],[f2130,f946])).

fof(f946,plain,(
    sK3 = k5_relat_1(k6_partfun1(sK2),sK3) ),
    inference(resolution,[],[f941,f73])).

fof(f941,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | sK3 = k5_relat_1(k6_partfun1(sK2),sK3) ) ),
    inference(resolution,[],[f937,f73])).

fof(f937,plain,(
    ! [X26,X25] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X26)))
      | sK3 = k5_relat_1(k6_partfun1(sK2),sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ),
    inference(resolution,[],[f928,f71])).

fof(f928,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k5_relat_1(k6_partfun1(sK2),X0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) ) ),
    inference(resolution,[],[f794,f82])).

fof(f794,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X4)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | k5_relat_1(k6_partfun1(sK2),X3) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X6))) ) ),
    inference(resolution,[],[f787,f277])).

fof(f277,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(k6_partfun1(X3))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(k6_partfun1(X3),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k5_relat_1(k6_partfun1(X3),X0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ),
    inference(resolution,[],[f240,f206])).

fof(f206,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k5_relat_1(k6_partfun1(X1),X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k5_relat_1(k6_partfun1(X1),X0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k5_relat_1(k6_partfun1(X1),X0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(k5_relat_1(k6_partfun1(X1),X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f202,f123])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f201,f82])).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(duplicate_literal_removal,[],[f198])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f118,f128])).

fof(f128,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

fof(f240,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f239])).

fof(f239,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f127,f125])).

fof(f125,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
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
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f127,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f787,plain,(
    v1_funct_1(k6_partfun1(sK2)) ),
    inference(resolution,[],[f784,f73])).

fof(f784,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(subsumption_resolution,[],[f783,f165])).

fof(f165,plain,(
    sK2 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f163,f73])).

fof(f163,plain,
    ( sK2 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(superposition,[],[f160,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f160,plain,(
    sK2 = k1_relset_1(sK2,sK2,sK3) ),
    inference(subsumption_resolution,[],[f159,f71])).

fof(f159,plain,
    ( sK2 = k1_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f157,f73])).

fof(f157,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK2 = k1_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f110,f72])).

fof(f72,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f783,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 != k1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f782,f71])).

fof(f782,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK3)
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 != k1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f780,f78])).

fof(f780,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(sK3)
      | ~ v1_funct_1(sK3)
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 != k1_relat_1(sK3) ) ),
    inference(superposition,[],[f750,f256])).

fof(f256,plain,(
    sK3 = k5_relat_1(sK4,sK3) ),
    inference(subsumption_resolution,[],[f255,f74])).

fof(f74,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f255,plain,
    ( sK3 = k5_relat_1(sK4,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f254,f76])).

fof(f254,plain,
    ( sK3 = k5_relat_1(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f253,f71])).

fof(f253,plain,
    ( sK3 = k5_relat_1(sK4,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f249,f73])).

fof(f249,plain,
    ( sK3 = k5_relat_1(sK4,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f244,f125])).

fof(f244,plain,(
    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f243,f74])).

fof(f243,plain,
    ( ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f242,f76])).

fof(f242,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f241,f71])).

fof(f241,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f238,f73])).

fof(f238,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(resolution,[],[f127,f184])).

fof(f184,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f177,f73])).

fof(f177,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f123,f77])).

fof(f77,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f750,plain,(
    ! [X4,X5,X3] :
      ( ~ v2_funct_1(k5_relat_1(sK4,X3))
      | ~ v1_funct_1(X3)
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | sK2 != k1_relat_1(X3) ) ),
    inference(resolution,[],[f735,f107])).

fof(f735,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(sK4,X0))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k1_relat_1(X0) != sK2 ) ),
    inference(resolution,[],[f732,f85])).

fof(f732,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(X1) != sK2
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(sK4,X1))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(subsumption_resolution,[],[f731,f107])).

fof(f731,plain,(
    ! [X1] :
      ( ~ v2_funct_1(k5_relat_1(sK4,X1))
      | k1_relat_1(X1) != sK2
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_1(k6_partfun1(sK2))
      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ) ),
    inference(resolution,[],[f686,f76])).

fof(f686,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X1))
      | ~ v2_funct_1(k5_relat_1(sK4,X0))
      | k1_relat_1(X0) != sK2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k6_partfun1(sK2))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f633,f85])).

fof(f633,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK4)
      | v1_funct_1(k6_partfun1(sK2))
      | ~ v2_funct_1(k5_relat_1(sK4,X1))
      | k1_relat_1(X1) != sK2
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f632,f307])).

fof(f307,plain,(
    sK2 = k2_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f302,f107])).

fof(f302,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK2))
    | sK2 = k2_relat_1(sK4) ),
    inference(resolution,[],[f299,f73])).

fof(f299,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_relat_1(X1)
      | sK2 = k2_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f295,f107])).

fof(f295,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_relat_1(X1)
      | sK2 = k2_relat_1(sK4)
      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ) ),
    inference(resolution,[],[f291,f76])).

fof(f291,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_relat_1(X1)
      | sK2 = k2_relat_1(sK4)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f287,f76])).

fof(f287,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_relat_1(X1)
      | sK2 = k2_relat_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f285,f85])).

fof(f285,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK4)
      | sK2 = k2_relat_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) ) ),
    inference(resolution,[],[f276,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = X2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f142,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
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

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X0),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f117,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f276,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK2,k2_relat_1(sK4))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f275,f85])).

fof(f275,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | r1_tarski(sK2,k2_relat_1(sK4))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f269,f85])).

fof(f269,plain,
    ( ~ v1_relat_1(sK4)
    | r1_tarski(sK2,k2_relat_1(sK4))
    | ~ v1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f268,f165])).

fof(f268,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f267,f71])).

fof(f267,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f266,f74])).

fof(f266,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f265,f78])).

fof(f265,plain,
    ( ~ v2_funct_1(sK3)
    | r1_tarski(k1_relat_1(sK3),k2_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f264])).

fof(f264,plain,
    ( k2_relat_1(sK3) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | r1_tarski(k1_relat_1(sK3),k2_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f106,f256])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X0)
              & k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) )
           => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).

fof(f632,plain,(
    ! [X1] :
      ( v1_funct_1(k6_partfun1(sK2))
      | k1_relat_1(X1) != k2_relat_1(sK4)
      | ~ v2_funct_1(k5_relat_1(sK4,X1))
      | ~ v1_relat_1(sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f628,f74])).

fof(f628,plain,(
    ! [X1] :
      ( v1_funct_1(k6_partfun1(sK2))
      | k1_relat_1(X1) != k2_relat_1(sK4)
      | ~ v2_funct_1(k5_relat_1(sK4,X1))
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f619,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f619,plain,
    ( ~ v2_funct_1(sK4)
    | v1_funct_1(k6_partfun1(sK2)) ),
    inference(resolution,[],[f617,f76])).

fof(f617,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(sK4)
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(subsumption_resolution,[],[f616,f76])).

fof(f616,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k6_partfun1(sK2))
      | ~ v2_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ) ),
    inference(subsumption_resolution,[],[f615,f307])).

fof(f615,plain,(
    ! [X0,X1] :
      ( sK2 != k2_relat_1(sK4)
      | v1_funct_1(k6_partfun1(sK2))
      | ~ v2_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ) ),
    inference(superposition,[],[f614,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f614,plain,(
    ! [X2,X3] :
      ( sK2 != k2_relset_1(sK2,sK2,sK4)
      | v1_funct_1(k6_partfun1(sK2))
      | ~ v2_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(subsumption_resolution,[],[f607,f75])).

fof(f75,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f607,plain,(
    ! [X2,X3] :
      ( v1_funct_1(k6_partfun1(sK2))
      | sK2 != k2_relset_1(sK2,sK2,sK4)
      | ~ v2_funct_1(sK4)
      | ~ v1_funct_2(sK4,sK2,sK2)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f605,f76])).

fof(f605,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | v1_funct_1(k6_partfun1(sK2))
      | k2_relset_1(X4,X5,sK4) != X5
      | ~ v2_funct_1(sK4)
      | ~ v1_funct_2(sK4,X4,X5)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(subsumption_resolution,[],[f604,f107])).

fof(f604,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v2_funct_1(sK4)
      | v1_funct_1(k6_partfun1(sK2))
      | k2_relset_1(X4,X5,sK4) != X5
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(sK4,X4,X5)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ) ),
    inference(resolution,[],[f589,f76])).

fof(f589,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X4))
      | ~ v2_funct_1(sK4)
      | v1_funct_1(k6_partfun1(sK2))
      | k2_relset_1(X2,X3,sK4) != X3
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK4,X2,X3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f559,f85])).

fof(f559,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ v1_relat_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v2_funct_1(sK4)
      | v1_funct_1(k6_partfun1(sK2))
      | k2_relset_1(X12,X13,sK4) != X13
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | ~ v1_funct_2(sK4,X12,X13) ) ),
    inference(forward_demodulation,[],[f558,f307])).

fof(f558,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | v1_funct_1(k6_partfun1(k2_relat_1(sK4)))
      | ~ v2_funct_1(sK4)
      | ~ v1_relat_1(sK4)
      | k2_relset_1(X12,X13,sK4) != X13
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | ~ v1_funct_2(sK4,X12,X13) ) ),
    inference(subsumption_resolution,[],[f551,f74])).

fof(f551,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | v1_funct_1(k6_partfun1(k2_relat_1(sK4)))
      | ~ v2_funct_1(sK4)
      | ~ v1_relat_1(sK4)
      | k2_relset_1(X12,X13,sK4) != X13
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | ~ v1_funct_2(sK4,X12,X13) ) ),
    inference(resolution,[],[f545,f354])).

fof(f354,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_1(k6_partfun1(k2_relat_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relset_1(X5,X6,X0) != X6
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f353])).

fof(f353,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_funct_1(k6_partfun1(k2_relat_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relset_1(X5,X6,X0) != X6
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f274,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f274,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(k2_funct_1(X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_funct_1(k6_partfun1(k2_relat_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f270])).

fof(f270,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k6_partfun1(k2_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f228,f131])).

fof(f131,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f90,f80])).

fof(f80,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f90,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f228,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f126,f125])).

fof(f126,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f545,plain,(
    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) ),
    inference(resolution,[],[f542,f73])).

fof(f542,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) ) ),
    inference(subsumption_resolution,[],[f541,f165])).

fof(f541,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 != k1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f540,f71])).

fof(f540,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK3)
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 != k1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f538,f78])).

fof(f538,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(sK3)
      | ~ v1_funct_1(sK3)
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 != k1_relat_1(sK3) ) ),
    inference(superposition,[],[f530,f256])).

fof(f530,plain,(
    ! [X4,X5,X3] :
      ( ~ v2_funct_1(k5_relat_1(sK4,X3))
      | ~ v1_funct_1(X3)
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | sK2 != k1_relat_1(X3) ) ),
    inference(resolution,[],[f512,f107])).

fof(f512,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(sK4,X0))
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k1_relat_1(X0) != sK2 ) ),
    inference(resolution,[],[f510,f85])).

fof(f510,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(X1) != sK2
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(sK4,X1))
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) ) ),
    inference(subsumption_resolution,[],[f509,f107])).

fof(f509,plain,(
    ! [X1] :
      ( ~ v2_funct_1(k5_relat_1(sK4,X1))
      | k1_relat_1(X1) != sK2
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ) ),
    inference(resolution,[],[f498,f76])).

fof(f498,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X1))
      | ~ v2_funct_1(k5_relat_1(sK4,X0))
      | k1_relat_1(X0) != sK2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f469,f85])).

fof(f469,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK4)
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | ~ v2_funct_1(k5_relat_1(sK4,X1))
      | k1_relat_1(X1) != sK2
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f468,f307])).

fof(f468,plain,(
    ! [X1] :
      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | k1_relat_1(X1) != k2_relat_1(sK4)
      | ~ v2_funct_1(k5_relat_1(sK4,X1))
      | ~ v1_relat_1(sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f464,f74])).

fof(f464,plain,(
    ! [X1] :
      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | k1_relat_1(X1) != k2_relat_1(sK4)
      | ~ v2_funct_1(k5_relat_1(sK4,X1))
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f456,f104])).

fof(f456,plain,
    ( ~ v2_funct_1(sK4)
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) ),
    inference(subsumption_resolution,[],[f455,f76])).

fof(f455,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
    | ~ v2_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(subsumption_resolution,[],[f454,f307])).

fof(f454,plain,
    ( sK2 != k2_relat_1(sK4)
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
    | ~ v2_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(superposition,[],[f453,f115])).

fof(f453,plain,
    ( sK2 != k2_relset_1(sK2,sK2,sK4)
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
    | ~ v2_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f446,f75])).

fof(f446,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
    | sK2 != k2_relset_1(sK2,sK2,sK4)
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK2) ),
    inference(resolution,[],[f440,f76])).

fof(f440,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | k2_relset_1(X0,X1,sK4) != X1
      | ~ v2_funct_1(sK4)
      | ~ v1_funct_2(sK4,X0,X1) ) ),
    inference(subsumption_resolution,[],[f439,f76])).

fof(f439,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(sK4)
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | k2_relset_1(X0,X1,sK4) != X1
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK4,X0,X1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ) ),
    inference(subsumption_resolution,[],[f438,f307])).

fof(f438,plain,(
    ! [X0,X1] :
      ( sK2 != k2_relat_1(sK4)
      | ~ v2_funct_1(sK4)
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | k2_relset_1(X0,X1,sK4) != X1
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK4,X0,X1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ) ),
    inference(superposition,[],[f433,f115])).

fof(f433,plain,(
    ! [X2,X3] :
      ( sK2 != k2_relset_1(sK2,sK2,sK4)
      | ~ v2_funct_1(sK4)
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | k2_relset_1(X2,X3,sK4) != X3
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK4,X2,X3) ) ),
    inference(subsumption_resolution,[],[f426,f75])).

fof(f426,plain,(
    ! [X2,X3] :
      ( sK2 != k2_relset_1(sK2,sK2,sK4)
      | ~ v2_funct_1(sK4)
      | ~ v1_funct_2(sK4,sK2,sK2)
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | k2_relset_1(X2,X3,sK4) != X3
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK4,X2,X3) ) ),
    inference(resolution,[],[f424,f76])).

fof(f424,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,sK4) != X1
      | ~ v2_funct_1(sK4)
      | ~ v1_funct_2(sK4,X0,X1)
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | k2_relset_1(X3,X2,sK4) != X2
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | ~ v1_funct_2(sK4,X3,X2) ) ),
    inference(subsumption_resolution,[],[f423,f74])).

fof(f423,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_funct_1(sK4)
      | k2_relset_1(X0,X1,sK4) != X1
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK4,X0,X1)
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | k2_relset_1(X3,X2,sK4) != X2
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | ~ v1_funct_2(sK4,X3,X2)
      | ~ v1_funct_1(sK4) ) ),
    inference(subsumption_resolution,[],[f422,f107])).

fof(f422,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_funct_1(sK4)
      | k2_relset_1(X0,X1,sK4) != X1
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK4,X0,X1)
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | ~ v1_relat_1(k2_zfmisc_1(X2,X3))
      | k2_relset_1(X3,X2,sK4) != X2
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | ~ v1_funct_2(sK4,X3,X2)
      | ~ v1_funct_1(sK4) ) ),
    inference(duplicate_literal_removal,[],[f420])).

fof(f420,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_funct_1(sK4)
      | k2_relset_1(X0,X1,sK4) != X1
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK4,X0,X1)
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | ~ v1_relat_1(k2_zfmisc_1(X2,X3))
      | k2_relset_1(X3,X2,sK4) != X2
      | ~ v2_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | ~ v1_funct_2(sK4,X3,X2)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f415,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f415,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(X2))
      | ~ v2_funct_1(sK4)
      | k2_relset_1(X0,X1,sK4) != X1
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK4,X0,X1)
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f414,f85])).

fof(f414,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k2_funct_1(sK4))
      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | ~ v2_funct_1(sK4)
      | k2_relset_1(X0,X1,sK4) != X1
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK4,X0,X1) ) ),
    inference(subsumption_resolution,[],[f413,f74])).

fof(f413,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | ~ v1_relat_1(k2_funct_1(sK4))
      | ~ v2_funct_1(sK4)
      | k2_relset_1(X0,X1,sK4) != X1
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK4,X0,X1)
      | ~ v1_funct_1(sK4) ) ),
    inference(duplicate_literal_removal,[],[f412])).

fof(f412,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
      | ~ v1_relat_1(k2_funct_1(sK4))
      | ~ v2_funct_1(sK4)
      | k2_relset_1(X0,X1,sK4) != X1
      | ~ v2_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK4,X0,X1)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f406,f120])).

fof(f406,plain,
    ( ~ v1_funct_1(k2_funct_1(sK4))
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v2_funct_1(sK4) ),
    inference(superposition,[],[f88,f403])).

fof(f403,plain,
    ( sK2 = k1_relat_1(k2_funct_1(sK4))
    | ~ v2_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f402,f74])).

fof(f402,plain,
    ( ~ v1_funct_1(sK4)
    | sK2 = k1_relat_1(k2_funct_1(sK4))
    | ~ v2_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f401,f307])).

fof(f401,plain,
    ( sK2 != k2_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | sK2 = k1_relat_1(k2_funct_1(sK4))
    | ~ v2_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f396,f76])).

fof(f396,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK2 != k2_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | sK2 = k1_relat_1(k2_funct_1(sK4))
    | ~ v2_funct_1(sK4) ),
    inference(resolution,[],[f390,f75])).

fof(f390,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | k1_relat_1(k2_funct_1(X1)) = X0
      | ~ v2_funct_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f389])).

fof(f389,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X1) != X0
      | k1_relat_1(k2_funct_1(X1)) = X0
      | ~ v2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f384,f115])).

fof(f384,plain,(
    ! [X0,X1] :
      ( k2_relset_1(X1,X1,X0) != X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_funct_2(X0,X1,X1)
      | ~ v1_funct_1(X0)
      | k2_relat_1(X0) != X1
      | k1_relat_1(k2_funct_1(X0)) = X1
      | ~ v2_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f383])).

fof(f383,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_funct_2(X0,X1,X1)
      | ~ v1_funct_1(X0)
      | k2_relat_1(X0) != X1
      | k1_relat_1(k2_funct_1(X0)) = X1
      | k2_relset_1(X1,X1,X0) != X1
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_funct_2(X0,X1,X1)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f349,f122])).

fof(f349,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X1) != X0
      | k1_relat_1(k2_funct_1(X1)) = X0 ) ),
    inference(superposition,[],[f290,f114])).

fof(f290,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,k2_funct_1(X1)) = X0
      | ~ v2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X1) != X0 ) ),
    inference(duplicate_literal_removal,[],[f289])).

fof(f289,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != X0
      | ~ v2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k1_relset_1(X0,X0,k2_funct_1(X1)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f216,f115])).

fof(f216,plain,(
    ! [X0,X1] :
      ( k2_relset_1(X0,X0,X1) != X0
      | ~ v2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k1_relset_1(X0,X0,k2_funct_1(X1)) = X0 ) ),
    inference(subsumption_resolution,[],[f215,f122])).

fof(f215,plain,(
    ! [X0,X1] :
      ( k2_relset_1(X0,X0,X1) != X0
      | ~ v2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,k2_funct_1(X1)) = X0 ) ),
    inference(subsumption_resolution,[],[f214,f120])).

fof(f214,plain,(
    ! [X0,X1] :
      ( k2_relset_1(X0,X0,X1) != X0
      | ~ v2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,k2_funct_1(X1)) = X0
      | ~ v1_funct_1(k2_funct_1(X1)) ) ),
    inference(resolution,[],[f121,f110])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f2130,plain,(
    ! [X0,X1] :
      ( k6_partfun1(sK2) = sK4
      | ~ sP0(sK3)
      | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK3 != k5_relat_1(k6_partfun1(sK2),sK3) ) ),
    inference(subsumption_resolution,[],[f2129,f133])).

fof(f133,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f2129,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2,sK2)
      | k6_partfun1(sK2) = sK4
      | ~ sP0(sK3)
      | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK3 != k5_relat_1(k6_partfun1(sK2),sK3) ) ),
    inference(trivial_inequality_removal,[],[f2126])).

fof(f2126,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2,sK2)
      | sK2 != sK2
      | k6_partfun1(sK2) = sK4
      | ~ sP0(sK3)
      | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK3 != k5_relat_1(k6_partfun1(sK2),sK3) ) ),
    inference(resolution,[],[f2117,f787])).

fof(f2117,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(k6_partfun1(X0))
      | ~ r1_tarski(X0,sK2)
      | sK2 != X0
      | k6_partfun1(X0) = sK4
      | ~ sP0(sK3)
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | sK3 != k5_relat_1(k6_partfun1(X0),sK3) ) ),
    inference(forward_demodulation,[],[f2115,f130])).

fof(f130,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f83,f80])).

fof(f83,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f2115,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,sK2)
      | ~ v1_funct_1(k6_partfun1(X0))
      | k6_partfun1(X0) = sK4
      | ~ sP0(sK3)
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | sK3 != k5_relat_1(k6_partfun1(X0),sK3)
      | sK2 != k1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f2112,f129])).

fof(f129,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f84,f80])).

fof(f84,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f2112,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k2_relat_1(X3),sK2)
      | ~ v1_funct_1(X3)
      | sK4 = X3
      | ~ sP0(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | sK3 != k5_relat_1(X3,sK3)
      | sK2 != k1_relat_1(X3) ) ),
    inference(resolution,[],[f658,f76])).

fof(f658,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | sK2 != k1_relat_1(X6)
      | ~ v1_funct_1(X6)
      | sK4 = X6
      | ~ sP0(sK3)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | sK3 != k5_relat_1(X6,sK3)
      | ~ r1_tarski(k2_relat_1(X6),sK2) ) ),
    inference(forward_demodulation,[],[f657,f256])).

fof(f657,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( sK2 != k1_relat_1(X6)
      | ~ v1_funct_1(X6)
      | sK4 = X6
      | ~ sP0(sK3)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | k5_relat_1(sK4,sK3) != k5_relat_1(X6,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ r1_tarski(k2_relat_1(X6),sK2) ) ),
    inference(forward_demodulation,[],[f656,f172])).

fof(f172,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f170,f76])).

fof(f170,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(superposition,[],[f162,f114])).

fof(f162,plain,(
    sK2 = k1_relset_1(sK2,sK2,sK4) ),
    inference(subsumption_resolution,[],[f161,f74])).

fof(f161,plain,
    ( sK2 = k1_relset_1(sK2,sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f158,f76])).

fof(f158,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK2 = k1_relset_1(sK2,sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f110,f75])).

fof(f656,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( ~ v1_funct_1(X6)
      | sK4 = X6
      | k1_relat_1(sK4) != k1_relat_1(X6)
      | ~ sP0(sK3)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | k5_relat_1(sK4,sK3) != k5_relat_1(X6,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ r1_tarski(k2_relat_1(X6),sK2) ) ),
    inference(subsumption_resolution,[],[f655,f74])).

fof(f655,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( ~ v1_funct_1(X6)
      | sK4 = X6
      | ~ v1_funct_1(sK4)
      | k1_relat_1(sK4) != k1_relat_1(X6)
      | ~ sP0(sK3)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | k5_relat_1(sK4,sK3) != k5_relat_1(X6,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ r1_tarski(k2_relat_1(X6),sK2) ) ),
    inference(subsumption_resolution,[],[f653,f133])).

fof(f653,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( ~ r1_tarski(sK2,sK2)
      | ~ v1_funct_1(X6)
      | sK4 = X6
      | ~ v1_funct_1(sK4)
      | k1_relat_1(sK4) != k1_relat_1(X6)
      | ~ sP0(sK3)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | k5_relat_1(sK4,sK3) != k5_relat_1(X6,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ r1_tarski(k2_relat_1(X6),sK2) ) ),
    inference(superposition,[],[f524,f307])).

fof(f524,plain,(
    ! [X14,X17,X15,X13,X18,X16] :
      ( ~ r1_tarski(k2_relat_1(X13),sK2)
      | ~ v1_funct_1(X14)
      | X13 = X14
      | ~ v1_funct_1(X13)
      | k1_relat_1(X14) != k1_relat_1(X13)
      | ~ sP0(sK3)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | k5_relat_1(X14,sK3) != k5_relat_1(X13,sK3)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | ~ r1_tarski(k2_relat_1(X14),sK2) ) ),
    inference(superposition,[],[f442,f165])).

fof(f442,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] :
      ( ~ r1_tarski(k2_relat_1(X7),k1_relat_1(X8))
      | ~ v1_funct_1(X9)
      | X7 = X9
      | ~ v1_funct_1(X7)
      | k1_relat_1(X9) != k1_relat_1(X7)
      | ~ sP0(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | k5_relat_1(X9,X8) != k5_relat_1(X7,X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | ~ r1_tarski(k2_relat_1(X9),k1_relat_1(X8)) ) ),
    inference(resolution,[],[f368,f107])).

fof(f368,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X5)
      | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X1))
      | ~ v1_funct_1(X0)
      | X0 = X2
      | ~ v1_funct_1(X2)
      | k1_relat_1(X0) != k1_relat_1(X2)
      | ~ sP0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k5_relat_1(X0,X1) != k5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X5))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(resolution,[],[f329,f85])).

fof(f329,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_relat_1(X5)
      | ~ r1_tarski(k2_relat_1(X6),k1_relat_1(X7))
      | ~ r1_tarski(k2_relat_1(X5),k1_relat_1(X7))
      | ~ v1_funct_1(X6)
      | X5 = X6
      | ~ v1_funct_1(X5)
      | k1_relat_1(X5) != k1_relat_1(X6)
      | ~ sP0(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | k5_relat_1(X5,X7) != k5_relat_1(X6,X7) ) ),
    inference(resolution,[],[f258,f107])).

fof(f258,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X3)
      | k1_relat_1(X0) != k1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | X0 = X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ sP0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k5_relat_1(X0,X1) != k5_relat_1(X2,X1) ) ),
    inference(resolution,[],[f93,f85])).

fof(f93,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_relat_1(X4)
      | k5_relat_1(X3,X0) != k5_relat_1(X4,X0)
      | k1_relat_1(X3) != k1_relat_1(X4)
      | ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X0))
      | ~ v1_funct_1(X4)
      | X3 = X4
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK5(X0) != sK6(X0)
          & k5_relat_1(sK5(X0),X0) = k5_relat_1(sK6(X0),X0)
          & k1_relat_1(sK5(X0)) = k1_relat_1(sK6(X0))
          & r1_tarski(k2_relat_1(sK6(X0)),k1_relat_1(X0))
          & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0))
          & v1_funct_1(sK6(X0))
          & v1_relat_1(sK6(X0))
          & v1_funct_1(sK5(X0))
          & v1_relat_1(sK5(X0)) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( X3 = X4
                | k5_relat_1(X3,X0) != k5_relat_1(X4,X0)
                | k1_relat_1(X3) != k1_relat_1(X4)
                | ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X0))
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f63,f65,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
              & k1_relat_1(X1) = k1_relat_1(X2)
              & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
              & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( sK5(X0) != X2
            & k5_relat_1(X2,X0) = k5_relat_1(sK5(X0),X0)
            & k1_relat_1(X2) = k1_relat_1(sK5(X0))
            & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
            & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0))
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(sK5(X0))
        & v1_relat_1(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK5(X0) != X2
          & k5_relat_1(X2,X0) = k5_relat_1(sK5(X0),X0)
          & k1_relat_1(X2) = k1_relat_1(sK5(X0))
          & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
          & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( sK5(X0) != sK6(X0)
        & k5_relat_1(sK5(X0),X0) = k5_relat_1(sK6(X0),X0)
        & k1_relat_1(sK5(X0)) = k1_relat_1(sK6(X0))
        & r1_tarski(k2_relat_1(sK6(X0)),k1_relat_1(X0))
        & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0))
        & v1_funct_1(sK6(X0))
        & v1_relat_1(sK6(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                & k1_relat_1(X1) = k1_relat_1(X2)
                & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( X3 = X4
                | k5_relat_1(X3,X0) != k5_relat_1(X4,X0)
                | k1_relat_1(X3) != k1_relat_1(X4)
                | ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X0))
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                & k1_relat_1(X1) = k1_relat_1(X2)
                & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) ) )
      & ( ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f79,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f60])).

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (18391)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.50  % (18396)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.50  % (18384)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.50  % (18412)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.51  % (18410)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.51  % (18383)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.51  % (18387)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.51  % (18388)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.51  % (18393)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.51  % (18399)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.51  % (18399)Refutation not found, incomplete strategy% (18399)------------------------------
% 0.19/0.51  % (18399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (18399)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (18399)Memory used [KB]: 10746
% 0.19/0.51  % (18399)Time elapsed: 0.121 s
% 0.19/0.51  % (18399)------------------------------
% 0.19/0.51  % (18399)------------------------------
% 0.19/0.52  % (18397)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.52  % (18404)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.52  % (18402)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.52  % (18395)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.52  % (18398)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.52  % (18385)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.53  % (18394)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.35/0.53  % (18386)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.35/0.53  % (18392)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.35/0.53  % (18403)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.35/0.53  % (18389)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.53  % (18390)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.35/0.53  % (18405)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.35/0.53  % (18401)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.35/0.54  % (18408)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.35/0.54  % (18411)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.35/0.54  % (18407)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.35/0.54  % (18409)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.45/0.54  % (18400)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.45/0.56  % (18406)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.45/0.58  % (18393)Refutation not found, incomplete strategy% (18393)------------------------------
% 1.45/0.58  % (18393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (18393)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.58  
% 1.45/0.58  % (18393)Memory used [KB]: 11385
% 1.45/0.58  % (18393)Time elapsed: 0.194 s
% 1.45/0.58  % (18393)------------------------------
% 1.45/0.58  % (18393)------------------------------
% 1.45/0.59  % (18411)Refutation not found, incomplete strategy% (18411)------------------------------
% 1.45/0.59  % (18411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.59  % (18411)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.59  
% 1.45/0.59  % (18411)Memory used [KB]: 11385
% 1.45/0.59  % (18411)Time elapsed: 0.200 s
% 1.45/0.59  % (18411)------------------------------
% 1.45/0.59  % (18411)------------------------------
% 2.09/0.64  % (18413)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.46/0.71  % (18414)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.46/0.73  % (18415)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.14/0.80  % (18385)Time limit reached!
% 3.14/0.80  % (18385)------------------------------
% 3.14/0.80  % (18385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.14/0.80  % (18385)Termination reason: Time limit
% 3.14/0.80  % (18385)Termination phase: Saturation
% 3.14/0.80  
% 3.14/0.80  % (18385)Memory used [KB]: 6780
% 3.14/0.80  % (18385)Time elapsed: 0.400 s
% 3.14/0.80  % (18385)------------------------------
% 3.14/0.80  % (18385)------------------------------
% 3.14/0.81  % (18407)Time limit reached!
% 3.14/0.81  % (18407)------------------------------
% 3.14/0.81  % (18407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.14/0.81  % (18407)Termination reason: Time limit
% 3.14/0.81  % (18407)Termination phase: Saturation
% 3.14/0.81  
% 3.14/0.81  % (18407)Memory used [KB]: 13304
% 3.14/0.81  % (18407)Time elapsed: 0.417 s
% 3.14/0.81  % (18407)------------------------------
% 3.14/0.81  % (18407)------------------------------
% 3.67/0.92  % (18412)Time limit reached!
% 3.67/0.92  % (18412)------------------------------
% 3.67/0.92  % (18412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.67/0.92  % (18389)Time limit reached!
% 3.67/0.92  % (18389)------------------------------
% 3.67/0.92  % (18389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.67/0.92  % (18412)Termination reason: Time limit
% 3.67/0.92  
% 3.67/0.92  % (18412)Memory used [KB]: 5245
% 3.67/0.92  % (18412)Time elapsed: 0.516 s
% 3.67/0.92  % (18412)------------------------------
% 3.67/0.92  % (18412)------------------------------
% 4.22/0.93  % (18389)Termination reason: Time limit
% 4.22/0.93  
% 4.22/0.93  % (18389)Memory used [KB]: 14583
% 4.22/0.93  % (18389)Time elapsed: 0.501 s
% 4.22/0.93  % (18389)------------------------------
% 4.22/0.93  % (18389)------------------------------
% 4.22/0.94  % (18416)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.22/0.95  % (18417)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.22/0.96  % (18397)Time limit reached!
% 4.22/0.96  % (18397)------------------------------
% 4.22/0.96  % (18397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.62/0.98  % (18397)Termination reason: Time limit
% 4.62/0.98  
% 4.62/0.98  % (18397)Memory used [KB]: 6268
% 4.62/0.98  % (18397)Time elapsed: 0.530 s
% 4.62/0.98  % (18397)------------------------------
% 4.62/0.98  % (18397)------------------------------
% 5.05/1.06  % (18419)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.67/1.08  % (18390)Time limit reached!
% 5.67/1.08  % (18390)------------------------------
% 5.67/1.08  % (18390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.67/1.08  % (18390)Termination reason: Time limit
% 5.67/1.08  
% 5.67/1.08  % (18390)Memory used [KB]: 4477
% 5.67/1.08  % (18390)Time elapsed: 0.678 s
% 5.67/1.08  % (18390)------------------------------
% 5.67/1.08  % (18390)------------------------------
% 5.67/1.10  % (18418)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.67/1.12  % (18420)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 6.28/1.16  % (18405)Refutation found. Thanks to Tanya!
% 6.28/1.16  % SZS status Theorem for theBenchmark
% 6.28/1.16  % SZS output start Proof for theBenchmark
% 6.28/1.16  fof(f2576,plain,(
% 6.28/1.16    $false),
% 6.28/1.16    inference(unit_resulting_resolution,[],[f76,f2253,f136])).
% 6.28/1.16  fof(f136,plain,(
% 6.28/1.16    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.28/1.16    inference(duplicate_literal_removal,[],[f135])).
% 6.28/1.16  fof(f135,plain,(
% 6.28/1.16    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.28/1.16    inference(equality_resolution,[],[f124])).
% 6.28/1.16  fof(f124,plain,(
% 6.28/1.16    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.28/1.16    inference(cnf_transformation,[],[f70])).
% 6.28/1.16  fof(f70,plain,(
% 6.28/1.16    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.28/1.16    inference(nnf_transformation,[],[f48])).
% 6.28/1.16  fof(f48,plain,(
% 6.28/1.16    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.28/1.16    inference(flattening,[],[f47])).
% 6.28/1.16  fof(f47,plain,(
% 6.28/1.16    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.28/1.16    inference(ennf_transformation,[],[f14])).
% 6.28/1.16  fof(f14,axiom,(
% 6.28/1.16    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 6.28/1.16  fof(f2253,plain,(
% 6.28/1.16    ~r2_relset_1(sK2,sK2,sK4,sK4)),
% 6.28/1.16    inference(backward_demodulation,[],[f79,f2251])).
% 6.28/1.16  fof(f2251,plain,(
% 6.28/1.16    k6_partfun1(sK2) = sK4),
% 6.28/1.16    inference(resolution,[],[f2244,f73])).
% 6.28/1.16  fof(f73,plain,(
% 6.28/1.16    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.28/1.16    inference(cnf_transformation,[],[f60])).
% 6.28/1.16  fof(f60,plain,(
% 6.28/1.16    (~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 6.28/1.16    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f59,f58])).
% 6.28/1.16  fof(f58,plain,(
% 6.28/1.16    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 6.28/1.16    introduced(choice_axiom,[])).
% 6.28/1.16  fof(f59,plain,(
% 6.28/1.16    ? [X2] : (~r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) => (~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4))),
% 6.28/1.16    introduced(choice_axiom,[])).
% 6.28/1.16  fof(f26,plain,(
% 6.28/1.16    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 6.28/1.16    inference(flattening,[],[f25])).
% 6.28/1.16  fof(f25,plain,(
% 6.28/1.16    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 6.28/1.16    inference(ennf_transformation,[],[f24])).
% 6.28/1.16  fof(f24,negated_conjecture,(
% 6.28/1.16    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 6.28/1.16    inference(negated_conjecture,[],[f23])).
% 6.28/1.16  fof(f23,conjecture,(
% 6.28/1.16    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).
% 6.28/1.16  fof(f2244,plain,(
% 6.28/1.16    ( ! [X2,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k6_partfun1(sK2) = sK4) )),
% 6.28/1.16    inference(resolution,[],[f2207,f107])).
% 6.28/1.16  fof(f107,plain,(
% 6.28/1.16    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 6.28/1.16    inference(cnf_transformation,[],[f4])).
% 6.28/1.16  fof(f4,axiom,(
% 6.28/1.16    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 6.28/1.16  fof(f2207,plain,(
% 6.28/1.16    ( ! [X0] : (~v1_relat_1(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | k6_partfun1(sK2) = sK4) )),
% 6.28/1.16    inference(resolution,[],[f2198,f85])).
% 6.28/1.16  fof(f85,plain,(
% 6.28/1.16    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f27])).
% 6.28/1.16  fof(f27,plain,(
% 6.28/1.16    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 6.28/1.16    inference(ennf_transformation,[],[f2])).
% 6.28/1.16  fof(f2,axiom,(
% 6.28/1.16    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 6.28/1.16  fof(f2198,plain,(
% 6.28/1.16    ~v1_relat_1(sK3) | k6_partfun1(sK2) = sK4),
% 6.28/1.16    inference(subsumption_resolution,[],[f2197,f71])).
% 6.28/1.16  fof(f71,plain,(
% 6.28/1.16    v1_funct_1(sK3)),
% 6.28/1.16    inference(cnf_transformation,[],[f60])).
% 6.28/1.16  fof(f2197,plain,(
% 6.28/1.16    k6_partfun1(sK2) = sK4 | ~v1_relat_1(sK3) | ~v1_funct_1(sK3)),
% 6.28/1.16    inference(subsumption_resolution,[],[f2146,f78])).
% 6.28/1.16  fof(f78,plain,(
% 6.28/1.16    v2_funct_1(sK3)),
% 6.28/1.16    inference(cnf_transformation,[],[f60])).
% 6.28/1.16  fof(f2146,plain,(
% 6.28/1.16    k6_partfun1(sK2) = sK4 | ~v1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3)),
% 6.28/1.16    inference(resolution,[],[f2132,f138])).
% 6.28/1.16  fof(f138,plain,(
% 6.28/1.16    ( ! [X1] : (sP0(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 6.28/1.16    inference(resolution,[],[f103,f91])).
% 6.28/1.16  fof(f91,plain,(
% 6.28/1.16    ( ! [X0] : (~sP1(X0) | ~v2_funct_1(X0) | sP0(X0)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f61])).
% 6.28/1.16  fof(f61,plain,(
% 6.28/1.16    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 6.28/1.16    inference(nnf_transformation,[],[f56])).
% 6.28/1.16  fof(f56,plain,(
% 6.28/1.16    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 6.28/1.16    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 6.28/1.16  fof(f103,plain,(
% 6.28/1.16    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f57])).
% 6.28/1.16  fof(f57,plain,(
% 6.28/1.16    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.28/1.16    inference(definition_folding,[],[f33,f56,f55])).
% 6.28/1.16  fof(f55,plain,(
% 6.28/1.16    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.28/1.16    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 6.28/1.16  fof(f33,plain,(
% 6.28/1.16    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.28/1.16    inference(flattening,[],[f32])).
% 6.28/1.16  fof(f32,plain,(
% 6.28/1.16    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : ((X1 = X2 | (k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.28/1.16    inference(ennf_transformation,[],[f7])).
% 6.28/1.16  fof(f7,axiom,(
% 6.28/1.16    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) => X1 = X2)))))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).
% 6.28/1.16  fof(f2132,plain,(
% 6.28/1.16    ~sP0(sK3) | k6_partfun1(sK2) = sK4),
% 6.28/1.16    inference(resolution,[],[f2131,f82])).
% 6.28/1.16  fof(f82,plain,(
% 6.28/1.16    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 6.28/1.16    inference(cnf_transformation,[],[f16])).
% 6.28/1.16  fof(f16,axiom,(
% 6.28/1.16    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 6.28/1.16  fof(f2131,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP0(sK3) | k6_partfun1(sK2) = sK4) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f2130,f946])).
% 6.28/1.16  fof(f946,plain,(
% 6.28/1.16    sK3 = k5_relat_1(k6_partfun1(sK2),sK3)),
% 6.28/1.16    inference(resolution,[],[f941,f73])).
% 6.28/1.16  fof(f941,plain,(
% 6.28/1.16    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | sK3 = k5_relat_1(k6_partfun1(sK2),sK3)) )),
% 6.28/1.16    inference(resolution,[],[f937,f73])).
% 6.28/1.16  fof(f937,plain,(
% 6.28/1.16    ( ! [X26,X25] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X26))) | sK3 = k5_relat_1(k6_partfun1(sK2),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))) )),
% 6.28/1.16    inference(resolution,[],[f928,f71])).
% 6.28/1.16  fof(f928,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(k6_partfun1(sK2),X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))) )),
% 6.28/1.16    inference(resolution,[],[f794,f82])).
% 6.28/1.16  fof(f794,plain,(
% 6.28/1.16    ( ! [X6,X4,X5,X3] : (~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k5_relat_1(k6_partfun1(sK2),X3) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X6)))) )),
% 6.28/1.16    inference(resolution,[],[f787,f277])).
% 6.28/1.16  fof(f277,plain,(
% 6.28/1.16    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(k6_partfun1(X3)) | ~v1_funct_1(X0) | ~m1_subset_1(k6_partfun1(X3),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(k6_partfun1(X3),X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))) )),
% 6.28/1.16    inference(resolution,[],[f240,f206])).
% 6.28/1.16  fof(f206,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (~m1_subset_1(k5_relat_1(k6_partfun1(X1),X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(k6_partfun1(X1),X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 6.28/1.16    inference(duplicate_literal_removal,[],[f204])).
% 6.28/1.16  fof(f204,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(k6_partfun1(X1),X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(k5_relat_1(k6_partfun1(X1),X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 6.28/1.16    inference(resolution,[],[f202,f123])).
% 6.28/1.16  fof(f123,plain,(
% 6.28/1.16    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.28/1.16    inference(cnf_transformation,[],[f70])).
% 6.28/1.16  fof(f202,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f201,f82])).
% 6.28/1.16  fof(f201,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 6.28/1.16    inference(duplicate_literal_removal,[],[f198])).
% 6.28/1.16  fof(f198,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 6.28/1.16    inference(superposition,[],[f118,f128])).
% 6.28/1.16  fof(f128,plain,(
% 6.28/1.16    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.28/1.16    inference(cnf_transformation,[],[f54])).
% 6.28/1.16  fof(f54,plain,(
% 6.28/1.16    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.28/1.16    inference(flattening,[],[f53])).
% 6.28/1.16  fof(f53,plain,(
% 6.28/1.16    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.28/1.16    inference(ennf_transformation,[],[f13])).
% 6.28/1.16  fof(f13,axiom,(
% 6.28/1.16    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 6.28/1.16  fof(f118,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.28/1.16    inference(cnf_transformation,[],[f44])).
% 6.28/1.16  fof(f44,plain,(
% 6.28/1.16    ! [X0,X1,X2] : ((r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.28/1.16    inference(ennf_transformation,[],[f19])).
% 6.28/1.16  fof(f19,axiom,(
% 6.28/1.16    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).
% 6.28/1.16  fof(f240,plain,(
% 6.28/1.16    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.28/1.16    inference(duplicate_literal_removal,[],[f239])).
% 6.28/1.16  fof(f239,plain,(
% 6.28/1.16    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.28/1.16    inference(superposition,[],[f127,f125])).
% 6.28/1.16  fof(f125,plain,(
% 6.28/1.16    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f50])).
% 6.28/1.16  fof(f50,plain,(
% 6.28/1.16    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.28/1.16    inference(flattening,[],[f49])).
% 6.28/1.16  fof(f49,plain,(
% 6.28/1.16    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.28/1.16    inference(ennf_transformation,[],[f17])).
% 6.28/1.16  fof(f17,axiom,(
% 6.28/1.16    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 6.28/1.16  fof(f127,plain,(
% 6.28/1.16    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f52])).
% 6.28/1.16  fof(f52,plain,(
% 6.28/1.16    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.28/1.16    inference(flattening,[],[f51])).
% 6.28/1.16  fof(f51,plain,(
% 6.28/1.16    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.28/1.16    inference(ennf_transformation,[],[f15])).
% 6.28/1.16  fof(f15,axiom,(
% 6.28/1.16    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 6.28/1.16  fof(f787,plain,(
% 6.28/1.16    v1_funct_1(k6_partfun1(sK2))),
% 6.28/1.16    inference(resolution,[],[f784,f73])).
% 6.28/1.16  fof(f784,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k6_partfun1(sK2))) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f783,f165])).
% 6.28/1.16  fof(f165,plain,(
% 6.28/1.16    sK2 = k1_relat_1(sK3)),
% 6.28/1.16    inference(subsumption_resolution,[],[f163,f73])).
% 6.28/1.16  fof(f163,plain,(
% 6.28/1.16    sK2 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.28/1.16    inference(superposition,[],[f160,f114])).
% 6.28/1.16  fof(f114,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.28/1.16    inference(cnf_transformation,[],[f41])).
% 6.28/1.16  fof(f41,plain,(
% 6.28/1.16    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.28/1.16    inference(ennf_transformation,[],[f11])).
% 6.28/1.16  fof(f11,axiom,(
% 6.28/1.16    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 6.28/1.16  fof(f160,plain,(
% 6.28/1.16    sK2 = k1_relset_1(sK2,sK2,sK3)),
% 6.28/1.16    inference(subsumption_resolution,[],[f159,f71])).
% 6.28/1.16  fof(f159,plain,(
% 6.28/1.16    sK2 = k1_relset_1(sK2,sK2,sK3) | ~v1_funct_1(sK3)),
% 6.28/1.16    inference(subsumption_resolution,[],[f157,f73])).
% 6.28/1.16  fof(f157,plain,(
% 6.28/1.16    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK2 = k1_relset_1(sK2,sK2,sK3) | ~v1_funct_1(sK3)),
% 6.28/1.16    inference(resolution,[],[f110,f72])).
% 6.28/1.16  fof(f72,plain,(
% 6.28/1.16    v1_funct_2(sK3,sK2,sK2)),
% 6.28/1.16    inference(cnf_transformation,[],[f60])).
% 6.28/1.16  fof(f110,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_1(X1)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f40])).
% 6.28/1.16  fof(f40,plain,(
% 6.28/1.16    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 6.28/1.16    inference(flattening,[],[f39])).
% 6.28/1.16  fof(f39,plain,(
% 6.28/1.16    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 6.28/1.16    inference(ennf_transformation,[],[f22])).
% 6.28/1.16  fof(f22,axiom,(
% 6.28/1.16    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 6.28/1.16  fof(f783,plain,(
% 6.28/1.16    ( ! [X0,X1] : (v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 != k1_relat_1(sK3)) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f782,f71])).
% 6.28/1.16  fof(f782,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~v1_funct_1(sK3) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 != k1_relat_1(sK3)) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f780,f78])).
% 6.28/1.16  fof(f780,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~v2_funct_1(sK3) | ~v1_funct_1(sK3) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 != k1_relat_1(sK3)) )),
% 6.28/1.16    inference(superposition,[],[f750,f256])).
% 6.28/1.16  fof(f256,plain,(
% 6.28/1.16    sK3 = k5_relat_1(sK4,sK3)),
% 6.28/1.16    inference(subsumption_resolution,[],[f255,f74])).
% 6.28/1.16  fof(f74,plain,(
% 6.28/1.16    v1_funct_1(sK4)),
% 6.28/1.16    inference(cnf_transformation,[],[f60])).
% 6.28/1.16  fof(f255,plain,(
% 6.28/1.16    sK3 = k5_relat_1(sK4,sK3) | ~v1_funct_1(sK4)),
% 6.28/1.16    inference(subsumption_resolution,[],[f254,f76])).
% 6.28/1.16  fof(f254,plain,(
% 6.28/1.16    sK3 = k5_relat_1(sK4,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 6.28/1.16    inference(subsumption_resolution,[],[f253,f71])).
% 6.28/1.16  fof(f253,plain,(
% 6.28/1.16    sK3 = k5_relat_1(sK4,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 6.28/1.16    inference(subsumption_resolution,[],[f249,f73])).
% 6.28/1.16  fof(f249,plain,(
% 6.28/1.16    sK3 = k5_relat_1(sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 6.28/1.16    inference(superposition,[],[f244,f125])).
% 6.28/1.16  fof(f244,plain,(
% 6.28/1.16    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 6.28/1.16    inference(subsumption_resolution,[],[f243,f74])).
% 6.28/1.16  fof(f243,plain,(
% 6.28/1.16    ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 6.28/1.16    inference(subsumption_resolution,[],[f242,f76])).
% 6.28/1.16  fof(f242,plain,(
% 6.28/1.16    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 6.28/1.16    inference(subsumption_resolution,[],[f241,f71])).
% 6.28/1.16  fof(f241,plain,(
% 6.28/1.16    ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 6.28/1.16    inference(subsumption_resolution,[],[f238,f73])).
% 6.28/1.16  fof(f238,plain,(
% 6.28/1.16    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 6.28/1.16    inference(resolution,[],[f127,f184])).
% 6.28/1.16  fof(f184,plain,(
% 6.28/1.16    ~m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 6.28/1.16    inference(subsumption_resolution,[],[f177,f73])).
% 6.28/1.16  fof(f177,plain,(
% 6.28/1.16    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.28/1.16    inference(resolution,[],[f123,f77])).
% 6.28/1.16  fof(f77,plain,(
% 6.28/1.16    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)),
% 6.28/1.16    inference(cnf_transformation,[],[f60])).
% 6.28/1.16  fof(f750,plain,(
% 6.28/1.16    ( ! [X4,X5,X3] : (~v2_funct_1(k5_relat_1(sK4,X3)) | ~v1_funct_1(X3) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | sK2 != k1_relat_1(X3)) )),
% 6.28/1.16    inference(resolution,[],[f735,f107])).
% 6.28/1.16  fof(f735,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v2_funct_1(k5_relat_1(sK4,X0)) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_relat_1(X0) != sK2) )),
% 6.28/1.16    inference(resolution,[],[f732,f85])).
% 6.28/1.16  fof(f732,plain,(
% 6.28/1.16    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(X1) != sK2 | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(sK4,X1)) | v1_funct_1(k6_partfun1(sK2))) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f731,f107])).
% 6.28/1.16  fof(f731,plain,(
% 6.28/1.16    ( ! [X1] : (~v2_funct_1(k5_relat_1(sK4,X1)) | k1_relat_1(X1) != sK2 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | v1_funct_1(k6_partfun1(sK2)) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))) )),
% 6.28/1.16    inference(resolution,[],[f686,f76])).
% 6.28/1.16  fof(f686,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(X1)) | ~v2_funct_1(k5_relat_1(sK4,X0)) | k1_relat_1(X0) != sK2 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k6_partfun1(sK2)) | ~v1_relat_1(X1)) )),
% 6.28/1.16    inference(resolution,[],[f633,f85])).
% 6.28/1.16  fof(f633,plain,(
% 6.28/1.16    ( ! [X1] : (~v1_relat_1(sK4) | v1_funct_1(k6_partfun1(sK2)) | ~v2_funct_1(k5_relat_1(sK4,X1)) | k1_relat_1(X1) != sK2 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.28/1.16    inference(forward_demodulation,[],[f632,f307])).
% 6.28/1.16  fof(f307,plain,(
% 6.28/1.16    sK2 = k2_relat_1(sK4)),
% 6.28/1.16    inference(subsumption_resolution,[],[f302,f107])).
% 6.28/1.16  fof(f302,plain,(
% 6.28/1.16    ~v1_relat_1(k2_zfmisc_1(sK2,sK2)) | sK2 = k2_relat_1(sK4)),
% 6.28/1.16    inference(resolution,[],[f299,f73])).
% 6.28/1.16  fof(f299,plain,(
% 6.28/1.16    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_relat_1(X1) | sK2 = k2_relat_1(sK4)) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f295,f107])).
% 6.28/1.16  fof(f295,plain,(
% 6.28/1.16    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_relat_1(X1) | sK2 = k2_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))) )),
% 6.28/1.16    inference(resolution,[],[f291,f76])).
% 6.28/1.16  fof(f291,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_relat_1(X1) | sK2 = k2_relat_1(sK4) | ~v1_relat_1(X0)) )),
% 6.28/1.16    inference(resolution,[],[f287,f76])).
% 6.28/1.16  fof(f287,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) | ~v1_relat_1(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_relat_1(X1) | sK2 = k2_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(X0))) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f285,f85])).
% 6.28/1.16  fof(f285,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(sK4) | sK2 = k2_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))) )),
% 6.28/1.16    inference(resolution,[],[f276,f151])).
% 6.28/1.16  fof(f151,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_relat_1(X0)) | ~v1_relat_1(X0) | k2_relat_1(X0) = X2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 6.28/1.16    inference(resolution,[],[f142,f113])).
% 6.28/1.16  fof(f113,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f69])).
% 6.28/1.16  fof(f69,plain,(
% 6.28/1.16    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.28/1.16    inference(flattening,[],[f68])).
% 6.28/1.16  fof(f68,plain,(
% 6.28/1.16    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.28/1.16    inference(nnf_transformation,[],[f1])).
% 6.28/1.16  fof(f1,axiom,(
% 6.28/1.16    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.28/1.16  fof(f142,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X0),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_relat_1(X0)) )),
% 6.28/1.16    inference(resolution,[],[f117,f108])).
% 6.28/1.16  fof(f108,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f67])).
% 6.28/1.16  fof(f67,plain,(
% 6.28/1.16    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.28/1.16    inference(nnf_transformation,[],[f38])).
% 6.28/1.16  fof(f38,plain,(
% 6.28/1.16    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.28/1.16    inference(ennf_transformation,[],[f3])).
% 6.28/1.16  fof(f3,axiom,(
% 6.28/1.16    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 6.28/1.16  fof(f117,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.28/1.16    inference(cnf_transformation,[],[f43])).
% 6.28/1.16  fof(f43,plain,(
% 6.28/1.16    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.28/1.16    inference(ennf_transformation,[],[f10])).
% 6.28/1.16  fof(f10,axiom,(
% 6.28/1.16    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 6.28/1.16  fof(f276,plain,(
% 6.28/1.16    ( ! [X0,X1] : (r1_tarski(sK2,k2_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_relat_1(X1)) )),
% 6.28/1.16    inference(resolution,[],[f275,f85])).
% 6.28/1.16  fof(f275,plain,(
% 6.28/1.16    ( ! [X0] : (~v1_relat_1(sK3) | r1_tarski(sK2,k2_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 6.28/1.16    inference(resolution,[],[f269,f85])).
% 6.28/1.16  fof(f269,plain,(
% 6.28/1.16    ~v1_relat_1(sK4) | r1_tarski(sK2,k2_relat_1(sK4)) | ~v1_relat_1(sK3)),
% 6.28/1.16    inference(forward_demodulation,[],[f268,f165])).
% 6.28/1.16  fof(f268,plain,(
% 6.28/1.16    r1_tarski(k1_relat_1(sK3),k2_relat_1(sK4)) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3)),
% 6.28/1.16    inference(subsumption_resolution,[],[f267,f71])).
% 6.28/1.16  fof(f267,plain,(
% 6.28/1.16    r1_tarski(k1_relat_1(sK3),k2_relat_1(sK4)) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 6.28/1.16    inference(subsumption_resolution,[],[f266,f74])).
% 6.28/1.16  fof(f266,plain,(
% 6.28/1.16    r1_tarski(k1_relat_1(sK3),k2_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 6.28/1.16    inference(subsumption_resolution,[],[f265,f78])).
% 6.28/1.16  fof(f265,plain,(
% 6.28/1.16    ~v2_funct_1(sK3) | r1_tarski(k1_relat_1(sK3),k2_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 6.28/1.16    inference(trivial_inequality_removal,[],[f264])).
% 6.28/1.16  fof(f264,plain,(
% 6.28/1.16    k2_relat_1(sK3) != k2_relat_1(sK3) | ~v2_funct_1(sK3) | r1_tarski(k1_relat_1(sK3),k2_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 6.28/1.16    inference(superposition,[],[f106,f256])).
% 6.28/1.16  fof(f106,plain,(
% 6.28/1.16    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) | ~v2_funct_1(X0) | r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f37])).
% 6.28/1.16  fof(f37,plain,(
% 6.28/1.16    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.28/1.16    inference(flattening,[],[f36])).
% 6.28/1.16  fof(f36,plain,(
% 6.28/1.16    ! [X0] : (! [X1] : ((r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | (~v2_funct_1(X0) | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.28/1.16    inference(ennf_transformation,[],[f8])).
% 6.28/1.16  fof(f8,axiom,(
% 6.28/1.16    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X0) & k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)) => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)))))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).
% 6.28/1.16  fof(f632,plain,(
% 6.28/1.16    ( ! [X1] : (v1_funct_1(k6_partfun1(sK2)) | k1_relat_1(X1) != k2_relat_1(sK4) | ~v2_funct_1(k5_relat_1(sK4,X1)) | ~v1_relat_1(sK4) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f628,f74])).
% 6.28/1.16  fof(f628,plain,(
% 6.28/1.16    ( ! [X1] : (v1_funct_1(k6_partfun1(sK2)) | k1_relat_1(X1) != k2_relat_1(sK4) | ~v2_funct_1(k5_relat_1(sK4,X1)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.28/1.16    inference(resolution,[],[f619,f104])).
% 6.28/1.16  fof(f104,plain,(
% 6.28/1.16    ( ! [X0,X1] : (v2_funct_1(X1) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f35])).
% 6.28/1.16  fof(f35,plain,(
% 6.28/1.16    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.28/1.16    inference(flattening,[],[f34])).
% 6.28/1.16  fof(f34,plain,(
% 6.28/1.16    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.28/1.16    inference(ennf_transformation,[],[f6])).
% 6.28/1.16  fof(f6,axiom,(
% 6.28/1.16    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 6.28/1.16  fof(f619,plain,(
% 6.28/1.16    ~v2_funct_1(sK4) | v1_funct_1(k6_partfun1(sK2))),
% 6.28/1.16    inference(resolution,[],[f617,f76])).
% 6.28/1.16  fof(f617,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(sK4) | v1_funct_1(k6_partfun1(sK2))) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f616,f76])).
% 6.28/1.16  fof(f616,plain,(
% 6.28/1.16    ( ! [X0,X1] : (v1_funct_1(k6_partfun1(sK2)) | ~v2_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f615,f307])).
% 6.28/1.16  fof(f615,plain,(
% 6.28/1.16    ( ! [X0,X1] : (sK2 != k2_relat_1(sK4) | v1_funct_1(k6_partfun1(sK2)) | ~v2_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))) )),
% 6.28/1.16    inference(superposition,[],[f614,f115])).
% 6.28/1.16  fof(f115,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.28/1.16    inference(cnf_transformation,[],[f42])).
% 6.28/1.16  fof(f42,plain,(
% 6.28/1.16    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.28/1.16    inference(ennf_transformation,[],[f12])).
% 6.28/1.16  fof(f12,axiom,(
% 6.28/1.16    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 6.28/1.16  fof(f614,plain,(
% 6.28/1.16    ( ! [X2,X3] : (sK2 != k2_relset_1(sK2,sK2,sK4) | v1_funct_1(k6_partfun1(sK2)) | ~v2_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f607,f75])).
% 6.28/1.16  fof(f75,plain,(
% 6.28/1.16    v1_funct_2(sK4,sK2,sK2)),
% 6.28/1.16    inference(cnf_transformation,[],[f60])).
% 6.28/1.16  fof(f607,plain,(
% 6.28/1.16    ( ! [X2,X3] : (v1_funct_1(k6_partfun1(sK2)) | sK2 != k2_relset_1(sK2,sK2,sK4) | ~v2_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 6.28/1.16    inference(resolution,[],[f605,f76])).
% 6.28/1.16  fof(f605,plain,(
% 6.28/1.16    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | v1_funct_1(k6_partfun1(sK2)) | k2_relset_1(X4,X5,sK4) != X5 | ~v2_funct_1(sK4) | ~v1_funct_2(sK4,X4,X5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f604,f107])).
% 6.28/1.16  fof(f604,plain,(
% 6.28/1.16    ( ! [X6,X4,X7,X5] : (~v2_funct_1(sK4) | v1_funct_1(k6_partfun1(sK2)) | k2_relset_1(X4,X5,sK4) != X5 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(sK4,X4,X5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))) )),
% 6.28/1.16    inference(resolution,[],[f589,f76])).
% 6.28/1.16  fof(f589,plain,(
% 6.28/1.16    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(X4)) | ~v2_funct_1(sK4) | v1_funct_1(k6_partfun1(sK2)) | k2_relset_1(X2,X3,sK4) != X3 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK4,X2,X3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_relat_1(X4)) )),
% 6.28/1.16    inference(resolution,[],[f559,f85])).
% 6.28/1.16  fof(f559,plain,(
% 6.28/1.16    ( ! [X12,X10,X13,X11] : (~v1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~v2_funct_1(sK4) | v1_funct_1(k6_partfun1(sK2)) | k2_relset_1(X12,X13,sK4) != X13 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | ~v1_funct_2(sK4,X12,X13)) )),
% 6.28/1.16    inference(forward_demodulation,[],[f558,f307])).
% 6.28/1.16  fof(f558,plain,(
% 6.28/1.16    ( ! [X12,X10,X13,X11] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | v1_funct_1(k6_partfun1(k2_relat_1(sK4))) | ~v2_funct_1(sK4) | ~v1_relat_1(sK4) | k2_relset_1(X12,X13,sK4) != X13 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | ~v1_funct_2(sK4,X12,X13)) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f551,f74])).
% 6.28/1.16  fof(f551,plain,(
% 6.28/1.16    ( ! [X12,X10,X13,X11] : (~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | v1_funct_1(k6_partfun1(k2_relat_1(sK4))) | ~v2_funct_1(sK4) | ~v1_relat_1(sK4) | k2_relset_1(X12,X13,sK4) != X13 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | ~v1_funct_2(sK4,X12,X13)) )),
% 6.28/1.16    inference(resolution,[],[f545,f354])).
% 6.28/1.16  fof(f354,plain,(
% 6.28/1.16    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_1(k6_partfun1(k2_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | k2_relset_1(X5,X6,X0) != X6 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6)) )),
% 6.28/1.16    inference(duplicate_literal_removal,[],[f353])).
% 6.28/1.16  fof(f353,plain,(
% 6.28/1.16    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_funct_1(k6_partfun1(k2_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | k2_relset_1(X5,X6,X0) != X6 | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6) | ~v1_funct_1(X0)) )),
% 6.28/1.16    inference(resolution,[],[f274,f120])).
% 6.28/1.16  fof(f120,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f46])).
% 6.28/1.16  fof(f46,plain,(
% 6.28/1.16    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.28/1.16    inference(flattening,[],[f45])).
% 6.28/1.16  fof(f45,plain,(
% 6.28/1.16    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.28/1.16    inference(ennf_transformation,[],[f20])).
% 6.28/1.16  fof(f20,axiom,(
% 6.28/1.16    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 6.28/1.16  fof(f274,plain,(
% 6.28/1.16    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(k2_funct_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_funct_1(k6_partfun1(k2_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.28/1.16    inference(duplicate_literal_removal,[],[f270])).
% 6.28/1.16  fof(f270,plain,(
% 6.28/1.16    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k6_partfun1(k2_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.28/1.16    inference(superposition,[],[f228,f131])).
% 6.28/1.16  fof(f131,plain,(
% 6.28/1.16    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.28/1.16    inference(definition_unfolding,[],[f90,f80])).
% 6.28/1.16  fof(f80,plain,(
% 6.28/1.16    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f18])).
% 6.28/1.16  fof(f18,axiom,(
% 6.28/1.16    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 6.28/1.16  fof(f90,plain,(
% 6.28/1.16    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f31])).
% 6.28/1.16  fof(f31,plain,(
% 6.28/1.16    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.28/1.16    inference(flattening,[],[f30])).
% 6.28/1.16  fof(f30,plain,(
% 6.28/1.16    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.28/1.16    inference(ennf_transformation,[],[f9])).
% 6.28/1.16  fof(f9,axiom,(
% 6.28/1.16    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 6.28/1.16  fof(f228,plain,(
% 6.28/1.16    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.28/1.16    inference(duplicate_literal_removal,[],[f227])).
% 6.28/1.16  fof(f227,plain,(
% 6.28/1.16    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.28/1.16    inference(superposition,[],[f126,f125])).
% 6.28/1.16  fof(f126,plain,(
% 6.28/1.16    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f52])).
% 6.28/1.16  fof(f545,plain,(
% 6.28/1.16    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))),
% 6.28/1.16    inference(resolution,[],[f542,f73])).
% 6.28/1.16  fof(f542,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f541,f165])).
% 6.28/1.16  fof(f541,plain,(
% 6.28/1.16    ( ! [X0,X1] : (m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 != k1_relat_1(sK3)) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f540,f71])).
% 6.28/1.16  fof(f540,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~v1_funct_1(sK3) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 != k1_relat_1(sK3)) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f538,f78])).
% 6.28/1.16  fof(f538,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~v2_funct_1(sK3) | ~v1_funct_1(sK3) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 != k1_relat_1(sK3)) )),
% 6.28/1.16    inference(superposition,[],[f530,f256])).
% 6.28/1.16  fof(f530,plain,(
% 6.28/1.16    ( ! [X4,X5,X3] : (~v2_funct_1(k5_relat_1(sK4,X3)) | ~v1_funct_1(X3) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | sK2 != k1_relat_1(X3)) )),
% 6.28/1.16    inference(resolution,[],[f512,f107])).
% 6.28/1.16  fof(f512,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v2_funct_1(k5_relat_1(sK4,X0)) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_relat_1(X0) != sK2) )),
% 6.28/1.16    inference(resolution,[],[f510,f85])).
% 6.28/1.16  fof(f510,plain,(
% 6.28/1.16    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(X1) != sK2 | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(sK4,X1)) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f509,f107])).
% 6.28/1.16  fof(f509,plain,(
% 6.28/1.16    ( ! [X1] : (~v2_funct_1(k5_relat_1(sK4,X1)) | k1_relat_1(X1) != sK2 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))) )),
% 6.28/1.16    inference(resolution,[],[f498,f76])).
% 6.28/1.16  fof(f498,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(X1)) | ~v2_funct_1(k5_relat_1(sK4,X0)) | k1_relat_1(X0) != sK2 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~v1_relat_1(X1)) )),
% 6.28/1.16    inference(resolution,[],[f469,f85])).
% 6.28/1.16  fof(f469,plain,(
% 6.28/1.16    ( ! [X1] : (~v1_relat_1(sK4) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~v2_funct_1(k5_relat_1(sK4,X1)) | k1_relat_1(X1) != sK2 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.28/1.16    inference(forward_demodulation,[],[f468,f307])).
% 6.28/1.16  fof(f468,plain,(
% 6.28/1.16    ( ! [X1] : (m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | k1_relat_1(X1) != k2_relat_1(sK4) | ~v2_funct_1(k5_relat_1(sK4,X1)) | ~v1_relat_1(sK4) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f464,f74])).
% 6.28/1.16  fof(f464,plain,(
% 6.28/1.16    ( ! [X1] : (m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | k1_relat_1(X1) != k2_relat_1(sK4) | ~v2_funct_1(k5_relat_1(sK4,X1)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.28/1.16    inference(resolution,[],[f456,f104])).
% 6.28/1.16  fof(f456,plain,(
% 6.28/1.16    ~v2_funct_1(sK4) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4)))))),
% 6.28/1.16    inference(subsumption_resolution,[],[f455,f76])).
% 6.28/1.16  fof(f455,plain,(
% 6.28/1.16    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~v2_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.28/1.16    inference(subsumption_resolution,[],[f454,f307])).
% 6.28/1.16  fof(f454,plain,(
% 6.28/1.16    sK2 != k2_relat_1(sK4) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~v2_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.28/1.16    inference(superposition,[],[f453,f115])).
% 6.28/1.16  fof(f453,plain,(
% 6.28/1.16    sK2 != k2_relset_1(sK2,sK2,sK4) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~v2_funct_1(sK4)),
% 6.28/1.16    inference(subsumption_resolution,[],[f446,f75])).
% 6.28/1.16  fof(f446,plain,(
% 6.28/1.16    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | sK2 != k2_relset_1(sK2,sK2,sK4) | ~v2_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK2)),
% 6.28/1.16    inference(resolution,[],[f440,f76])).
% 6.28/1.16  fof(f440,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | k2_relset_1(X0,X1,sK4) != X1 | ~v2_funct_1(sK4) | ~v1_funct_2(sK4,X0,X1)) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f439,f76])).
% 6.28/1.16  fof(f439,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~v2_funct_1(sK4) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | k2_relset_1(X0,X1,sK4) != X1 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK4,X0,X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f438,f307])).
% 6.28/1.16  fof(f438,plain,(
% 6.28/1.16    ( ! [X0,X1] : (sK2 != k2_relat_1(sK4) | ~v2_funct_1(sK4) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | k2_relset_1(X0,X1,sK4) != X1 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK4,X0,X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))) )),
% 6.28/1.16    inference(superposition,[],[f433,f115])).
% 6.28/1.16  fof(f433,plain,(
% 6.28/1.16    ( ! [X2,X3] : (sK2 != k2_relset_1(sK2,sK2,sK4) | ~v2_funct_1(sK4) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | k2_relset_1(X2,X3,sK4) != X3 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK4,X2,X3)) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f426,f75])).
% 6.28/1.16  fof(f426,plain,(
% 6.28/1.16    ( ! [X2,X3] : (sK2 != k2_relset_1(sK2,sK2,sK4) | ~v2_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK2) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | k2_relset_1(X2,X3,sK4) != X3 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK4,X2,X3)) )),
% 6.28/1.16    inference(resolution,[],[f424,f76])).
% 6.28/1.16  fof(f424,plain,(
% 6.28/1.16    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK4) != X1 | ~v2_funct_1(sK4) | ~v1_funct_2(sK4,X0,X1) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | k2_relset_1(X3,X2,sK4) != X2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK4,X3,X2)) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f423,f74])).
% 6.28/1.16  fof(f423,plain,(
% 6.28/1.16    ( ! [X2,X0,X3,X1] : (~v2_funct_1(sK4) | k2_relset_1(X0,X1,sK4) != X1 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK4,X0,X1) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | k2_relset_1(X3,X2,sK4) != X2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK4,X3,X2) | ~v1_funct_1(sK4)) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f422,f107])).
% 6.28/1.16  fof(f422,plain,(
% 6.28/1.16    ( ! [X2,X0,X3,X1] : (~v2_funct_1(sK4) | k2_relset_1(X0,X1,sK4) != X1 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK4,X0,X1) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~v1_relat_1(k2_zfmisc_1(X2,X3)) | k2_relset_1(X3,X2,sK4) != X2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK4,X3,X2) | ~v1_funct_1(sK4)) )),
% 6.28/1.16    inference(duplicate_literal_removal,[],[f420])).
% 6.28/1.16  fof(f420,plain,(
% 6.28/1.16    ( ! [X2,X0,X3,X1] : (~v2_funct_1(sK4) | k2_relset_1(X0,X1,sK4) != X1 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK4,X0,X1) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~v1_relat_1(k2_zfmisc_1(X2,X3)) | k2_relset_1(X3,X2,sK4) != X2 | ~v2_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK4,X3,X2) | ~v1_funct_1(sK4)) )),
% 6.28/1.16    inference(resolution,[],[f415,f122])).
% 6.28/1.16  fof(f122,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f46])).
% 6.28/1.16  fof(f415,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(X2)) | ~v2_funct_1(sK4) | k2_relset_1(X0,X1,sK4) != X1 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK4,X0,X1) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~v1_relat_1(X2)) )),
% 6.28/1.16    inference(resolution,[],[f414,f85])).
% 6.28/1.16  fof(f414,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~v1_relat_1(k2_funct_1(sK4)) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~v2_funct_1(sK4) | k2_relset_1(X0,X1,sK4) != X1 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK4,X0,X1)) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f413,f74])).
% 6.28/1.16  fof(f413,plain,(
% 6.28/1.16    ( ! [X0,X1] : (m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~v1_relat_1(k2_funct_1(sK4)) | ~v2_funct_1(sK4) | k2_relset_1(X0,X1,sK4) != X1 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK4,X0,X1) | ~v1_funct_1(sK4)) )),
% 6.28/1.16    inference(duplicate_literal_removal,[],[f412])).
% 6.28/1.16  fof(f412,plain,(
% 6.28/1.16    ( ! [X0,X1] : (m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~v1_relat_1(k2_funct_1(sK4)) | ~v2_funct_1(sK4) | k2_relset_1(X0,X1,sK4) != X1 | ~v2_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK4,X0,X1) | ~v1_funct_1(sK4)) )),
% 6.28/1.16    inference(resolution,[],[f406,f120])).
% 6.28/1.16  fof(f406,plain,(
% 6.28/1.16    ~v1_funct_1(k2_funct_1(sK4)) | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK4))))) | ~v1_relat_1(k2_funct_1(sK4)) | ~v2_funct_1(sK4)),
% 6.28/1.16    inference(superposition,[],[f88,f403])).
% 6.28/1.16  fof(f403,plain,(
% 6.28/1.16    sK2 = k1_relat_1(k2_funct_1(sK4)) | ~v2_funct_1(sK4)),
% 6.28/1.16    inference(subsumption_resolution,[],[f402,f74])).
% 6.28/1.16  fof(f402,plain,(
% 6.28/1.16    ~v1_funct_1(sK4) | sK2 = k1_relat_1(k2_funct_1(sK4)) | ~v2_funct_1(sK4)),
% 6.28/1.16    inference(subsumption_resolution,[],[f401,f307])).
% 6.28/1.16  fof(f401,plain,(
% 6.28/1.16    sK2 != k2_relat_1(sK4) | ~v1_funct_1(sK4) | sK2 = k1_relat_1(k2_funct_1(sK4)) | ~v2_funct_1(sK4)),
% 6.28/1.16    inference(subsumption_resolution,[],[f396,f76])).
% 6.28/1.16  fof(f396,plain,(
% 6.28/1.16    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK2 != k2_relat_1(sK4) | ~v1_funct_1(sK4) | sK2 = k1_relat_1(k2_funct_1(sK4)) | ~v2_funct_1(sK4)),
% 6.28/1.16    inference(resolution,[],[f390,f75])).
% 6.28/1.16  fof(f390,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_relat_1(X1) != X0 | ~v1_funct_1(X1) | k1_relat_1(k2_funct_1(X1)) = X0 | ~v2_funct_1(X1)) )),
% 6.28/1.16    inference(duplicate_literal_removal,[],[f389])).
% 6.28/1.16  fof(f389,plain,(
% 6.28/1.16    ( ! [X0,X1] : (k2_relat_1(X1) != X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k2_relat_1(X1) != X0 | k1_relat_1(k2_funct_1(X1)) = X0 | ~v2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 6.28/1.16    inference(superposition,[],[f384,f115])).
% 6.28/1.16  fof(f384,plain,(
% 6.28/1.16    ( ! [X0,X1] : (k2_relset_1(X1,X1,X0) != X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v1_funct_2(X0,X1,X1) | ~v1_funct_1(X0) | k2_relat_1(X0) != X1 | k1_relat_1(k2_funct_1(X0)) = X1 | ~v2_funct_1(X0)) )),
% 6.28/1.16    inference(duplicate_literal_removal,[],[f383])).
% 6.28/1.16  fof(f383,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v1_funct_2(X0,X1,X1) | ~v1_funct_1(X0) | k2_relat_1(X0) != X1 | k1_relat_1(k2_funct_1(X0)) = X1 | k2_relset_1(X1,X1,X0) != X1 | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v1_funct_2(X0,X1,X1) | ~v1_funct_1(X0)) )),
% 6.28/1.16    inference(resolution,[],[f349,f122])).
% 6.28/1.16  fof(f349,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k2_relat_1(X1) != X0 | k1_relat_1(k2_funct_1(X1)) = X0) )),
% 6.28/1.16    inference(superposition,[],[f290,f114])).
% 6.28/1.16  fof(f290,plain,(
% 6.28/1.16    ( ! [X0,X1] : (k1_relset_1(X0,X0,k2_funct_1(X1)) = X0 | ~v2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k2_relat_1(X1) != X0) )),
% 6.28/1.16    inference(duplicate_literal_removal,[],[f289])).
% 6.28/1.16  fof(f289,plain,(
% 6.28/1.16    ( ! [X0,X1] : (k2_relat_1(X1) != X0 | ~v2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k1_relset_1(X0,X0,k2_funct_1(X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 6.28/1.16    inference(superposition,[],[f216,f115])).
% 6.28/1.16  fof(f216,plain,(
% 6.28/1.16    ( ! [X0,X1] : (k2_relset_1(X0,X0,X1) != X0 | ~v2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k1_relset_1(X0,X0,k2_funct_1(X1)) = X0) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f215,f122])).
% 6.28/1.16  fof(f215,plain,(
% 6.28/1.16    ( ! [X0,X1] : (k2_relset_1(X0,X0,X1) != X0 | ~v2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | ~m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,k2_funct_1(X1)) = X0) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f214,f120])).
% 6.28/1.16  fof(f214,plain,(
% 6.28/1.16    ( ! [X0,X1] : (k2_relset_1(X0,X0,X1) != X0 | ~v2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | ~m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,k2_funct_1(X1)) = X0 | ~v1_funct_1(k2_funct_1(X1))) )),
% 6.28/1.16    inference(resolution,[],[f121,f110])).
% 6.28/1.16  fof(f121,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f46])).
% 6.28/1.16  fof(f88,plain,(
% 6.28/1.16    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f29])).
% 6.28/1.16  fof(f29,plain,(
% 6.28/1.16    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.28/1.16    inference(flattening,[],[f28])).
% 6.28/1.16  fof(f28,plain,(
% 6.28/1.16    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.28/1.16    inference(ennf_transformation,[],[f21])).
% 6.28/1.16  fof(f21,axiom,(
% 6.28/1.16    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 6.28/1.16  fof(f2130,plain,(
% 6.28/1.16    ( ! [X0,X1] : (k6_partfun1(sK2) = sK4 | ~sP0(sK3) | ~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK3 != k5_relat_1(k6_partfun1(sK2),sK3)) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f2129,f133])).
% 6.28/1.16  fof(f133,plain,(
% 6.28/1.16    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.28/1.16    inference(equality_resolution,[],[f112])).
% 6.28/1.16  fof(f112,plain,(
% 6.28/1.16    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 6.28/1.16    inference(cnf_transformation,[],[f69])).
% 6.28/1.16  fof(f2129,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~r1_tarski(sK2,sK2) | k6_partfun1(sK2) = sK4 | ~sP0(sK3) | ~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK3 != k5_relat_1(k6_partfun1(sK2),sK3)) )),
% 6.28/1.16    inference(trivial_inequality_removal,[],[f2126])).
% 6.28/1.16  fof(f2126,plain,(
% 6.28/1.16    ( ! [X0,X1] : (~r1_tarski(sK2,sK2) | sK2 != sK2 | k6_partfun1(sK2) = sK4 | ~sP0(sK3) | ~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK3 != k5_relat_1(k6_partfun1(sK2),sK3)) )),
% 6.28/1.16    inference(resolution,[],[f2117,f787])).
% 6.28/1.16  fof(f2117,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (~v1_funct_1(k6_partfun1(X0)) | ~r1_tarski(X0,sK2) | sK2 != X0 | k6_partfun1(X0) = sK4 | ~sP0(sK3) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | sK3 != k5_relat_1(k6_partfun1(X0),sK3)) )),
% 6.28/1.16    inference(forward_demodulation,[],[f2115,f130])).
% 6.28/1.16  fof(f130,plain,(
% 6.28/1.16    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 6.28/1.16    inference(definition_unfolding,[],[f83,f80])).
% 6.28/1.16  fof(f83,plain,(
% 6.28/1.16    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 6.28/1.16    inference(cnf_transformation,[],[f5])).
% 6.28/1.16  fof(f5,axiom,(
% 6.28/1.16    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 6.28/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 6.28/1.16  fof(f2115,plain,(
% 6.28/1.16    ( ! [X2,X0,X1] : (~r1_tarski(X0,sK2) | ~v1_funct_1(k6_partfun1(X0)) | k6_partfun1(X0) = sK4 | ~sP0(sK3) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | sK3 != k5_relat_1(k6_partfun1(X0),sK3) | sK2 != k1_relat_1(k6_partfun1(X0))) )),
% 6.28/1.16    inference(superposition,[],[f2112,f129])).
% 6.28/1.16  fof(f129,plain,(
% 6.28/1.16    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 6.28/1.16    inference(definition_unfolding,[],[f84,f80])).
% 6.28/1.16  fof(f84,plain,(
% 6.28/1.16    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 6.28/1.16    inference(cnf_transformation,[],[f5])).
% 6.28/1.16  fof(f2112,plain,(
% 6.28/1.16    ( ! [X4,X5,X3] : (~r1_tarski(k2_relat_1(X3),sK2) | ~v1_funct_1(X3) | sK4 = X3 | ~sP0(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | sK3 != k5_relat_1(X3,sK3) | sK2 != k1_relat_1(X3)) )),
% 6.28/1.16    inference(resolution,[],[f658,f76])).
% 6.28/1.16  fof(f658,plain,(
% 6.28/1.16    ( ! [X6,X10,X8,X7,X9] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | sK2 != k1_relat_1(X6) | ~v1_funct_1(X6) | sK4 = X6 | ~sP0(sK3) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | sK3 != k5_relat_1(X6,sK3) | ~r1_tarski(k2_relat_1(X6),sK2)) )),
% 6.28/1.16    inference(forward_demodulation,[],[f657,f256])).
% 6.28/1.16  fof(f657,plain,(
% 6.28/1.16    ( ! [X6,X10,X8,X7,X9] : (sK2 != k1_relat_1(X6) | ~v1_funct_1(X6) | sK4 = X6 | ~sP0(sK3) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | k5_relat_1(sK4,sK3) != k5_relat_1(X6,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | ~r1_tarski(k2_relat_1(X6),sK2)) )),
% 6.28/1.16    inference(forward_demodulation,[],[f656,f172])).
% 6.28/1.16  fof(f172,plain,(
% 6.28/1.16    sK2 = k1_relat_1(sK4)),
% 6.28/1.16    inference(subsumption_resolution,[],[f170,f76])).
% 6.28/1.16  fof(f170,plain,(
% 6.28/1.16    sK2 = k1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.28/1.16    inference(superposition,[],[f162,f114])).
% 6.28/1.16  fof(f162,plain,(
% 6.28/1.16    sK2 = k1_relset_1(sK2,sK2,sK4)),
% 6.28/1.16    inference(subsumption_resolution,[],[f161,f74])).
% 6.28/1.16  fof(f161,plain,(
% 6.28/1.16    sK2 = k1_relset_1(sK2,sK2,sK4) | ~v1_funct_1(sK4)),
% 6.28/1.16    inference(subsumption_resolution,[],[f158,f76])).
% 6.28/1.16  fof(f158,plain,(
% 6.28/1.16    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK2 = k1_relset_1(sK2,sK2,sK4) | ~v1_funct_1(sK4)),
% 6.28/1.16    inference(resolution,[],[f110,f75])).
% 6.28/1.16  fof(f656,plain,(
% 6.28/1.16    ( ! [X6,X10,X8,X7,X9] : (~v1_funct_1(X6) | sK4 = X6 | k1_relat_1(sK4) != k1_relat_1(X6) | ~sP0(sK3) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | k5_relat_1(sK4,sK3) != k5_relat_1(X6,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | ~r1_tarski(k2_relat_1(X6),sK2)) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f655,f74])).
% 6.28/1.16  fof(f655,plain,(
% 6.28/1.16    ( ! [X6,X10,X8,X7,X9] : (~v1_funct_1(X6) | sK4 = X6 | ~v1_funct_1(sK4) | k1_relat_1(sK4) != k1_relat_1(X6) | ~sP0(sK3) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | k5_relat_1(sK4,sK3) != k5_relat_1(X6,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | ~r1_tarski(k2_relat_1(X6),sK2)) )),
% 6.28/1.16    inference(subsumption_resolution,[],[f653,f133])).
% 6.28/1.16  fof(f653,plain,(
% 6.28/1.16    ( ! [X6,X10,X8,X7,X9] : (~r1_tarski(sK2,sK2) | ~v1_funct_1(X6) | sK4 = X6 | ~v1_funct_1(sK4) | k1_relat_1(sK4) != k1_relat_1(X6) | ~sP0(sK3) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | k5_relat_1(sK4,sK3) != k5_relat_1(X6,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | ~r1_tarski(k2_relat_1(X6),sK2)) )),
% 6.28/1.16    inference(superposition,[],[f524,f307])).
% 6.28/1.16  fof(f524,plain,(
% 6.28/1.16    ( ! [X14,X17,X15,X13,X18,X16] : (~r1_tarski(k2_relat_1(X13),sK2) | ~v1_funct_1(X14) | X13 = X14 | ~v1_funct_1(X13) | k1_relat_1(X14) != k1_relat_1(X13) | ~sP0(sK3) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) | k5_relat_1(X14,sK3) != k5_relat_1(X13,sK3) | ~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) | ~r1_tarski(k2_relat_1(X14),sK2)) )),
% 6.28/1.16    inference(superposition,[],[f442,f165])).
% 6.28/1.16  fof(f442,plain,(
% 6.28/1.16    ( ! [X12,X10,X8,X7,X13,X11,X9] : (~r1_tarski(k2_relat_1(X7),k1_relat_1(X8)) | ~v1_funct_1(X9) | X7 = X9 | ~v1_funct_1(X7) | k1_relat_1(X9) != k1_relat_1(X7) | ~sP0(X8) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | k5_relat_1(X9,X8) != k5_relat_1(X7,X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | ~r1_tarski(k2_relat_1(X9),k1_relat_1(X8))) )),
% 6.28/1.16    inference(resolution,[],[f368,f107])).
% 6.28/1.16  fof(f368,plain,(
% 6.28/1.16    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_relat_1(X5) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) | ~v1_funct_1(X0) | X0 = X2 | ~v1_funct_1(X2) | k1_relat_1(X0) != k1_relat_1(X2) | ~sP0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k5_relat_1(X0,X1) != k5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X5)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) )),
% 6.28/1.16    inference(resolution,[],[f329,f85])).
% 6.28/1.16  fof(f329,plain,(
% 6.28/1.16    ( ! [X6,X8,X7,X5,X9] : (~v1_relat_1(X5) | ~r1_tarski(k2_relat_1(X6),k1_relat_1(X7)) | ~r1_tarski(k2_relat_1(X5),k1_relat_1(X7)) | ~v1_funct_1(X6) | X5 = X6 | ~v1_funct_1(X5) | k1_relat_1(X5) != k1_relat_1(X6) | ~sP0(X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | k5_relat_1(X5,X7) != k5_relat_1(X6,X7)) )),
% 6.28/1.16    inference(resolution,[],[f258,f107])).
% 6.28/1.16  fof(f258,plain,(
% 6.28/1.16    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X3) | k1_relat_1(X0) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X2) | X0 = X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~sP0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k5_relat_1(X0,X1) != k5_relat_1(X2,X1)) )),
% 6.28/1.16    inference(resolution,[],[f93,f85])).
% 6.28/1.16  fof(f93,plain,(
% 6.28/1.16    ( ! [X4,X0,X3] : (~v1_relat_1(X4) | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | X3 = X4 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~sP0(X0)) )),
% 6.28/1.16    inference(cnf_transformation,[],[f66])).
% 6.28/1.16  fof(f66,plain,(
% 6.28/1.16    ! [X0] : ((sP0(X0) | ((sK5(X0) != sK6(X0) & k5_relat_1(sK5(X0),X0) = k5_relat_1(sK6(X0),X0) & k1_relat_1(sK5(X0)) = k1_relat_1(sK6(X0)) & r1_tarski(k2_relat_1(sK6(X0)),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0)) & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0))) & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0)))) & (! [X3] : (! [X4] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~sP0(X0)))),
% 6.28/1.16    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f63,f65,f64])).
% 6.28/1.16  fof(f64,plain,(
% 6.28/1.16    ! [X0] : (? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (sK5(X0) != X2 & k5_relat_1(X2,X0) = k5_relat_1(sK5(X0),X0) & k1_relat_1(X2) = k1_relat_1(sK5(X0)) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0))))),
% 6.28/1.16    introduced(choice_axiom,[])).
% 6.28/1.16  fof(f65,plain,(
% 6.28/1.16    ! [X0] : (? [X2] : (sK5(X0) != X2 & k5_relat_1(X2,X0) = k5_relat_1(sK5(X0),X0) & k1_relat_1(X2) = k1_relat_1(sK5(X0)) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) => (sK5(X0) != sK6(X0) & k5_relat_1(sK5(X0),X0) = k5_relat_1(sK6(X0),X0) & k1_relat_1(sK5(X0)) = k1_relat_1(sK6(X0)) & r1_tarski(k2_relat_1(sK6(X0)),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0)) & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0))))),
% 6.28/1.16    introduced(choice_axiom,[])).
% 6.28/1.16  fof(f63,plain,(
% 6.28/1.16    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))) & (! [X3] : (! [X4] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~sP0(X0)))),
% 6.28/1.16    inference(rectify,[],[f62])).
% 6.28/1.16  fof(f62,plain,(
% 6.28/1.16    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))) & (! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~sP0(X0)))),
% 6.28/1.16    inference(nnf_transformation,[],[f55])).
% 6.28/1.16  fof(f79,plain,(
% 6.28/1.16    ~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))),
% 6.28/1.16    inference(cnf_transformation,[],[f60])).
% 6.28/1.16  fof(f76,plain,(
% 6.28/1.16    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.28/1.16    inference(cnf_transformation,[],[f60])).
% 6.28/1.16  % SZS output end Proof for theBenchmark
% 6.28/1.16  % (18405)------------------------------
% 6.28/1.16  % (18405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.28/1.16  % (18405)Termination reason: Refutation
% 6.28/1.16  
% 6.28/1.16  % (18405)Memory used [KB]: 8827
% 6.28/1.16  % (18405)Time elapsed: 0.727 s
% 6.28/1.16  % (18405)------------------------------
% 6.28/1.16  % (18405)------------------------------
% 6.28/1.18  % (18382)Success in time 0.824 s
%------------------------------------------------------------------------------
