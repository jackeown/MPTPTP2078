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
% DateTime   : Thu Dec  3 13:01:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 318 expanded)
%              Number of leaves         :   26 ( 101 expanded)
%              Depth                    :   21
%              Number of atoms          :  517 (2151 expanded)
%              Number of equality atoms :   52 (  64 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f113,f159,f174,f213,f220,f278])).

fof(f278,plain,
    ( spl4_2
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | spl4_2
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f276,f126])).

fof(f126,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f68,f51])).

fof(f51,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f68,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f276,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f275,f93])).

fof(f93,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f275,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f274,f132])).

fof(f132,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f71,f51])).

fof(f71,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f274,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_8 ),
    inference(superposition,[],[f82,f273])).

fof(f273,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f142,f272])).

fof(f272,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f271,f49])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f271,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f270,f50])).

fof(f50,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f270,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f269,f51])).

fof(f269,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f268,f46])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f268,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f267,f47])).

fof(f47,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f267,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f266,f48])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f266,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f265,f140])).

fof(f140,plain,(
    ! [X0] : r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) ),
    inference(resolution,[],[f85,f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f56,f55])).

fof(f55,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f265,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_8 ),
    inference(superposition,[],[f72,f158])).

fof(f158,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl4_8
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f72,plain,(
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
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f142,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f69,f51])).

fof(f69,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f82,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
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

fof(f220,plain,
    ( spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f216,f89])).

fof(f89,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f216,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f112,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v2_funct_1(X0) ) ),
    inference(global_subsumption,[],[f59,f60,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f112,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f213,plain,
    ( spl4_1
    | spl4_3
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl4_1
    | spl4_3
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f201,f54])).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f201,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_1
    | spl4_3
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f123,f194])).

fof(f194,plain,
    ( k1_xboole_0 = sK0
    | spl4_1
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f193,f46])).

fof(f193,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2)
    | spl4_1
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f192,f47])).

fof(f192,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f191,f48])).

fof(f191,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f190,f49])).

fof(f190,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f189,f50])).

fof(f189,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f188,f51])).

fof(f188,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f187,f89])).

fof(f187,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f186,f80])).

fof(f80,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f58,f55])).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f186,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_8 ),
    inference(superposition,[],[f73,f158])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f123,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_3 ),
    inference(resolution,[],[f108,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f108,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_3
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f174,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f172,f46])).

fof(f172,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f171,f48])).

fof(f171,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f170,f49])).

fof(f170,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f160,f51])).

fof(f160,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_7 ),
    inference(resolution,[],[f78,f154])).

fof(f154,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl4_7
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f78,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f159,plain,
    ( ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f149,f156,f152])).

fof(f149,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f146,f52])).

fof(f52,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f146,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f75,f79])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f113,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f102,f110,f106])).

fof(f102,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f61,f48])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f94,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f53,f91,f87])).

fof(f53,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:10:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (23862)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.50  % (23857)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (23857)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (23871)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.51  % (23854)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (23864)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.51  % (23861)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (23870)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.52  % (23872)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.52  % (23855)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (23856)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (23851)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (23853)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.30/0.53  % SZS output start Proof for theBenchmark
% 1.30/0.53  fof(f279,plain,(
% 1.30/0.53    $false),
% 1.30/0.53    inference(avatar_sat_refutation,[],[f94,f113,f159,f174,f213,f220,f278])).
% 1.30/0.53  fof(f278,plain,(
% 1.30/0.53    spl4_2 | ~spl4_8),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f277])).
% 1.30/0.53  fof(f277,plain,(
% 1.30/0.53    $false | (spl4_2 | ~spl4_8)),
% 1.30/0.53    inference(subsumption_resolution,[],[f276,f126])).
% 1.30/0.53  fof(f126,plain,(
% 1.30/0.53    v1_relat_1(sK3)),
% 1.30/0.53    inference(resolution,[],[f68,f51])).
% 1.30/0.53  fof(f51,plain,(
% 1.30/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.30/0.53    inference(cnf_transformation,[],[f43])).
% 1.30/0.53  fof(f43,plain,(
% 1.30/0.53    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f42,f41])).
% 1.30/0.53  fof(f41,plain,(
% 1.30/0.53    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f42,plain,(
% 1.30/0.53    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f21,plain,(
% 1.30/0.53    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.30/0.53    inference(flattening,[],[f20])).
% 1.30/0.53  fof(f20,plain,(
% 1.30/0.53    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.30/0.53    inference(ennf_transformation,[],[f19])).
% 1.30/0.53  fof(f19,negated_conjecture,(
% 1.30/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.30/0.53    inference(negated_conjecture,[],[f18])).
% 1.30/0.53  fof(f18,conjecture,(
% 1.30/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.30/0.53  fof(f68,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f30])).
% 1.30/0.53  fof(f30,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.53    inference(ennf_transformation,[],[f8])).
% 1.30/0.53  fof(f8,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.30/0.53  fof(f276,plain,(
% 1.30/0.53    ~v1_relat_1(sK3) | (spl4_2 | ~spl4_8)),
% 1.30/0.53    inference(subsumption_resolution,[],[f275,f93])).
% 1.30/0.53  fof(f93,plain,(
% 1.30/0.53    ~v2_funct_2(sK3,sK0) | spl4_2),
% 1.30/0.53    inference(avatar_component_clause,[],[f91])).
% 1.30/0.53  fof(f91,plain,(
% 1.30/0.53    spl4_2 <=> v2_funct_2(sK3,sK0)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.30/0.53  fof(f275,plain,(
% 1.30/0.53    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_8),
% 1.30/0.53    inference(subsumption_resolution,[],[f274,f132])).
% 1.30/0.53  fof(f132,plain,(
% 1.30/0.53    v5_relat_1(sK3,sK0)),
% 1.30/0.53    inference(resolution,[],[f71,f51])).
% 1.30/0.53  fof(f71,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f32])).
% 1.30/0.53  fof(f32,plain,(
% 1.30/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.53    inference(ennf_transformation,[],[f9])).
% 1.30/0.53  fof(f9,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.30/0.53  fof(f274,plain,(
% 1.30/0.53    ~v5_relat_1(sK3,sK0) | v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_8),
% 1.30/0.53    inference(superposition,[],[f82,f273])).
% 1.30/0.53  fof(f273,plain,(
% 1.30/0.53    sK0 = k2_relat_1(sK3) | ~spl4_8),
% 1.30/0.53    inference(backward_demodulation,[],[f142,f272])).
% 1.30/0.53  fof(f272,plain,(
% 1.30/0.53    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_8),
% 1.30/0.53    inference(subsumption_resolution,[],[f271,f49])).
% 1.30/0.53  fof(f49,plain,(
% 1.30/0.53    v1_funct_1(sK3)),
% 1.30/0.53    inference(cnf_transformation,[],[f43])).
% 1.30/0.53  fof(f271,plain,(
% 1.30/0.53    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | ~spl4_8),
% 1.30/0.53    inference(subsumption_resolution,[],[f270,f50])).
% 1.30/0.53  fof(f50,plain,(
% 1.30/0.53    v1_funct_2(sK3,sK1,sK0)),
% 1.30/0.53    inference(cnf_transformation,[],[f43])).
% 1.30/0.53  fof(f270,plain,(
% 1.30/0.53    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_8),
% 1.30/0.53    inference(subsumption_resolution,[],[f269,f51])).
% 1.30/0.53  fof(f269,plain,(
% 1.30/0.53    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_8),
% 1.30/0.53    inference(subsumption_resolution,[],[f268,f46])).
% 1.30/0.53  fof(f46,plain,(
% 1.30/0.53    v1_funct_1(sK2)),
% 1.30/0.53    inference(cnf_transformation,[],[f43])).
% 1.30/0.53  fof(f268,plain,(
% 1.30/0.53    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_8),
% 1.30/0.53    inference(subsumption_resolution,[],[f267,f47])).
% 1.30/0.53  fof(f47,plain,(
% 1.30/0.53    v1_funct_2(sK2,sK0,sK1)),
% 1.30/0.53    inference(cnf_transformation,[],[f43])).
% 1.30/0.53  fof(f267,plain,(
% 1.30/0.53    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_8),
% 1.30/0.53    inference(subsumption_resolution,[],[f266,f48])).
% 1.30/0.53  fof(f48,plain,(
% 1.30/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.30/0.53    inference(cnf_transformation,[],[f43])).
% 1.30/0.53  fof(f266,plain,(
% 1.30/0.53    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_8),
% 1.30/0.53    inference(subsumption_resolution,[],[f265,f140])).
% 1.30/0.53  fof(f140,plain,(
% 1.30/0.53    ( ! [X0] : (r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))) )),
% 1.30/0.53    inference(resolution,[],[f85,f79])).
% 1.30/0.53  fof(f79,plain,(
% 1.30/0.53    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.30/0.53    inference(definition_unfolding,[],[f56,f55])).
% 1.30/0.53  fof(f55,plain,(
% 1.30/0.53    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f15])).
% 1.30/0.53  fof(f15,axiom,(
% 1.30/0.53    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.30/0.53  fof(f56,plain,(
% 1.30/0.53    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f12])).
% 1.30/0.53  fof(f12,axiom,(
% 1.30/0.53    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.30/0.53  fof(f85,plain,(
% 1.30/0.53    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.30/0.53    inference(duplicate_literal_removal,[],[f84])).
% 1.30/0.53  fof(f84,plain,(
% 1.30/0.53    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.30/0.53    inference(equality_resolution,[],[f76])).
% 1.30/0.53  fof(f76,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f45])).
% 1.30/0.53  fof(f45,plain,(
% 1.30/0.53    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.53    inference(nnf_transformation,[],[f38])).
% 1.30/0.53  fof(f38,plain,(
% 1.30/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.53    inference(flattening,[],[f37])).
% 1.30/0.53  fof(f37,plain,(
% 1.30/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.30/0.53    inference(ennf_transformation,[],[f11])).
% 1.30/0.53  fof(f11,axiom,(
% 1.30/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.30/0.53  fof(f265,plain,(
% 1.30/0.53    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_8),
% 1.30/0.53    inference(superposition,[],[f72,f158])).
% 1.30/0.53  fof(f158,plain,(
% 1.30/0.53    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl4_8),
% 1.30/0.53    inference(avatar_component_clause,[],[f156])).
% 1.30/0.53  fof(f156,plain,(
% 1.30/0.53    spl4_8 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.30/0.53  fof(f72,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f34])).
% 1.30/0.53  fof(f34,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.30/0.53    inference(flattening,[],[f33])).
% 1.30/0.53  fof(f33,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.30/0.53    inference(ennf_transformation,[],[f16])).
% 1.30/0.53  fof(f16,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.30/0.53  fof(f142,plain,(
% 1.30/0.53    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 1.30/0.53    inference(resolution,[],[f69,f51])).
% 1.30/0.53  fof(f69,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f31])).
% 1.30/0.53  fof(f31,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.53    inference(ennf_transformation,[],[f10])).
% 1.30/0.53  fof(f10,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.30/0.53  fof(f82,plain,(
% 1.30/0.53    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.30/0.53    inference(equality_resolution,[],[f67])).
% 1.30/0.53  fof(f67,plain,(
% 1.30/0.53    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f44])).
% 1.30/0.53  fof(f44,plain,(
% 1.30/0.53    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.30/0.53    inference(nnf_transformation,[],[f29])).
% 1.30/0.53  fof(f29,plain,(
% 1.30/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.30/0.53    inference(flattening,[],[f28])).
% 1.30/0.53  fof(f28,plain,(
% 1.30/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.30/0.53    inference(ennf_transformation,[],[f13])).
% 1.30/0.53  fof(f13,axiom,(
% 1.30/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.30/0.53  fof(f220,plain,(
% 1.30/0.53    spl4_1 | ~spl4_4),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f219])).
% 1.30/0.53  fof(f219,plain,(
% 1.30/0.53    $false | (spl4_1 | ~spl4_4)),
% 1.30/0.53    inference(subsumption_resolution,[],[f216,f89])).
% 1.30/0.53  fof(f89,plain,(
% 1.30/0.53    ~v2_funct_1(sK2) | spl4_1),
% 1.30/0.53    inference(avatar_component_clause,[],[f87])).
% 1.30/0.53  fof(f87,plain,(
% 1.30/0.53    spl4_1 <=> v2_funct_1(sK2)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.30/0.53  fof(f216,plain,(
% 1.30/0.53    v2_funct_1(sK2) | ~spl4_4),
% 1.30/0.53    inference(resolution,[],[f112,f95])).
% 1.30/0.53  fof(f95,plain,(
% 1.30/0.53    ( ! [X0] : (~v1_xboole_0(X0) | v2_funct_1(X0)) )),
% 1.30/0.53    inference(global_subsumption,[],[f59,f60,f64])).
% 1.30/0.53  fof(f64,plain,(
% 1.30/0.53    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f26])).
% 1.30/0.53  fof(f26,plain,(
% 1.30/0.53    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.30/0.53    inference(flattening,[],[f25])).
% 1.30/0.53  fof(f25,plain,(
% 1.30/0.53    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 1.30/0.53    inference(ennf_transformation,[],[f6])).
% 1.30/0.53  fof(f6,axiom,(
% 1.30/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0) & v1_xboole_0(X0)) => (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).
% 1.30/0.53  fof(f60,plain,(
% 1.30/0.53    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f23])).
% 1.30/0.53  fof(f23,plain,(
% 1.30/0.53    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 1.30/0.53    inference(ennf_transformation,[],[f5])).
% 1.30/0.53  fof(f5,axiom,(
% 1.30/0.53    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 1.30/0.53  fof(f59,plain,(
% 1.30/0.53    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f22])).
% 1.30/0.53  fof(f22,plain,(
% 1.30/0.53    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.30/0.53    inference(ennf_transformation,[],[f4])).
% 1.30/0.53  fof(f4,axiom,(
% 1.30/0.53    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.30/0.53  fof(f112,plain,(
% 1.30/0.53    v1_xboole_0(sK2) | ~spl4_4),
% 1.30/0.53    inference(avatar_component_clause,[],[f110])).
% 1.30/0.53  fof(f110,plain,(
% 1.30/0.53    spl4_4 <=> v1_xboole_0(sK2)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.30/0.53  fof(f213,plain,(
% 1.30/0.53    spl4_1 | spl4_3 | ~spl4_8),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f212])).
% 1.30/0.53  fof(f212,plain,(
% 1.30/0.53    $false | (spl4_1 | spl4_3 | ~spl4_8)),
% 1.30/0.53    inference(subsumption_resolution,[],[f201,f54])).
% 1.30/0.53  fof(f54,plain,(
% 1.30/0.53    v1_xboole_0(k1_xboole_0)),
% 1.30/0.53    inference(cnf_transformation,[],[f1])).
% 1.30/0.53  fof(f1,axiom,(
% 1.30/0.53    v1_xboole_0(k1_xboole_0)),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.30/0.53  fof(f201,plain,(
% 1.30/0.53    ~v1_xboole_0(k1_xboole_0) | (spl4_1 | spl4_3 | ~spl4_8)),
% 1.30/0.53    inference(backward_demodulation,[],[f123,f194])).
% 1.30/0.53  fof(f194,plain,(
% 1.30/0.53    k1_xboole_0 = sK0 | (spl4_1 | ~spl4_8)),
% 1.30/0.53    inference(subsumption_resolution,[],[f193,f46])).
% 1.30/0.53  fof(f193,plain,(
% 1.30/0.53    k1_xboole_0 = sK0 | ~v1_funct_1(sK2) | (spl4_1 | ~spl4_8)),
% 1.30/0.53    inference(subsumption_resolution,[],[f192,f47])).
% 1.30/0.53  fof(f192,plain,(
% 1.30/0.53    k1_xboole_0 = sK0 | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_1 | ~spl4_8)),
% 1.30/0.53    inference(subsumption_resolution,[],[f191,f48])).
% 1.30/0.53  fof(f191,plain,(
% 1.30/0.53    k1_xboole_0 = sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_1 | ~spl4_8)),
% 1.30/0.53    inference(subsumption_resolution,[],[f190,f49])).
% 1.30/0.53  fof(f190,plain,(
% 1.30/0.53    k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_1 | ~spl4_8)),
% 1.30/0.53    inference(subsumption_resolution,[],[f189,f50])).
% 1.30/0.53  fof(f189,plain,(
% 1.30/0.53    k1_xboole_0 = sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_1 | ~spl4_8)),
% 1.30/0.53    inference(subsumption_resolution,[],[f188,f51])).
% 1.30/0.53  fof(f188,plain,(
% 1.30/0.53    k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_1 | ~spl4_8)),
% 1.30/0.53    inference(subsumption_resolution,[],[f187,f89])).
% 1.30/0.53  fof(f187,plain,(
% 1.30/0.53    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_8),
% 1.30/0.53    inference(subsumption_resolution,[],[f186,f80])).
% 1.30/0.53  fof(f80,plain,(
% 1.30/0.53    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.30/0.53    inference(definition_unfolding,[],[f58,f55])).
% 1.30/0.53  fof(f58,plain,(
% 1.30/0.53    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f7])).
% 1.30/0.53  fof(f7,axiom,(
% 1.30/0.53    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.30/0.53  fof(f186,plain,(
% 1.30/0.53    ~v2_funct_1(k6_partfun1(sK0)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_8),
% 1.30/0.53    inference(superposition,[],[f73,f158])).
% 1.30/0.53  fof(f73,plain,(
% 1.30/0.53    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f36])).
% 1.30/0.53  fof(f36,plain,(
% 1.30/0.53    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.30/0.53    inference(flattening,[],[f35])).
% 1.30/0.53  fof(f35,plain,(
% 1.30/0.53    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.30/0.53    inference(ennf_transformation,[],[f17])).
% 1.30/0.53  fof(f17,axiom,(
% 1.30/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 1.30/0.53  fof(f123,plain,(
% 1.30/0.53    ~v1_xboole_0(sK0) | spl4_3),
% 1.30/0.53    inference(resolution,[],[f108,f65])).
% 1.30/0.53  fof(f65,plain,(
% 1.30/0.53    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f27])).
% 1.30/0.53  fof(f27,plain,(
% 1.30/0.53    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 1.30/0.53    inference(ennf_transformation,[],[f2])).
% 1.30/0.53  fof(f2,axiom,(
% 1.30/0.53    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 1.30/0.53  fof(f108,plain,(
% 1.30/0.53    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl4_3),
% 1.30/0.53    inference(avatar_component_clause,[],[f106])).
% 1.30/0.53  fof(f106,plain,(
% 1.30/0.53    spl4_3 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.30/0.53  fof(f174,plain,(
% 1.30/0.53    spl4_7),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f173])).
% 1.30/0.53  fof(f173,plain,(
% 1.30/0.53    $false | spl4_7),
% 1.30/0.53    inference(subsumption_resolution,[],[f172,f46])).
% 1.30/0.53  fof(f172,plain,(
% 1.30/0.53    ~v1_funct_1(sK2) | spl4_7),
% 1.30/0.53    inference(subsumption_resolution,[],[f171,f48])).
% 1.30/0.53  fof(f171,plain,(
% 1.30/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_7),
% 1.30/0.53    inference(subsumption_resolution,[],[f170,f49])).
% 1.30/0.53  fof(f170,plain,(
% 1.30/0.53    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_7),
% 1.30/0.53    inference(subsumption_resolution,[],[f160,f51])).
% 1.30/0.53  fof(f160,plain,(
% 1.30/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_7),
% 1.30/0.53    inference(resolution,[],[f78,f154])).
% 1.30/0.53  fof(f154,plain,(
% 1.30/0.53    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_7),
% 1.30/0.53    inference(avatar_component_clause,[],[f152])).
% 1.30/0.53  fof(f152,plain,(
% 1.30/0.53    spl4_7 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.30/0.53  fof(f78,plain,(
% 1.30/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f40])).
% 1.30/0.53  fof(f40,plain,(
% 1.30/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.30/0.53    inference(flattening,[],[f39])).
% 1.30/0.53  fof(f39,plain,(
% 1.30/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.30/0.53    inference(ennf_transformation,[],[f14])).
% 1.30/0.53  fof(f14,axiom,(
% 1.30/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.30/0.53  fof(f159,plain,(
% 1.30/0.53    ~spl4_7 | spl4_8),
% 1.30/0.53    inference(avatar_split_clause,[],[f149,f156,f152])).
% 1.30/0.53  fof(f149,plain,(
% 1.30/0.53    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.30/0.53    inference(resolution,[],[f146,f52])).
% 1.30/0.53  fof(f52,plain,(
% 1.30/0.53    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.30/0.53    inference(cnf_transformation,[],[f43])).
% 1.30/0.53  fof(f146,plain,(
% 1.30/0.53    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.30/0.53    inference(resolution,[],[f75,f79])).
% 1.30/0.53  fof(f75,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f45])).
% 1.30/0.53  fof(f113,plain,(
% 1.30/0.53    ~spl4_3 | spl4_4),
% 1.30/0.53    inference(avatar_split_clause,[],[f102,f110,f106])).
% 1.30/0.53  fof(f102,plain,(
% 1.30/0.53    v1_xboole_0(sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.30/0.53    inference(resolution,[],[f61,f48])).
% 1.30/0.53  fof(f61,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f24])).
% 1.30/0.53  fof(f24,plain,(
% 1.30/0.53    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.30/0.53    inference(ennf_transformation,[],[f3])).
% 1.30/0.53  fof(f3,axiom,(
% 1.30/0.53    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.30/0.53  fof(f94,plain,(
% 1.30/0.53    ~spl4_1 | ~spl4_2),
% 1.30/0.53    inference(avatar_split_clause,[],[f53,f91,f87])).
% 1.30/0.53  fof(f53,plain,(
% 1.30/0.53    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.30/0.53    inference(cnf_transformation,[],[f43])).
% 1.30/0.53  % SZS output end Proof for theBenchmark
% 1.30/0.53  % (23857)------------------------------
% 1.30/0.53  % (23857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (23857)Termination reason: Refutation
% 1.30/0.53  
% 1.30/0.53  % (23857)Memory used [KB]: 10874
% 1.30/0.53  % (23857)Time elapsed: 0.100 s
% 1.30/0.53  % (23857)------------------------------
% 1.30/0.53  % (23857)------------------------------
% 1.30/0.54  % (23879)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.30/0.54  % (23850)Success in time 0.175 s
%------------------------------------------------------------------------------
