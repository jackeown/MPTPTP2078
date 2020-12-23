%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 989 expanded)
%              Number of leaves         :   19 ( 310 expanded)
%              Depth                    :   21
%              Number of atoms          :  555 (8282 expanded)
%              Number of equality atoms :  112 ( 226 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f743,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f145,f249,f265,f376,f381,f742])).

fof(f742,plain,
    ( ~ spl3_5
    | spl3_11
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f741])).

fof(f741,plain,
    ( $false
    | ~ spl3_5
    | spl3_11
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f740,f243])).

fof(f243,plain,
    ( sK2 != k2_funct_1(sK1)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl3_11
  <=> sK2 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f740,plain,
    ( sK2 = k2_funct_1(sK1)
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f735,f474])).

fof(f474,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(sK1))
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f473,f248])).

fof(f248,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl3_12
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f473,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f472,f318])).

fof(f318,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f283,f59])).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f283,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f223,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f223,plain,(
    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f222,f188])).

fof(f188,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f187,f47])).

fof(f47,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f41,f40])).

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

fof(f41,plain,
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f187,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f186,f48])).

fof(f48,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f186,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f182,f49])).

fof(f49,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f182,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f62,f50])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f222,plain,(
    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f221,f47])).

fof(f221,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f220,f48])).

fof(f220,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f216,f49])).

fof(f216,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f66,f50])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f472,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f470,f273])).

fof(f273,plain,(
    v5_relat_1(k2_funct_1(sK1),sK0) ),
    inference(resolution,[],[f223,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f470,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ v5_relat_1(k2_funct_1(sK1),sK0)
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f292,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f292,plain,(
    v2_funct_2(k2_funct_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f291,f260])).

fof(f260,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(superposition,[],[f164,f188])).

fof(f164,plain,(
    v1_funct_1(k2_funct_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f163,f47])).

fof(f163,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f162,f48])).

fof(f162,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f158,f49])).

fof(f158,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f63,f50])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_1(k2_funct_2(X0,X1))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f291,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | v2_funct_2(k2_funct_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f276,f211])).

fof(f211,plain,(
    v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    inference(forward_demodulation,[],[f210,f188])).

fof(f210,plain,(
    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) ),
    inference(subsumption_resolution,[],[f209,f47])).

fof(f209,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f208,f48])).

fof(f208,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f204,f49])).

fof(f204,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f65,f50])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f276,plain,
    ( ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | v2_funct_2(k2_funct_1(sK1),sK0) ),
    inference(resolution,[],[f223,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f735,plain,
    ( k1_xboole_0 != k2_relat_1(k2_funct_1(sK1))
    | sK2 = k2_funct_1(sK1)
    | ~ spl3_5 ),
    inference(resolution,[],[f140,f318])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 != k2_relat_1(X0)
        | sK2 = X0 )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_5
  <=> ! [X0] :
        ( k1_xboole_0 != k2_relat_1(X0)
        | ~ v1_relat_1(X0)
        | sK2 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f381,plain,
    ( spl3_6
    | ~ spl3_10
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | spl3_6
    | ~ spl3_10
    | spl3_11 ),
    inference(global_subsumption,[],[f236,f243,f239,f369])).

fof(f369,plain,
    ( k1_xboole_0 != sK0
    | spl3_6 ),
    inference(superposition,[],[f144,f255])).

fof(f255,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f254,f91])).

fof(f91,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f89,f59])).

fof(f89,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f58,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f254,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f253,f97])).

fof(f97,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f72,f54])).

fof(f253,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f153,f60])).

fof(f153,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f152,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f152,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f147,f53])).

fof(f53,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f147,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0) ),
    inference(resolution,[],[f77,f54])).

fof(f144,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl3_6
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f239,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl3_10
  <=> sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f236,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f235,f47])).

fof(f235,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f234,f48])).

fof(f234,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f233,f50])).

fof(f233,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f232,f51])).

fof(f232,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f231,f52])).

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f231,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f230,f54])).

fof(f230,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f229,f115])).

fof(f115,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f114,f47])).

fof(f114,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f110,f49])).

fof(f110,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f76,f50])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f229,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f78,f55])).

fof(f55,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f37])).

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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f376,plain,(
    ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f374,f103])).

fof(f103,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f85,f54])).

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
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f374,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_11 ),
    inference(superposition,[],[f261,f244])).

fof(f244,plain,
    ( sK2 = k2_funct_1(sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f242])).

fof(f261,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(superposition,[],[f56,f188])).

fof(f56,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f265,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | spl3_10 ),
    inference(subsumption_resolution,[],[f263,f252])).

fof(f252,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f251,f90])).

fof(f90,plain,(
    v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f88,f59])).

fof(f88,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f58,f50])).

fof(f251,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f250,f96])).

fof(f96,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f72,f50])).

fof(f250,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f151,f60])).

fof(f151,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f150,f47])).

fof(f150,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f146,f49])).

fof(f146,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(resolution,[],[f77,f50])).

fof(f263,plain,
    ( sK0 != k2_relat_1(sK1)
    | spl3_10 ),
    inference(superposition,[],[f240,f106])).

fof(f106,plain,(
    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(resolution,[],[f71,f50])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f240,plain,
    ( sK0 != k2_relset_1(sK0,sK0,sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f238])).

fof(f249,plain,
    ( ~ spl3_10
    | spl3_11
    | spl3_12 ),
    inference(avatar_split_clause,[],[f236,f246,f242,f238])).

fof(f145,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f137,f142,f139])).

fof(f137,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(sK2)
      | k1_xboole_0 != k2_relat_1(X0)
      | sK2 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f91,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 != k2_relat_1(X1)
      | k1_xboole_0 != k2_relat_1(X0)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k1_xboole_0 != k2_relat_1(X1)
          | k1_xboole_0 != k2_relat_1(X0)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k1_xboole_0 != k2_relat_1(X1)
          | k1_xboole_0 != k2_relat_1(X0)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k2_relat_1(X1)
              & k1_xboole_0 = k2_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t197_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (5084)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.48  % (5101)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.49  % (5087)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (5096)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (5080)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (5079)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (5078)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (5087)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f743,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f145,f249,f265,f376,f381,f742])).
% 0.21/0.52  fof(f742,plain,(
% 0.21/0.52    ~spl3_5 | spl3_11 | ~spl3_12),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f741])).
% 0.21/0.52  fof(f741,plain,(
% 0.21/0.52    $false | (~spl3_5 | spl3_11 | ~spl3_12)),
% 0.21/0.52    inference(subsumption_resolution,[],[f740,f243])).
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    sK2 != k2_funct_1(sK1) | spl3_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f242])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    spl3_11 <=> sK2 = k2_funct_1(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.52  fof(f740,plain,(
% 0.21/0.52    sK2 = k2_funct_1(sK1) | (~spl3_5 | ~spl3_12)),
% 0.21/0.52    inference(subsumption_resolution,[],[f735,f474])).
% 0.21/0.52  fof(f474,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(k2_funct_1(sK1)) | ~spl3_12),
% 0.21/0.52    inference(forward_demodulation,[],[f473,f248])).
% 0.21/0.52  fof(f248,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~spl3_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f246])).
% 0.21/0.52  fof(f246,plain,(
% 0.21/0.52    spl3_12 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.52  fof(f473,plain,(
% 0.21/0.52    sK0 = k2_relat_1(k2_funct_1(sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f472,f318])).
% 0.21/0.52  fof(f318,plain,(
% 0.21/0.52    v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f283,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    v1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 0.21/0.52    inference(resolution,[],[f223,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.52    inference(forward_demodulation,[],[f222,f188])).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f187,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    v1_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f41,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f15])).
% 0.21/0.52  fof(f15,conjecture,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f186,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f182,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    v3_funct_2(sK1,sK0,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f62,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f221,f47])).
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f220,f48])).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f216,f49])).
% 0.21/0.52  fof(f216,plain,(
% 0.21/0.52    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f66,f50])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.52    inference(flattening,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.21/0.52  fof(f472,plain,(
% 0.21/0.52    sK0 = k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f470,f273])).
% 0.21/0.52  fof(f273,plain,(
% 0.21/0.52    v5_relat_1(k2_funct_1(sK1),sK0)),
% 0.21/0.52    inference(resolution,[],[f223,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f470,plain,(
% 0.21/0.52    sK0 = k2_relat_1(k2_funct_1(sK1)) | ~v5_relat_1(k2_funct_1(sK1),sK0) | ~v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.52    inference(resolution,[],[f292,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.21/0.52  fof(f292,plain,(
% 0.21/0.52    v2_funct_2(k2_funct_1(sK1),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f291,f260])).
% 0.21/0.52  fof(f260,plain,(
% 0.21/0.52    v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.52    inference(superposition,[],[f164,f188])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    v1_funct_1(k2_funct_2(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f163,f47])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f162,f48])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f158,f49])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f63,f50])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v1_funct_1(k2_funct_2(X0,X1)) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f291,plain,(
% 0.21/0.52    ~v1_funct_1(k2_funct_1(sK1)) | v2_funct_2(k2_funct_1(sK1),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f276,f211])).
% 0.21/0.52  fof(f211,plain,(
% 0.21/0.52    v3_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 0.21/0.52    inference(forward_demodulation,[],[f210,f188])).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f209,f47])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f208,f48])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f204,f49])).
% 0.21/0.52  fof(f204,plain,(
% 0.21/0.52    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f65,f50])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f276,plain,(
% 0.21/0.52    ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | v2_funct_2(k2_funct_1(sK1),sK0)),
% 0.21/0.52    inference(resolution,[],[f223,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.21/0.52  fof(f735,plain,(
% 0.21/0.52    k1_xboole_0 != k2_relat_1(k2_funct_1(sK1)) | sK2 = k2_funct_1(sK1) | ~spl3_5),
% 0.21/0.52    inference(resolution,[],[f140,f318])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | sK2 = X0) ) | ~spl3_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    spl3_5 <=> ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | sK2 = X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.52  fof(f381,plain,(
% 0.21/0.52    spl3_6 | ~spl3_10 | spl3_11),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f380])).
% 0.21/0.52  fof(f380,plain,(
% 0.21/0.52    $false | (spl3_6 | ~spl3_10 | spl3_11)),
% 0.21/0.52    inference(global_subsumption,[],[f236,f243,f239,f369])).
% 0.21/0.52  fof(f369,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | spl3_6),
% 0.21/0.52    inference(superposition,[],[f144,f255])).
% 0.21/0.52  fof(f255,plain,(
% 0.21/0.52    sK0 = k2_relat_1(sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f254,f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    v1_relat_1(sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f89,f59])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 0.21/0.52    inference(resolution,[],[f58,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    sK0 = k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f253,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    v5_relat_1(sK2,sK0)),
% 0.21/0.52    inference(resolution,[],[f72,f54])).
% 0.21/0.52  fof(f253,plain,(
% 0.21/0.52    sK0 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.21/0.52    inference(resolution,[],[f153,f60])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    v2_funct_2(sK2,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f152,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    v1_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    ~v1_funct_1(sK2) | v2_funct_2(sK2,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f147,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    v3_funct_2(sK2,sK0,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | v2_funct_2(sK2,sK0)),
% 0.21/0.52    inference(resolution,[],[f77,f54])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    k1_xboole_0 != k2_relat_1(sK2) | spl3_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f142])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    spl3_6 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.52  fof(f239,plain,(
% 0.21/0.52    sK0 = k2_relset_1(sK0,sK0,sK1) | ~spl3_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f238])).
% 0.21/0.52  fof(f238,plain,(
% 0.21/0.52    spl3_10 <=> sK0 = k2_relset_1(sK0,sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f235,f47])).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f234,f48])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f233,f50])).
% 0.21/0.52  fof(f233,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f232,f51])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f231,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    v1_funct_2(sK2,sK0,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f230,f54])).
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f229,f115])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    v2_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f114,f47])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f110,f49])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f76,f50])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f229,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f228])).
% 0.21/0.52  fof(f228,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f78,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | k2_funct_1(X2) = X3 | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 0.21/0.52  fof(f376,plain,(
% 0.21/0.52    ~spl3_11),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f375])).
% 0.21/0.52  fof(f375,plain,(
% 0.21/0.52    $false | ~spl3_11),
% 0.21/0.52    inference(subsumption_resolution,[],[f374,f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    r2_relset_1(sK0,sK0,sK2,sK2)),
% 0.21/0.52    inference(resolution,[],[f85,f54])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.52  fof(f374,plain,(
% 0.21/0.52    ~r2_relset_1(sK0,sK0,sK2,sK2) | ~spl3_11),
% 0.21/0.52    inference(superposition,[],[f261,f244])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    sK2 = k2_funct_1(sK1) | ~spl3_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f242])).
% 0.21/0.52  fof(f261,plain,(
% 0.21/0.52    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 0.21/0.52    inference(superposition,[],[f56,f188])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f265,plain,(
% 0.21/0.52    spl3_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f264])).
% 0.21/0.52  fof(f264,plain,(
% 0.21/0.52    $false | spl3_10),
% 0.21/0.52    inference(subsumption_resolution,[],[f263,f252])).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    sK0 = k2_relat_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f251,f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f88,f59])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    v1_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 0.21/0.52    inference(resolution,[],[f58,f50])).
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    sK0 = k2_relat_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f250,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    v5_relat_1(sK1,sK0)),
% 0.21/0.52    inference(resolution,[],[f72,f50])).
% 0.21/0.52  fof(f250,plain,(
% 0.21/0.52    sK0 = k2_relat_1(sK1) | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f151,f60])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    v2_funct_2(sK1,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f150,f47])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f146,f49])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 0.21/0.52    inference(resolution,[],[f77,f50])).
% 0.21/0.52  fof(f263,plain,(
% 0.21/0.52    sK0 != k2_relat_1(sK1) | spl3_10),
% 0.21/0.52    inference(superposition,[],[f240,f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f71,f50])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    sK0 != k2_relset_1(sK0,sK0,sK1) | spl3_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f238])).
% 0.21/0.52  fof(f249,plain,(
% 0.21/0.52    ~spl3_10 | spl3_11 | spl3_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f236,f246,f242,f238])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    spl3_5 | ~spl3_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f137,f142,f139])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 != k2_relat_1(X0) | sK2 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f91,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 != k2_relat_1(X1) | k1_xboole_0 != k2_relat_1(X0) | X0 = X1 | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (X0 = X1 | k1_xboole_0 != k2_relat_1(X1) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((X0 = X1 | (k1_xboole_0 != k2_relat_1(X1) | k1_xboole_0 != k2_relat_1(X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0)) => X0 = X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t197_relat_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (5087)------------------------------
% 0.21/0.52  % (5087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5087)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (5087)Memory used [KB]: 11001
% 0.21/0.52  % (5087)Time elapsed: 0.106 s
% 0.21/0.52  % (5087)------------------------------
% 0.21/0.52  % (5087)------------------------------
% 0.21/0.52  % (5076)Success in time 0.161 s
%------------------------------------------------------------------------------
