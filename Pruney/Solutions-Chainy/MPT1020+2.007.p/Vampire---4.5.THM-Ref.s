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
% DateTime   : Thu Dec  3 13:05:40 EST 2020

% Result     : Theorem 6.46s
% Output     : Refutation 6.46s
% Verified   : 
% Statistics : Number of formulae       :  266 (3816 expanded)
%              Number of leaves         :   34 (1283 expanded)
%              Depth                    :   28
%              Number of atoms          :  807 (33001 expanded)
%              Number of equality atoms :  222 ( 582 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5480,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f232,f641,f663,f681,f688,f4788,f4982,f4991,f5235])).

fof(f5235,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_35
    | ~ spl4_36 ),
    inference(avatar_contradiction_clause,[],[f5234])).

fof(f5234,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_35
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f5233,f5192])).

fof(f5192,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f5015,f230])).

fof(f230,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f5015,plain,
    ( r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1 ),
    inference(superposition,[],[f193,f227])).

fof(f227,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f193,plain,(
    r2_relset_1(sK0,sK0,sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f95,f169])).

fof(f169,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f157])).

fof(f157,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f95,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f82,f81])).

fof(f81,plain,
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

fof(f82,plain,
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

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f38])).

fof(f38,negated_conjecture,(
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
    inference(negated_conjecture,[],[f37])).

fof(f37,conjecture,(
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

fof(f5233,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_35
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f5232,f230])).

fof(f5232,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_35
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f5231,f4990])).

fof(f4990,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f4988])).

fof(f4988,plain,
    ( spl4_36
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f5231,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f5044,f4995])).

fof(f4995,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f4981,f227])).

fof(f4981,plain,
    ( k1_xboole_0 = k2_funct_1(sK1)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f4979])).

fof(f4979,plain,
    ( spl4_35
  <=> k1_xboole_0 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f5044,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(k1_xboole_0))
    | ~ spl4_1 ),
    inference(superposition,[],[f331,f227])).

fof(f331,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(superposition,[],[f101,f175])).

fof(f175,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unit_resulting_resolution,[],[f92,f93,f94,f95,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f94,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f93,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f92,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f83])).

fof(f101,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f83])).

fof(f4991,plain,
    ( spl4_36
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f4986,f229,f4988])).

fof(f4986,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f320,f274])).

fof(f274,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f116,f99,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f99,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f83])).

fof(f116,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f320,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f112,f317])).

fof(f317,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f274,f251,f258,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f258,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f96,f98,f99,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f98,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f96,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

fof(f251,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f99,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f112,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f4982,plain,
    ( spl4_35
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f4977,f229,f4979])).

fof(f4977,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f450,f382])).

fof(f382,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f116,f198,f114])).

fof(f198,plain,(
    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f174,f175])).

fof(f174,plain,(
    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f92,f93,f94,f95,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f450,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = k2_funct_1(sK1)
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(superposition,[],[f112,f447])).

fof(f447,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f382,f353,f360,f120])).

fof(f360,plain,(
    v2_funct_2(k2_funct_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f201,f199,f198,f151])).

fof(f199,plain,(
    v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    inference(forward_demodulation,[],[f173,f175])).

fof(f173,plain,(
    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f92,f93,f94,f95,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f201,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f171,f175])).

fof(f171,plain,(
    v1_funct_1(k2_funct_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f92,f93,f94,f95,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f353,plain,(
    v5_relat_1(k2_funct_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f198,f138])).

fof(f4788,plain,
    ( spl4_2
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f4787])).

fof(f4787,plain,
    ( $false
    | spl4_2
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f4741,f272])).

fof(f272,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f99,f169])).

fof(f4741,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | spl4_2
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(superposition,[],[f331,f4687])).

fof(f4687,plain,
    ( sK2 = k2_funct_1(sK1)
    | spl4_2
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(superposition,[],[f313,f4681])).

fof(f4681,plain,
    ( sK1 = k2_funct_1(sK2)
    | spl4_2
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(superposition,[],[f4484,f595])).

fof(f595,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_relat_1(sK0),k2_funct_1(sK2))
    | spl4_2 ),
    inference(forward_demodulation,[],[f517,f510])).

fof(f510,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK2))
    | spl4_2 ),
    inference(forward_demodulation,[],[f468,f475])).

fof(f475,plain,
    ( sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK2))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f231,f282,f280,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
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
    inference(nnf_transformation,[],[f68])).

fof(f68,plain,(
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
    inference(flattening,[],[f67])).

fof(f67,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f280,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f246,f247])).

fof(f247,plain,(
    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f96,f97,f98,f99,f122])).

fof(f97,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f246,plain,(
    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f96,f97,f98,f99,f126])).

fof(f282,plain,(
    v1_funct_2(k2_funct_1(sK2),sK0,sK0) ),
    inference(forward_demodulation,[],[f244,f247])).

fof(f244,plain,(
    v1_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f96,f97,f98,f99,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f231,plain,
    ( k1_xboole_0 != sK0
    | spl4_2 ),
    inference(avatar_component_clause,[],[f229])).

fof(f468,plain,(
    k1_relset_1(sK0,sK0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f280,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f517,plain,(
    k2_funct_1(sK2) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f505,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f505,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f116,f280,f114])).

fof(f4484,plain,
    ( sK1 = k5_relat_1(k6_relat_1(sK0),k2_funct_1(sK2))
    | spl4_2
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f4483,f613])).

fof(f613,plain,
    ( sK1 = k5_relat_1(k6_relat_1(sK0),sK1)
    | spl4_2 ),
    inference(superposition,[],[f203,f342])).

fof(f342,plain,
    ( sK0 = k1_relat_1(sK1)
    | spl4_2 ),
    inference(superposition,[],[f177,f242])).

fof(f242,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f93,f95,f231,f143])).

fof(f177,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f95,f136])).

fof(f203,plain,(
    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f195,f110])).

fof(f195,plain,(
    v1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f116,f95,f114])).

fof(f4483,plain,
    ( k5_relat_1(k6_relat_1(sK0),k2_funct_1(sK2)) = k5_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f4482,f612])).

fof(f612,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(superposition,[],[f202,f219])).

fof(f219,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f195,f179,f185,f120])).

fof(f185,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f92,f94,f95,f151])).

fof(f179,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f95,f138])).

fof(f202,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f195,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f4482,plain,
    ( k5_relat_1(k6_relat_1(sK0),k2_funct_1(sK2)) = k5_relat_1(k6_relat_1(sK0),k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f4481,f4112])).

fof(f4112,plain,
    ( k6_relat_1(sK0) = k5_relat_1(k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f4111,f662])).

fof(f662,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f660])).

fof(f660,plain,
    ( spl4_12
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f4111,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k5_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)),k6_relat_1(sK0))
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f4105,f1476])).

fof(f1476,plain,(
    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) ),
    inference(superposition,[],[f516,f597])).

fof(f597,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f505,f470,f477,f120])).

fof(f477,plain,(
    v2_funct_2(k2_funct_1(sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f283,f281,f280,f151])).

fof(f281,plain,(
    v3_funct_2(k2_funct_1(sK2),sK0,sK0) ),
    inference(forward_demodulation,[],[f245,f247])).

fof(f245,plain,(
    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f96,f97,f98,f99,f125])).

fof(f283,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f243,f247])).

fof(f243,plain,(
    v1_funct_1(k2_funct_2(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f96,f97,f98,f99,f123])).

fof(f470,plain,(
    v5_relat_1(k2_funct_1(sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f280,f138])).

fof(f516,plain,(
    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(k2_relat_1(k2_funct_1(sK2)))) ),
    inference(unit_resulting_resolution,[],[f505,f109])).

fof(f4105,plain,
    ( k5_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)),k6_relat_1(sK0)) = k5_relat_1(sK2,k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)))
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f505,f274,f3763,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f3763,plain,
    ( v1_relat_1(k6_relat_1(sK0))
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f116,f3671,f114])).

fof(f3671,plain,
    ( m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f3670,f640])).

fof(f640,plain,
    ( k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f638])).

fof(f638,plain,
    ( spl4_10
  <=> k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f3670,plain,(
    m1_subset_1(k5_relat_1(k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f3669,f201])).

fof(f3669,plain,
    ( m1_subset_1(k5_relat_1(k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f3668,f198])).

fof(f3668,plain,
    ( m1_subset_1(k5_relat_1(k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f3667,f92])).

fof(f3667,plain,
    ( m1_subset_1(k5_relat_1(k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f3660,f95])).

fof(f3660,plain,
    ( m1_subset_1(k5_relat_1(k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(superposition,[],[f160,f363])).

fof(f363,plain,(
    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f92,f201,f95,f198,f158])).

fof(f158,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f160,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f4481,plain,
    ( k5_relat_1(k6_relat_1(sK0),k5_relat_1(sK1,k6_relat_1(sK0))) = k5_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(sK0)),k2_funct_1(sK2))
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f4480,f3681])).

fof(f3681,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK1,sK2)
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f1489,f1483,f3671,f156])).

fof(f156,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f1483,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0)) ),
    inference(superposition,[],[f170,f262])).

fof(f262,plain,(
    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f92,f96,f95,f99,f158])).

fof(f170,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f100,f103])).

fof(f103,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f100,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f83])).

fof(f1489,plain,(
    m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f1488,f92])).

fof(f1488,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f1487,f95])).

fof(f1487,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f1486,f96])).

fof(f1486,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f1485,f99])).

fof(f1485,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(superposition,[],[f160,f262])).

fof(f4480,plain,
    ( k5_relat_1(k6_relat_1(sK0),k5_relat_1(sK1,k6_relat_1(sK0))) = k5_relat_1(k5_relat_1(k6_relat_1(sK0),k5_relat_1(sK1,sK2)),k2_funct_1(sK2))
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f4479,f662])).

fof(f4479,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(sK0),k5_relat_1(sK1,sK2)),k2_funct_1(sK2)) = k5_relat_1(k6_relat_1(sK0),k5_relat_1(sK1,k5_relat_1(sK2,k2_funct_1(sK2))))
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f3881,f587])).

fof(f587,plain,(
    k5_relat_1(k5_relat_1(sK1,sK2),k2_funct_1(sK2)) = k5_relat_1(sK1,k5_relat_1(sK2,k2_funct_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f274,f195,f505,f113])).

fof(f3881,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(sK0),k5_relat_1(sK1,sK2)),k2_funct_1(sK2)) = k5_relat_1(k6_relat_1(sK0),k5_relat_1(k5_relat_1(sK1,sK2),k2_funct_1(sK2)))
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f1543,f505,f3763,f113])).

fof(f1543,plain,(
    v1_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f116,f1489,f114])).

fof(f313,plain,(
    sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f257,f96,f274,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f257,plain,(
    v2_funct_1(sK2) ),
    inference(unit_resulting_resolution,[],[f96,f98,f99,f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f688,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f687])).

fof(f687,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f686,f658])).

fof(f658,plain,
    ( sK0 != k9_relat_1(sK2,sK0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f656])).

fof(f656,plain,
    ( spl4_11
  <=> sK0 = k9_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f686,plain,(
    sK0 = k9_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f682,f317])).

fof(f682,plain,(
    k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[],[f314,f316])).

fof(f316,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f274,f250,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f250,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f99,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f314,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k2_relat_1(k7_relat_1(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f274,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f681,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f680])).

fof(f680,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f679,f625])).

fof(f625,plain,
    ( sK0 != k9_relat_1(sK1,sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f623])).

fof(f623,plain,
    ( spl4_8
  <=> sK0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f679,plain,(
    sK0 = k9_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f675,f219])).

fof(f675,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(sK1) ),
    inference(superposition,[],[f217,f218])).

fof(f218,plain,(
    sK1 = k7_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f195,f178,f119])).

fof(f178,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f95,f137])).

fof(f217,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k2_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f195,f118])).

fof(f663,plain,
    ( ~ spl4_11
    | spl4_12
    | spl4_2 ),
    inference(avatar_split_clause,[],[f654,f229,f660,f656])).

fof(f654,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | sK0 != k9_relat_1(sK2,sK0)
    | spl4_2 ),
    inference(forward_demodulation,[],[f653,f103])).

fof(f653,plain,
    ( sK0 != k9_relat_1(sK2,sK0)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f652,f96])).

fof(f652,plain,
    ( sK0 != k9_relat_1(sK2,sK0)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f651,f97])).

fof(f651,plain,
    ( sK0 != k9_relat_1(sK2,sK0)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f650,f99])).

fof(f650,plain,
    ( sK0 != k9_relat_1(sK2,sK0)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f649,f257])).

fof(f649,plain,
    ( sK0 != k9_relat_1(sK2,sK0)
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f647,f231])).

fof(f647,plain,
    ( sK0 != k9_relat_1(sK2,sK0)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f152,f278])).

fof(f278,plain,(
    k2_relset_1(sK0,sK0,sK2) = k9_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f252,f259])).

fof(f259,plain,(
    ! [X0] : k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f99,f155])).

fof(f155,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f252,plain,(
    k2_relset_1(sK0,sK0,sK2) = k7_relset_1(sK0,sK0,sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f99,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
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

fof(f641,plain,
    ( ~ spl4_8
    | spl4_10
    | spl4_2 ),
    inference(avatar_split_clause,[],[f636,f229,f638,f623])).

fof(f636,plain,
    ( k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | sK0 != k9_relat_1(sK1,sK0)
    | spl4_2 ),
    inference(forward_demodulation,[],[f635,f103])).

fof(f635,plain,
    ( sK0 != k9_relat_1(sK1,sK0)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f634,f92])).

fof(f634,plain,
    ( sK0 != k9_relat_1(sK1,sK0)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ v1_funct_1(sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f633,f93])).

fof(f633,plain,
    ( sK0 != k9_relat_1(sK1,sK0)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f632,f95])).

fof(f632,plain,
    ( sK0 != k9_relat_1(sK1,sK0)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f631,f184])).

fof(f184,plain,(
    v2_funct_1(sK1) ),
    inference(unit_resulting_resolution,[],[f92,f94,f95,f150])).

fof(f631,plain,
    ( sK0 != k9_relat_1(sK1,sK0)
    | ~ v2_funct_1(sK1)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f615,f231])).

fof(f615,plain,
    ( sK0 != k9_relat_1(sK1,sK0)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(superposition,[],[f153,f197])).

fof(f197,plain,(
    k2_relset_1(sK0,sK0,sK1) = k9_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f180,f186])).

fof(f186,plain,(
    ! [X0] : k7_relset_1(sK0,sK0,sK1,X0) = k9_relat_1(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f95,f155])).

fof(f180,plain,(
    k2_relset_1(sK0,sK0,sK1) = k7_relset_1(sK0,sK0,sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f95,f139])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f232,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f223,f229,f225])).

fof(f223,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f221,f195])).

fof(f221,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f112,f219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:59:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (13807)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (13810)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (13811)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (13815)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (13814)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (13823)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (13826)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (13808)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (13812)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (13829)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (13827)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (13831)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (13820)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (13821)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (13825)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (13817)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (13806)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (13832)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (13816)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (13833)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (13819)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (13834)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (13835)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (13828)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (13830)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (13818)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (13822)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.57  % (13809)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.57  % (13822)Refutation not found, incomplete strategy% (13822)------------------------------
% 0.21/0.57  % (13822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (13822)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (13822)Memory used [KB]: 10746
% 0.21/0.57  % (13822)Time elapsed: 0.153 s
% 0.21/0.57  % (13822)------------------------------
% 0.21/0.57  % (13822)------------------------------
% 0.21/0.58  % (13824)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.59  % (13813)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 2.65/0.72  % (13842)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.90/0.81  % (13830)Time limit reached!
% 2.90/0.81  % (13830)------------------------------
% 2.90/0.81  % (13830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.90/0.81  % (13830)Termination reason: Time limit
% 2.90/0.81  % (13830)Termination phase: Saturation
% 2.90/0.81  
% 2.90/0.81  % (13830)Memory used [KB]: 12665
% 2.90/0.81  % (13830)Time elapsed: 0.400 s
% 2.90/0.81  % (13830)------------------------------
% 2.90/0.81  % (13830)------------------------------
% 3.59/0.83  % (13808)Time limit reached!
% 3.59/0.83  % (13808)------------------------------
% 3.59/0.83  % (13808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.59/0.83  % (13808)Termination reason: Time limit
% 3.59/0.83  % (13808)Termination phase: Saturation
% 3.59/0.83  
% 3.59/0.83  % (13808)Memory used [KB]: 6780
% 3.59/0.83  % (13808)Time elapsed: 0.400 s
% 3.59/0.83  % (13808)------------------------------
% 3.59/0.83  % (13808)------------------------------
% 3.98/0.92  % (13835)Time limit reached!
% 3.98/0.92  % (13835)------------------------------
% 3.98/0.92  % (13835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.92  % (13812)Time limit reached!
% 3.98/0.92  % (13812)------------------------------
% 3.98/0.92  % (13812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.92  % (13835)Termination reason: Time limit
% 3.98/0.92  
% 3.98/0.92  % (13835)Memory used [KB]: 5117
% 3.98/0.92  % (13835)Time elapsed: 0.511 s
% 3.98/0.92  % (13835)------------------------------
% 3.98/0.92  % (13835)------------------------------
% 3.98/0.93  % (13812)Termination reason: Time limit
% 3.98/0.93  
% 3.98/0.93  % (13812)Memory used [KB]: 13560
% 3.98/0.93  % (13812)Time elapsed: 0.506 s
% 3.98/0.93  % (13812)------------------------------
% 3.98/0.93  % (13812)------------------------------
% 3.98/0.93  % (13820)Time limit reached!
% 3.98/0.93  % (13820)------------------------------
% 3.98/0.93  % (13820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.94  % (13820)Termination reason: Time limit
% 3.98/0.94  
% 3.98/0.94  % (13820)Memory used [KB]: 4733
% 3.98/0.94  % (13820)Time elapsed: 0.521 s
% 3.98/0.94  % (13820)------------------------------
% 3.98/0.94  % (13820)------------------------------
% 3.98/0.94  % (13872)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.53/0.96  % (13873)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 5.15/1.05  % (13813)Time limit reached!
% 5.15/1.05  % (13813)------------------------------
% 5.15/1.05  % (13813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.15/1.05  % (13813)Termination reason: Time limit
% 5.15/1.05  % (13813)Termination phase: Saturation
% 5.15/1.05  
% 5.15/1.05  % (13813)Memory used [KB]: 7419
% 5.15/1.05  % (13813)Time elapsed: 0.600 s
% 5.15/1.05  % (13813)------------------------------
% 5.15/1.05  % (13813)------------------------------
% 5.15/1.06  % (13874)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 5.15/1.07  % (13875)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.15/1.07  % (13876)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 6.03/1.18  % (13877)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 6.46/1.22  % (13807)Time limit reached!
% 6.46/1.22  % (13807)------------------------------
% 6.46/1.22  % (13807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.46/1.24  % (13807)Termination reason: Time limit
% 6.46/1.24  % (13807)Termination phase: Saturation
% 6.46/1.24  
% 6.46/1.24  % (13807)Memory used [KB]: 9083
% 6.46/1.24  % (13807)Time elapsed: 0.800 s
% 6.46/1.24  % (13807)------------------------------
% 6.46/1.24  % (13807)------------------------------
% 6.46/1.25  % (13874)Refutation found. Thanks to Tanya!
% 6.46/1.25  % SZS status Theorem for theBenchmark
% 6.46/1.25  % SZS output start Proof for theBenchmark
% 6.46/1.25  fof(f5480,plain,(
% 6.46/1.25    $false),
% 6.46/1.25    inference(avatar_sat_refutation,[],[f232,f641,f663,f681,f688,f4788,f4982,f4991,f5235])).
% 6.46/1.25  fof(f5235,plain,(
% 6.46/1.25    ~spl4_1 | ~spl4_2 | ~spl4_35 | ~spl4_36),
% 6.46/1.25    inference(avatar_contradiction_clause,[],[f5234])).
% 6.46/1.25  fof(f5234,plain,(
% 6.46/1.25    $false | (~spl4_1 | ~spl4_2 | ~spl4_35 | ~spl4_36)),
% 6.46/1.25    inference(subsumption_resolution,[],[f5233,f5192])).
% 6.46/1.25  fof(f5192,plain,(
% 6.46/1.25    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_2)),
% 6.46/1.25    inference(forward_demodulation,[],[f5015,f230])).
% 6.46/1.25  fof(f230,plain,(
% 6.46/1.25    k1_xboole_0 = sK0 | ~spl4_2),
% 6.46/1.25    inference(avatar_component_clause,[],[f229])).
% 6.46/1.25  fof(f229,plain,(
% 6.46/1.25    spl4_2 <=> k1_xboole_0 = sK0),
% 6.46/1.25    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 6.46/1.25  fof(f5015,plain,(
% 6.46/1.25    r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0) | ~spl4_1),
% 6.46/1.25    inference(superposition,[],[f193,f227])).
% 6.46/1.25  fof(f227,plain,(
% 6.46/1.25    k1_xboole_0 = sK1 | ~spl4_1),
% 6.46/1.25    inference(avatar_component_clause,[],[f225])).
% 6.46/1.25  fof(f225,plain,(
% 6.46/1.25    spl4_1 <=> k1_xboole_0 = sK1),
% 6.46/1.25    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 6.46/1.25  fof(f193,plain,(
% 6.46/1.25    r2_relset_1(sK0,sK0,sK1,sK1)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f95,f169])).
% 6.46/1.25  fof(f169,plain,(
% 6.46/1.25    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.46/1.25    inference(duplicate_literal_removal,[],[f168])).
% 6.46/1.25  fof(f168,plain,(
% 6.46/1.25    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.46/1.25    inference(equality_resolution,[],[f157])).
% 6.46/1.25  fof(f157,plain,(
% 6.46/1.25    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.46/1.25    inference(cnf_transformation,[],[f91])).
% 6.46/1.25  fof(f91,plain,(
% 6.46/1.25    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.46/1.25    inference(nnf_transformation,[],[f76])).
% 6.46/1.25  fof(f76,plain,(
% 6.46/1.25    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.46/1.25    inference(flattening,[],[f75])).
% 6.46/1.25  fof(f75,plain,(
% 6.46/1.25    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.46/1.25    inference(ennf_transformation,[],[f23])).
% 6.46/1.25  fof(f23,axiom,(
% 6.46/1.25    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 6.46/1.25  fof(f95,plain,(
% 6.46/1.25    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 6.46/1.25    inference(cnf_transformation,[],[f83])).
% 6.46/1.25  fof(f83,plain,(
% 6.46/1.25    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 6.46/1.25    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f82,f81])).
% 6.46/1.25  fof(f81,plain,(
% 6.46/1.25    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 6.46/1.25    introduced(choice_axiom,[])).
% 6.46/1.25  fof(f82,plain,(
% 6.46/1.25    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 6.46/1.25    introduced(choice_axiom,[])).
% 6.46/1.25  fof(f40,plain,(
% 6.46/1.25    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 6.46/1.25    inference(flattening,[],[f39])).
% 6.46/1.25  fof(f39,plain,(
% 6.46/1.25    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 6.46/1.25    inference(ennf_transformation,[],[f38])).
% 6.46/1.25  fof(f38,negated_conjecture,(
% 6.46/1.25    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 6.46/1.25    inference(negated_conjecture,[],[f37])).
% 6.46/1.25  fof(f37,conjecture,(
% 6.46/1.25    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).
% 6.46/1.25  fof(f5233,plain,(
% 6.46/1.25    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_2 | ~spl4_35 | ~spl4_36)),
% 6.46/1.25    inference(forward_demodulation,[],[f5232,f230])).
% 6.46/1.25  fof(f5232,plain,(
% 6.46/1.25    ~r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_35 | ~spl4_36)),
% 6.46/1.25    inference(forward_demodulation,[],[f5231,f4990])).
% 6.46/1.25  fof(f4990,plain,(
% 6.46/1.25    k1_xboole_0 = sK2 | ~spl4_36),
% 6.46/1.25    inference(avatar_component_clause,[],[f4988])).
% 6.46/1.25  fof(f4988,plain,(
% 6.46/1.25    spl4_36 <=> k1_xboole_0 = sK2),
% 6.46/1.25    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 6.46/1.25  fof(f5231,plain,(
% 6.46/1.25    ~r2_relset_1(sK0,sK0,sK2,k1_xboole_0) | (~spl4_1 | ~spl4_35)),
% 6.46/1.25    inference(forward_demodulation,[],[f5044,f4995])).
% 6.46/1.25  fof(f4995,plain,(
% 6.46/1.25    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl4_1 | ~spl4_35)),
% 6.46/1.25    inference(forward_demodulation,[],[f4981,f227])).
% 6.46/1.25  fof(f4981,plain,(
% 6.46/1.25    k1_xboole_0 = k2_funct_1(sK1) | ~spl4_35),
% 6.46/1.25    inference(avatar_component_clause,[],[f4979])).
% 6.46/1.25  fof(f4979,plain,(
% 6.46/1.25    spl4_35 <=> k1_xboole_0 = k2_funct_1(sK1)),
% 6.46/1.25    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 6.46/1.25  fof(f5044,plain,(
% 6.46/1.25    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(k1_xboole_0)) | ~spl4_1),
% 6.46/1.25    inference(superposition,[],[f331,f227])).
% 6.46/1.25  fof(f331,plain,(
% 6.46/1.25    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 6.46/1.25    inference(superposition,[],[f101,f175])).
% 6.46/1.25  fof(f175,plain,(
% 6.46/1.25    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f92,f93,f94,f95,f122])).
% 6.46/1.25  fof(f122,plain,(
% 6.46/1.25    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 6.46/1.25    inference(cnf_transformation,[],[f57])).
% 6.46/1.25  fof(f57,plain,(
% 6.46/1.25    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 6.46/1.25    inference(flattening,[],[f56])).
% 6.46/1.25  fof(f56,plain,(
% 6.46/1.25    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 6.46/1.25    inference(ennf_transformation,[],[f34])).
% 6.46/1.25  fof(f34,axiom,(
% 6.46/1.25    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 6.46/1.25  fof(f94,plain,(
% 6.46/1.25    v3_funct_2(sK1,sK0,sK0)),
% 6.46/1.25    inference(cnf_transformation,[],[f83])).
% 6.46/1.25  fof(f93,plain,(
% 6.46/1.25    v1_funct_2(sK1,sK0,sK0)),
% 6.46/1.25    inference(cnf_transformation,[],[f83])).
% 6.46/1.25  fof(f92,plain,(
% 6.46/1.25    v1_funct_1(sK1)),
% 6.46/1.25    inference(cnf_transformation,[],[f83])).
% 6.46/1.25  fof(f101,plain,(
% 6.46/1.25    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 6.46/1.25    inference(cnf_transformation,[],[f83])).
% 6.46/1.25  fof(f4991,plain,(
% 6.46/1.25    spl4_36 | ~spl4_2),
% 6.46/1.25    inference(avatar_split_clause,[],[f4986,f229,f4988])).
% 6.46/1.25  fof(f4986,plain,(
% 6.46/1.25    k1_xboole_0 != sK0 | k1_xboole_0 = sK2),
% 6.46/1.25    inference(subsumption_resolution,[],[f320,f274])).
% 6.46/1.25  fof(f274,plain,(
% 6.46/1.25    v1_relat_1(sK2)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f116,f99,f114])).
% 6.46/1.25  fof(f114,plain,(
% 6.46/1.25    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 6.46/1.25    inference(cnf_transformation,[],[f47])).
% 6.46/1.25  fof(f47,plain,(
% 6.46/1.25    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 6.46/1.25    inference(ennf_transformation,[],[f8])).
% 6.46/1.25  fof(f8,axiom,(
% 6.46/1.25    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 6.46/1.25  fof(f99,plain,(
% 6.46/1.25    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 6.46/1.25    inference(cnf_transformation,[],[f83])).
% 6.46/1.25  fof(f116,plain,(
% 6.46/1.25    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 6.46/1.25    inference(cnf_transformation,[],[f10])).
% 6.46/1.25  fof(f10,axiom,(
% 6.46/1.25    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 6.46/1.25  fof(f320,plain,(
% 6.46/1.25    k1_xboole_0 != sK0 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 6.46/1.25    inference(superposition,[],[f112,f317])).
% 6.46/1.25  fof(f317,plain,(
% 6.46/1.25    sK0 = k2_relat_1(sK2)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f274,f251,f258,f120])).
% 6.46/1.25  fof(f120,plain,(
% 6.46/1.25    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.46/1.25    inference(cnf_transformation,[],[f84])).
% 6.46/1.25  fof(f84,plain,(
% 6.46/1.25    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.46/1.25    inference(nnf_transformation,[],[f55])).
% 6.46/1.25  fof(f55,plain,(
% 6.46/1.25    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.46/1.25    inference(flattening,[],[f54])).
% 6.46/1.25  fof(f54,plain,(
% 6.46/1.25    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 6.46/1.25    inference(ennf_transformation,[],[f29])).
% 6.46/1.25  fof(f29,axiom,(
% 6.46/1.25    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 6.46/1.25  fof(f258,plain,(
% 6.46/1.25    v2_funct_2(sK2,sK0)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f96,f98,f99,f151])).
% 6.46/1.25  fof(f151,plain,(
% 6.46/1.25    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.46/1.25    inference(cnf_transformation,[],[f70])).
% 6.46/1.25  fof(f70,plain,(
% 6.46/1.25    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.46/1.25    inference(flattening,[],[f69])).
% 6.46/1.25  fof(f69,plain,(
% 6.46/1.25    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.46/1.25    inference(ennf_transformation,[],[f27])).
% 6.46/1.25  fof(f27,axiom,(
% 6.46/1.25    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 6.46/1.25  fof(f98,plain,(
% 6.46/1.25    v3_funct_2(sK2,sK0,sK0)),
% 6.46/1.25    inference(cnf_transformation,[],[f83])).
% 6.46/1.25  fof(f96,plain,(
% 6.46/1.25    v1_funct_1(sK2)),
% 6.46/1.25    inference(cnf_transformation,[],[f83])).
% 6.46/1.25  fof(f251,plain,(
% 6.46/1.25    v5_relat_1(sK2,sK0)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f99,f138])).
% 6.46/1.25  fof(f138,plain,(
% 6.46/1.25    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.46/1.25    inference(cnf_transformation,[],[f64])).
% 6.46/1.25  fof(f64,plain,(
% 6.46/1.25    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.46/1.25    inference(ennf_transformation,[],[f20])).
% 6.46/1.25  fof(f20,axiom,(
% 6.46/1.25    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 6.46/1.25  fof(f112,plain,(
% 6.46/1.25    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 6.46/1.25    inference(cnf_transformation,[],[f45])).
% 6.46/1.25  fof(f45,plain,(
% 6.46/1.25    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 6.46/1.25    inference(flattening,[],[f44])).
% 6.46/1.25  fof(f44,plain,(
% 6.46/1.25    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 6.46/1.25    inference(ennf_transformation,[],[f14])).
% 6.46/1.25  fof(f14,axiom,(
% 6.46/1.25    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 6.46/1.25  fof(f4982,plain,(
% 6.46/1.25    spl4_35 | ~spl4_2),
% 6.46/1.25    inference(avatar_split_clause,[],[f4977,f229,f4979])).
% 6.46/1.25  fof(f4977,plain,(
% 6.46/1.25    k1_xboole_0 != sK0 | k1_xboole_0 = k2_funct_1(sK1)),
% 6.46/1.25    inference(subsumption_resolution,[],[f450,f382])).
% 6.46/1.25  fof(f382,plain,(
% 6.46/1.25    v1_relat_1(k2_funct_1(sK1))),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f116,f198,f114])).
% 6.46/1.25  fof(f198,plain,(
% 6.46/1.25    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 6.46/1.25    inference(forward_demodulation,[],[f174,f175])).
% 6.46/1.25  fof(f174,plain,(
% 6.46/1.25    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f92,f93,f94,f95,f126])).
% 6.46/1.25  fof(f126,plain,(
% 6.46/1.25    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 6.46/1.25    inference(cnf_transformation,[],[f59])).
% 6.46/1.25  fof(f59,plain,(
% 6.46/1.25    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 6.46/1.25    inference(flattening,[],[f58])).
% 6.46/1.25  fof(f58,plain,(
% 6.46/1.25    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 6.46/1.25    inference(ennf_transformation,[],[f31])).
% 6.46/1.25  fof(f31,axiom,(
% 6.46/1.25    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 6.46/1.25  fof(f450,plain,(
% 6.46/1.25    k1_xboole_0 != sK0 | k1_xboole_0 = k2_funct_1(sK1) | ~v1_relat_1(k2_funct_1(sK1))),
% 6.46/1.25    inference(superposition,[],[f112,f447])).
% 6.46/1.25  fof(f447,plain,(
% 6.46/1.25    sK0 = k2_relat_1(k2_funct_1(sK1))),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f382,f353,f360,f120])).
% 6.46/1.25  fof(f360,plain,(
% 6.46/1.25    v2_funct_2(k2_funct_1(sK1),sK0)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f201,f199,f198,f151])).
% 6.46/1.25  fof(f199,plain,(
% 6.46/1.25    v3_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 6.46/1.25    inference(forward_demodulation,[],[f173,f175])).
% 6.46/1.25  fof(f173,plain,(
% 6.46/1.25    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f92,f93,f94,f95,f125])).
% 6.46/1.25  fof(f125,plain,(
% 6.46/1.25    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 6.46/1.25    inference(cnf_transformation,[],[f59])).
% 6.46/1.25  fof(f201,plain,(
% 6.46/1.25    v1_funct_1(k2_funct_1(sK1))),
% 6.46/1.25    inference(forward_demodulation,[],[f171,f175])).
% 6.46/1.25  fof(f171,plain,(
% 6.46/1.25    v1_funct_1(k2_funct_2(sK0,sK1))),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f92,f93,f94,f95,f123])).
% 6.46/1.25  fof(f123,plain,(
% 6.46/1.25    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 6.46/1.25    inference(cnf_transformation,[],[f59])).
% 6.46/1.25  fof(f353,plain,(
% 6.46/1.25    v5_relat_1(k2_funct_1(sK1),sK0)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f198,f138])).
% 6.46/1.25  fof(f4788,plain,(
% 6.46/1.25    spl4_2 | ~spl4_10 | ~spl4_12),
% 6.46/1.25    inference(avatar_contradiction_clause,[],[f4787])).
% 6.46/1.25  fof(f4787,plain,(
% 6.46/1.25    $false | (spl4_2 | ~spl4_10 | ~spl4_12)),
% 6.46/1.25    inference(subsumption_resolution,[],[f4741,f272])).
% 6.46/1.25  fof(f272,plain,(
% 6.46/1.25    r2_relset_1(sK0,sK0,sK2,sK2)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f99,f169])).
% 6.46/1.25  fof(f4741,plain,(
% 6.46/1.25    ~r2_relset_1(sK0,sK0,sK2,sK2) | (spl4_2 | ~spl4_10 | ~spl4_12)),
% 6.46/1.25    inference(superposition,[],[f331,f4687])).
% 6.46/1.25  fof(f4687,plain,(
% 6.46/1.25    sK2 = k2_funct_1(sK1) | (spl4_2 | ~spl4_10 | ~spl4_12)),
% 6.46/1.25    inference(superposition,[],[f313,f4681])).
% 6.46/1.25  fof(f4681,plain,(
% 6.46/1.25    sK1 = k2_funct_1(sK2) | (spl4_2 | ~spl4_10 | ~spl4_12)),
% 6.46/1.25    inference(superposition,[],[f4484,f595])).
% 6.46/1.25  fof(f595,plain,(
% 6.46/1.25    k2_funct_1(sK2) = k5_relat_1(k6_relat_1(sK0),k2_funct_1(sK2)) | spl4_2),
% 6.46/1.25    inference(forward_demodulation,[],[f517,f510])).
% 6.46/1.25  fof(f510,plain,(
% 6.46/1.25    sK0 = k1_relat_1(k2_funct_1(sK2)) | spl4_2),
% 6.46/1.25    inference(forward_demodulation,[],[f468,f475])).
% 6.46/1.25  fof(f475,plain,(
% 6.46/1.25    sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK2)) | spl4_2),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f231,f282,f280,f143])).
% 6.46/1.25  fof(f143,plain,(
% 6.46/1.25    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.46/1.25    inference(cnf_transformation,[],[f90])).
% 6.46/1.25  fof(f90,plain,(
% 6.46/1.25    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.46/1.25    inference(nnf_transformation,[],[f68])).
% 6.46/1.25  fof(f68,plain,(
% 6.46/1.25    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.46/1.25    inference(flattening,[],[f67])).
% 6.46/1.25  fof(f67,plain,(
% 6.46/1.25    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.46/1.25    inference(ennf_transformation,[],[f28])).
% 6.46/1.25  fof(f28,axiom,(
% 6.46/1.25    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 6.46/1.25  fof(f280,plain,(
% 6.46/1.25    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 6.46/1.25    inference(forward_demodulation,[],[f246,f247])).
% 6.46/1.25  fof(f247,plain,(
% 6.46/1.25    k2_funct_1(sK2) = k2_funct_2(sK0,sK2)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f96,f97,f98,f99,f122])).
% 6.46/1.25  fof(f97,plain,(
% 6.46/1.25    v1_funct_2(sK2,sK0,sK0)),
% 6.46/1.25    inference(cnf_transformation,[],[f83])).
% 6.46/1.25  fof(f246,plain,(
% 6.46/1.25    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f96,f97,f98,f99,f126])).
% 6.46/1.25  fof(f282,plain,(
% 6.46/1.25    v1_funct_2(k2_funct_1(sK2),sK0,sK0)),
% 6.46/1.25    inference(forward_demodulation,[],[f244,f247])).
% 6.46/1.25  fof(f244,plain,(
% 6.46/1.25    v1_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f96,f97,f98,f99,f124])).
% 6.46/1.25  fof(f124,plain,(
% 6.46/1.25    ( ! [X0,X1] : (v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 6.46/1.25    inference(cnf_transformation,[],[f59])).
% 6.46/1.25  fof(f231,plain,(
% 6.46/1.25    k1_xboole_0 != sK0 | spl4_2),
% 6.46/1.25    inference(avatar_component_clause,[],[f229])).
% 6.46/1.25  fof(f468,plain,(
% 6.46/1.25    k1_relset_1(sK0,sK0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f280,f136])).
% 6.46/1.25  fof(f136,plain,(
% 6.46/1.25    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 6.46/1.25    inference(cnf_transformation,[],[f63])).
% 6.46/1.25  fof(f63,plain,(
% 6.46/1.25    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.46/1.25    inference(ennf_transformation,[],[f21])).
% 6.46/1.25  fof(f21,axiom,(
% 6.46/1.25    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 6.46/1.25  fof(f517,plain,(
% 6.46/1.25    k2_funct_1(sK2) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2))),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f505,f110])).
% 6.46/1.25  fof(f110,plain,(
% 6.46/1.25    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 6.46/1.25    inference(cnf_transformation,[],[f43])).
% 6.46/1.25  fof(f43,plain,(
% 6.46/1.25    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 6.46/1.25    inference(ennf_transformation,[],[f15])).
% 6.46/1.25  fof(f15,axiom,(
% 6.46/1.25    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 6.46/1.25  fof(f505,plain,(
% 6.46/1.25    v1_relat_1(k2_funct_1(sK2))),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f116,f280,f114])).
% 6.46/1.25  fof(f4484,plain,(
% 6.46/1.25    sK1 = k5_relat_1(k6_relat_1(sK0),k2_funct_1(sK2)) | (spl4_2 | ~spl4_10 | ~spl4_12)),
% 6.46/1.25    inference(forward_demodulation,[],[f4483,f613])).
% 6.46/1.25  fof(f613,plain,(
% 6.46/1.25    sK1 = k5_relat_1(k6_relat_1(sK0),sK1) | spl4_2),
% 6.46/1.25    inference(superposition,[],[f203,f342])).
% 6.46/1.25  fof(f342,plain,(
% 6.46/1.25    sK0 = k1_relat_1(sK1) | spl4_2),
% 6.46/1.25    inference(superposition,[],[f177,f242])).
% 6.46/1.25  fof(f242,plain,(
% 6.46/1.25    sK0 = k1_relset_1(sK0,sK0,sK1) | spl4_2),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f93,f95,f231,f143])).
% 6.46/1.25  fof(f177,plain,(
% 6.46/1.25    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f95,f136])).
% 6.46/1.25  fof(f203,plain,(
% 6.46/1.25    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f195,f110])).
% 6.46/1.25  fof(f195,plain,(
% 6.46/1.25    v1_relat_1(sK1)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f116,f95,f114])).
% 6.46/1.25  fof(f4483,plain,(
% 6.46/1.25    k5_relat_1(k6_relat_1(sK0),k2_funct_1(sK2)) = k5_relat_1(k6_relat_1(sK0),sK1) | (~spl4_10 | ~spl4_12)),
% 6.46/1.25    inference(forward_demodulation,[],[f4482,f612])).
% 6.46/1.25  fof(f612,plain,(
% 6.46/1.25    sK1 = k5_relat_1(sK1,k6_relat_1(sK0))),
% 6.46/1.25    inference(superposition,[],[f202,f219])).
% 6.46/1.25  fof(f219,plain,(
% 6.46/1.25    sK0 = k2_relat_1(sK1)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f195,f179,f185,f120])).
% 6.46/1.25  fof(f185,plain,(
% 6.46/1.25    v2_funct_2(sK1,sK0)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f92,f94,f95,f151])).
% 6.46/1.25  fof(f179,plain,(
% 6.46/1.25    v5_relat_1(sK1,sK0)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f95,f138])).
% 6.46/1.25  fof(f202,plain,(
% 6.46/1.25    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f195,f109])).
% 6.46/1.25  fof(f109,plain,(
% 6.46/1.25    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 6.46/1.25    inference(cnf_transformation,[],[f42])).
% 6.46/1.25  fof(f42,plain,(
% 6.46/1.25    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 6.46/1.25    inference(ennf_transformation,[],[f16])).
% 6.46/1.25  fof(f16,axiom,(
% 6.46/1.25    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 6.46/1.25  fof(f4482,plain,(
% 6.46/1.25    k5_relat_1(k6_relat_1(sK0),k2_funct_1(sK2)) = k5_relat_1(k6_relat_1(sK0),k5_relat_1(sK1,k6_relat_1(sK0))) | (~spl4_10 | ~spl4_12)),
% 6.46/1.25    inference(forward_demodulation,[],[f4481,f4112])).
% 6.46/1.25  fof(f4112,plain,(
% 6.46/1.25    k6_relat_1(sK0) = k5_relat_1(k6_relat_1(sK0),k6_relat_1(sK0)) | (~spl4_10 | ~spl4_12)),
% 6.46/1.25    inference(forward_demodulation,[],[f4111,f662])).
% 6.46/1.25  fof(f662,plain,(
% 6.46/1.25    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_12),
% 6.46/1.25    inference(avatar_component_clause,[],[f660])).
% 6.46/1.25  fof(f660,plain,(
% 6.46/1.25    spl4_12 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 6.46/1.25    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 6.46/1.25  fof(f4111,plain,(
% 6.46/1.25    k5_relat_1(sK2,k2_funct_1(sK2)) = k5_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)),k6_relat_1(sK0)) | ~spl4_10),
% 6.46/1.25    inference(forward_demodulation,[],[f4105,f1476])).
% 6.46/1.25  fof(f1476,plain,(
% 6.46/1.25    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0))),
% 6.46/1.25    inference(superposition,[],[f516,f597])).
% 6.46/1.25  fof(f597,plain,(
% 6.46/1.25    sK0 = k2_relat_1(k2_funct_1(sK2))),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f505,f470,f477,f120])).
% 6.46/1.25  fof(f477,plain,(
% 6.46/1.25    v2_funct_2(k2_funct_1(sK2),sK0)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f283,f281,f280,f151])).
% 6.46/1.25  fof(f281,plain,(
% 6.46/1.25    v3_funct_2(k2_funct_1(sK2),sK0,sK0)),
% 6.46/1.25    inference(forward_demodulation,[],[f245,f247])).
% 6.46/1.25  fof(f245,plain,(
% 6.46/1.25    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f96,f97,f98,f99,f125])).
% 6.46/1.25  fof(f283,plain,(
% 6.46/1.25    v1_funct_1(k2_funct_1(sK2))),
% 6.46/1.25    inference(forward_demodulation,[],[f243,f247])).
% 6.46/1.25  fof(f243,plain,(
% 6.46/1.25    v1_funct_1(k2_funct_2(sK0,sK2))),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f96,f97,f98,f99,f123])).
% 6.46/1.25  fof(f470,plain,(
% 6.46/1.25    v5_relat_1(k2_funct_1(sK2),sK0)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f280,f138])).
% 6.46/1.25  fof(f516,plain,(
% 6.46/1.25    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(k2_relat_1(k2_funct_1(sK2))))),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f505,f109])).
% 6.46/1.25  fof(f4105,plain,(
% 6.46/1.25    k5_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)),k6_relat_1(sK0)) = k5_relat_1(sK2,k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0))) | ~spl4_10),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f505,f274,f3763,f113])).
% 6.46/1.25  fof(f113,plain,(
% 6.46/1.25    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 6.46/1.25    inference(cnf_transformation,[],[f46])).
% 6.46/1.25  fof(f46,plain,(
% 6.46/1.25    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 6.46/1.25    inference(ennf_transformation,[],[f13])).
% 6.46/1.25  fof(f13,axiom,(
% 6.46/1.25    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 6.46/1.25  fof(f3763,plain,(
% 6.46/1.25    v1_relat_1(k6_relat_1(sK0)) | ~spl4_10),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f116,f3671,f114])).
% 6.46/1.25  fof(f3671,plain,(
% 6.46/1.25    m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_10),
% 6.46/1.25    inference(forward_demodulation,[],[f3670,f640])).
% 6.46/1.25  fof(f640,plain,(
% 6.46/1.25    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | ~spl4_10),
% 6.46/1.25    inference(avatar_component_clause,[],[f638])).
% 6.46/1.25  fof(f638,plain,(
% 6.46/1.25    spl4_10 <=> k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 6.46/1.25    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 6.46/1.25  fof(f3670,plain,(
% 6.46/1.25    m1_subset_1(k5_relat_1(k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 6.46/1.25    inference(subsumption_resolution,[],[f3669,f201])).
% 6.46/1.25  fof(f3669,plain,(
% 6.46/1.25    m1_subset_1(k5_relat_1(k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1))),
% 6.46/1.25    inference(subsumption_resolution,[],[f3668,f198])).
% 6.46/1.25  fof(f3668,plain,(
% 6.46/1.25    m1_subset_1(k5_relat_1(k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1))),
% 6.46/1.25    inference(subsumption_resolution,[],[f3667,f92])).
% 6.46/1.25  fof(f3667,plain,(
% 6.46/1.25    m1_subset_1(k5_relat_1(k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1))),
% 6.46/1.25    inference(subsumption_resolution,[],[f3660,f95])).
% 6.46/1.25  fof(f3660,plain,(
% 6.46/1.25    m1_subset_1(k5_relat_1(k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1))),
% 6.46/1.25    inference(superposition,[],[f160,f363])).
% 6.46/1.25  fof(f363,plain,(
% 6.46/1.25    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f92,f201,f95,f198,f158])).
% 6.46/1.25  fof(f158,plain,(
% 6.46/1.25    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 6.46/1.25    inference(cnf_transformation,[],[f78])).
% 6.46/1.25  fof(f78,plain,(
% 6.46/1.25    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.46/1.25    inference(flattening,[],[f77])).
% 6.46/1.25  fof(f77,plain,(
% 6.46/1.25    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.46/1.25    inference(ennf_transformation,[],[f33])).
% 6.46/1.25  fof(f33,axiom,(
% 6.46/1.25    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 6.46/1.25  fof(f160,plain,(
% 6.46/1.25    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.46/1.25    inference(cnf_transformation,[],[f80])).
% 6.46/1.25  fof(f80,plain,(
% 6.46/1.25    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.46/1.25    inference(flattening,[],[f79])).
% 6.46/1.25  fof(f79,plain,(
% 6.46/1.25    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.46/1.25    inference(ennf_transformation,[],[f30])).
% 6.46/1.25  fof(f30,axiom,(
% 6.46/1.25    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 6.46/1.25  fof(f4481,plain,(
% 6.46/1.25    k5_relat_1(k6_relat_1(sK0),k5_relat_1(sK1,k6_relat_1(sK0))) = k5_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(sK0)),k2_funct_1(sK2)) | (~spl4_10 | ~spl4_12)),
% 6.46/1.25    inference(forward_demodulation,[],[f4480,f3681])).
% 6.46/1.25  fof(f3681,plain,(
% 6.46/1.25    k6_relat_1(sK0) = k5_relat_1(sK1,sK2) | ~spl4_10),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f1489,f1483,f3671,f156])).
% 6.46/1.25  fof(f156,plain,(
% 6.46/1.25    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.46/1.25    inference(cnf_transformation,[],[f91])).
% 6.46/1.25  fof(f1483,plain,(
% 6.46/1.25    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0))),
% 6.46/1.25    inference(superposition,[],[f170,f262])).
% 6.46/1.25  fof(f262,plain,(
% 6.46/1.25    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f92,f96,f95,f99,f158])).
% 6.46/1.25  fof(f170,plain,(
% 6.46/1.25    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))),
% 6.46/1.25    inference(forward_demodulation,[],[f100,f103])).
% 6.46/1.25  fof(f103,plain,(
% 6.46/1.25    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 6.46/1.25    inference(cnf_transformation,[],[f35])).
% 6.46/1.25  fof(f35,axiom,(
% 6.46/1.25    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 6.46/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 6.46/1.25  fof(f100,plain,(
% 6.46/1.25    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 6.46/1.25    inference(cnf_transformation,[],[f83])).
% 6.46/1.25  fof(f1489,plain,(
% 6.46/1.25    m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 6.46/1.25    inference(subsumption_resolution,[],[f1488,f92])).
% 6.46/1.25  fof(f1488,plain,(
% 6.46/1.25    m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 6.46/1.25    inference(subsumption_resolution,[],[f1487,f95])).
% 6.46/1.25  fof(f1487,plain,(
% 6.46/1.25    m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 6.46/1.25    inference(subsumption_resolution,[],[f1486,f96])).
% 6.46/1.25  fof(f1486,plain,(
% 6.46/1.25    m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 6.46/1.25    inference(subsumption_resolution,[],[f1485,f99])).
% 6.46/1.25  fof(f1485,plain,(
% 6.46/1.25    m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 6.46/1.25    inference(superposition,[],[f160,f262])).
% 6.46/1.25  fof(f4480,plain,(
% 6.46/1.25    k5_relat_1(k6_relat_1(sK0),k5_relat_1(sK1,k6_relat_1(sK0))) = k5_relat_1(k5_relat_1(k6_relat_1(sK0),k5_relat_1(sK1,sK2)),k2_funct_1(sK2)) | (~spl4_10 | ~spl4_12)),
% 6.46/1.25    inference(forward_demodulation,[],[f4479,f662])).
% 6.46/1.25  fof(f4479,plain,(
% 6.46/1.25    k5_relat_1(k5_relat_1(k6_relat_1(sK0),k5_relat_1(sK1,sK2)),k2_funct_1(sK2)) = k5_relat_1(k6_relat_1(sK0),k5_relat_1(sK1,k5_relat_1(sK2,k2_funct_1(sK2)))) | ~spl4_10),
% 6.46/1.25    inference(forward_demodulation,[],[f3881,f587])).
% 6.46/1.25  fof(f587,plain,(
% 6.46/1.25    k5_relat_1(k5_relat_1(sK1,sK2),k2_funct_1(sK2)) = k5_relat_1(sK1,k5_relat_1(sK2,k2_funct_1(sK2)))),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f274,f195,f505,f113])).
% 6.46/1.25  fof(f3881,plain,(
% 6.46/1.25    k5_relat_1(k5_relat_1(k6_relat_1(sK0),k5_relat_1(sK1,sK2)),k2_funct_1(sK2)) = k5_relat_1(k6_relat_1(sK0),k5_relat_1(k5_relat_1(sK1,sK2),k2_funct_1(sK2))) | ~spl4_10),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f1543,f505,f3763,f113])).
% 6.46/1.25  fof(f1543,plain,(
% 6.46/1.25    v1_relat_1(k5_relat_1(sK1,sK2))),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f116,f1489,f114])).
% 6.46/1.25  fof(f313,plain,(
% 6.46/1.25    sK2 = k2_funct_1(k2_funct_1(sK2))),
% 6.46/1.25    inference(unit_resulting_resolution,[],[f257,f96,f274,f115])).
% 6.46/1.25  fof(f115,plain,(
% 6.46/1.25    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.46/1.25    inference(cnf_transformation,[],[f49])).
% 6.46/1.26  fof(f49,plain,(
% 6.46/1.26    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.46/1.26    inference(flattening,[],[f48])).
% 6.46/1.26  fof(f48,plain,(
% 6.46/1.26    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.46/1.26    inference(ennf_transformation,[],[f17])).
% 6.46/1.26  fof(f17,axiom,(
% 6.46/1.26    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 6.46/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 6.46/1.26  fof(f257,plain,(
% 6.46/1.26    v2_funct_1(sK2)),
% 6.46/1.26    inference(unit_resulting_resolution,[],[f96,f98,f99,f150])).
% 6.46/1.26  fof(f150,plain,(
% 6.46/1.26    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.46/1.26    inference(cnf_transformation,[],[f70])).
% 6.46/1.26  fof(f688,plain,(
% 6.46/1.26    spl4_11),
% 6.46/1.26    inference(avatar_contradiction_clause,[],[f687])).
% 6.46/1.26  fof(f687,plain,(
% 6.46/1.26    $false | spl4_11),
% 6.46/1.26    inference(subsumption_resolution,[],[f686,f658])).
% 6.46/1.26  fof(f658,plain,(
% 6.46/1.26    sK0 != k9_relat_1(sK2,sK0) | spl4_11),
% 6.46/1.26    inference(avatar_component_clause,[],[f656])).
% 6.46/1.26  fof(f656,plain,(
% 6.46/1.26    spl4_11 <=> sK0 = k9_relat_1(sK2,sK0)),
% 6.46/1.26    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 6.46/1.26  fof(f686,plain,(
% 6.46/1.26    sK0 = k9_relat_1(sK2,sK0)),
% 6.46/1.26    inference(forward_demodulation,[],[f682,f317])).
% 6.46/1.26  fof(f682,plain,(
% 6.46/1.26    k9_relat_1(sK2,sK0) = k2_relat_1(sK2)),
% 6.46/1.26    inference(superposition,[],[f314,f316])).
% 6.46/1.26  fof(f316,plain,(
% 6.46/1.26    sK2 = k7_relat_1(sK2,sK0)),
% 6.46/1.26    inference(unit_resulting_resolution,[],[f274,f250,f119])).
% 6.46/1.26  fof(f119,plain,(
% 6.46/1.26    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 6.46/1.26    inference(cnf_transformation,[],[f53])).
% 6.46/1.26  fof(f53,plain,(
% 6.46/1.26    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.46/1.26    inference(flattening,[],[f52])).
% 6.46/1.26  fof(f52,plain,(
% 6.46/1.26    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 6.46/1.26    inference(ennf_transformation,[],[f12])).
% 6.46/1.26  fof(f12,axiom,(
% 6.46/1.26    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 6.46/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 6.46/1.26  fof(f250,plain,(
% 6.46/1.26    v4_relat_1(sK2,sK0)),
% 6.46/1.26    inference(unit_resulting_resolution,[],[f99,f137])).
% 6.46/1.26  fof(f137,plain,(
% 6.46/1.26    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.46/1.26    inference(cnf_transformation,[],[f64])).
% 6.46/1.26  fof(f314,plain,(
% 6.46/1.26    ( ! [X0] : (k9_relat_1(sK2,X0) = k2_relat_1(k7_relat_1(sK2,X0))) )),
% 6.46/1.26    inference(unit_resulting_resolution,[],[f274,f118])).
% 6.46/1.26  fof(f118,plain,(
% 6.46/1.26    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 6.46/1.26    inference(cnf_transformation,[],[f51])).
% 6.46/1.26  fof(f51,plain,(
% 6.46/1.26    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.46/1.26    inference(ennf_transformation,[],[f11])).
% 6.46/1.26  fof(f11,axiom,(
% 6.46/1.26    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 6.46/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 6.46/1.26  fof(f681,plain,(
% 6.46/1.26    spl4_8),
% 6.46/1.26    inference(avatar_contradiction_clause,[],[f680])).
% 6.46/1.26  fof(f680,plain,(
% 6.46/1.26    $false | spl4_8),
% 6.46/1.26    inference(subsumption_resolution,[],[f679,f625])).
% 6.46/1.26  fof(f625,plain,(
% 6.46/1.26    sK0 != k9_relat_1(sK1,sK0) | spl4_8),
% 6.46/1.26    inference(avatar_component_clause,[],[f623])).
% 6.46/1.26  fof(f623,plain,(
% 6.46/1.26    spl4_8 <=> sK0 = k9_relat_1(sK1,sK0)),
% 6.46/1.26    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 6.46/1.26  fof(f679,plain,(
% 6.46/1.26    sK0 = k9_relat_1(sK1,sK0)),
% 6.46/1.26    inference(forward_demodulation,[],[f675,f219])).
% 6.46/1.26  fof(f675,plain,(
% 6.46/1.26    k9_relat_1(sK1,sK0) = k2_relat_1(sK1)),
% 6.46/1.26    inference(superposition,[],[f217,f218])).
% 6.46/1.26  fof(f218,plain,(
% 6.46/1.26    sK1 = k7_relat_1(sK1,sK0)),
% 6.46/1.26    inference(unit_resulting_resolution,[],[f195,f178,f119])).
% 6.46/1.26  fof(f178,plain,(
% 6.46/1.26    v4_relat_1(sK1,sK0)),
% 6.46/1.26    inference(unit_resulting_resolution,[],[f95,f137])).
% 6.46/1.26  fof(f217,plain,(
% 6.46/1.26    ( ! [X0] : (k9_relat_1(sK1,X0) = k2_relat_1(k7_relat_1(sK1,X0))) )),
% 6.46/1.26    inference(unit_resulting_resolution,[],[f195,f118])).
% 6.46/1.26  fof(f663,plain,(
% 6.46/1.26    ~spl4_11 | spl4_12 | spl4_2),
% 6.46/1.26    inference(avatar_split_clause,[],[f654,f229,f660,f656])).
% 6.46/1.26  fof(f654,plain,(
% 6.46/1.26    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | sK0 != k9_relat_1(sK2,sK0) | spl4_2),
% 6.46/1.26    inference(forward_demodulation,[],[f653,f103])).
% 6.46/1.26  fof(f653,plain,(
% 6.46/1.26    sK0 != k9_relat_1(sK2,sK0) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | spl4_2),
% 6.46/1.26    inference(subsumption_resolution,[],[f652,f96])).
% 6.46/1.26  fof(f652,plain,(
% 6.46/1.26    sK0 != k9_relat_1(sK2,sK0) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | spl4_2),
% 6.46/1.26    inference(subsumption_resolution,[],[f651,f97])).
% 6.46/1.26  fof(f651,plain,(
% 6.46/1.26    sK0 != k9_relat_1(sK2,sK0) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl4_2),
% 6.46/1.26    inference(subsumption_resolution,[],[f650,f99])).
% 6.46/1.26  fof(f650,plain,(
% 6.46/1.26    sK0 != k9_relat_1(sK2,sK0) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl4_2),
% 6.46/1.26    inference(subsumption_resolution,[],[f649,f257])).
% 6.46/1.26  fof(f649,plain,(
% 6.46/1.26    sK0 != k9_relat_1(sK2,sK0) | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl4_2),
% 6.46/1.26    inference(subsumption_resolution,[],[f647,f231])).
% 6.46/1.26  fof(f647,plain,(
% 6.46/1.26    sK0 != k9_relat_1(sK2,sK0) | k1_xboole_0 = sK0 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 6.46/1.26    inference(superposition,[],[f152,f278])).
% 6.46/1.26  fof(f278,plain,(
% 6.46/1.26    k2_relset_1(sK0,sK0,sK2) = k9_relat_1(sK2,sK0)),
% 6.46/1.26    inference(forward_demodulation,[],[f252,f259])).
% 6.46/1.26  fof(f259,plain,(
% 6.46/1.26    ( ! [X0] : (k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0)) )),
% 6.46/1.26    inference(unit_resulting_resolution,[],[f99,f155])).
% 6.46/1.26  fof(f155,plain,(
% 6.46/1.26    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 6.46/1.26    inference(cnf_transformation,[],[f74])).
% 6.46/1.26  fof(f74,plain,(
% 6.46/1.26    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.46/1.26    inference(ennf_transformation,[],[f22])).
% 6.46/1.26  fof(f22,axiom,(
% 6.46/1.26    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 6.46/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 6.46/1.26  fof(f252,plain,(
% 6.46/1.26    k2_relset_1(sK0,sK0,sK2) = k7_relset_1(sK0,sK0,sK2,sK0)),
% 6.46/1.26    inference(unit_resulting_resolution,[],[f99,f139])).
% 6.46/1.26  fof(f139,plain,(
% 6.46/1.26    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) )),
% 6.46/1.26    inference(cnf_transformation,[],[f65])).
% 6.46/1.26  fof(f65,plain,(
% 6.46/1.26    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.46/1.26    inference(ennf_transformation,[],[f25])).
% 6.46/1.26  fof(f25,axiom,(
% 6.46/1.26    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 6.46/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 6.46/1.26  fof(f152,plain,(
% 6.46/1.26    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.46/1.26    inference(cnf_transformation,[],[f72])).
% 6.46/1.26  fof(f72,plain,(
% 6.46/1.26    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.46/1.26    inference(flattening,[],[f71])).
% 6.46/1.26  fof(f71,plain,(
% 6.46/1.26    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.46/1.26    inference(ennf_transformation,[],[f36])).
% 6.46/1.26  fof(f36,axiom,(
% 6.46/1.26    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 6.46/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 6.46/1.26  fof(f641,plain,(
% 6.46/1.26    ~spl4_8 | spl4_10 | spl4_2),
% 6.46/1.26    inference(avatar_split_clause,[],[f636,f229,f638,f623])).
% 6.46/1.26  fof(f636,plain,(
% 6.46/1.26    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | sK0 != k9_relat_1(sK1,sK0) | spl4_2),
% 6.46/1.26    inference(forward_demodulation,[],[f635,f103])).
% 6.46/1.26  fof(f635,plain,(
% 6.46/1.26    sK0 != k9_relat_1(sK1,sK0) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | spl4_2),
% 6.46/1.26    inference(subsumption_resolution,[],[f634,f92])).
% 6.46/1.26  fof(f634,plain,(
% 6.46/1.26    sK0 != k9_relat_1(sK1,sK0) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | ~v1_funct_1(sK1) | spl4_2),
% 6.46/1.26    inference(subsumption_resolution,[],[f633,f93])).
% 6.46/1.26  fof(f633,plain,(
% 6.46/1.26    sK0 != k9_relat_1(sK1,sK0) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | spl4_2),
% 6.46/1.26    inference(subsumption_resolution,[],[f632,f95])).
% 6.46/1.26  fof(f632,plain,(
% 6.46/1.26    sK0 != k9_relat_1(sK1,sK0) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | spl4_2),
% 6.46/1.26    inference(subsumption_resolution,[],[f631,f184])).
% 6.46/1.26  fof(f184,plain,(
% 6.46/1.26    v2_funct_1(sK1)),
% 6.46/1.26    inference(unit_resulting_resolution,[],[f92,f94,f95,f150])).
% 6.46/1.26  fof(f631,plain,(
% 6.46/1.26    sK0 != k9_relat_1(sK1,sK0) | ~v2_funct_1(sK1) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | spl4_2),
% 6.46/1.26    inference(subsumption_resolution,[],[f615,f231])).
% 6.46/1.26  fof(f615,plain,(
% 6.46/1.26    sK0 != k9_relat_1(sK1,sK0) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 6.46/1.26    inference(superposition,[],[f153,f197])).
% 6.46/1.26  fof(f197,plain,(
% 6.46/1.26    k2_relset_1(sK0,sK0,sK1) = k9_relat_1(sK1,sK0)),
% 6.46/1.26    inference(forward_demodulation,[],[f180,f186])).
% 6.46/1.26  fof(f186,plain,(
% 6.46/1.26    ( ! [X0] : (k7_relset_1(sK0,sK0,sK1,X0) = k9_relat_1(sK1,X0)) )),
% 6.46/1.26    inference(unit_resulting_resolution,[],[f95,f155])).
% 6.46/1.26  fof(f180,plain,(
% 6.46/1.26    k2_relset_1(sK0,sK0,sK1) = k7_relset_1(sK0,sK0,sK1,sK0)),
% 6.46/1.26    inference(unit_resulting_resolution,[],[f95,f139])).
% 6.46/1.26  fof(f153,plain,(
% 6.46/1.26    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.46/1.26    inference(cnf_transformation,[],[f72])).
% 6.46/1.26  fof(f232,plain,(
% 6.46/1.26    spl4_1 | ~spl4_2),
% 6.46/1.26    inference(avatar_split_clause,[],[f223,f229,f225])).
% 6.46/1.26  fof(f223,plain,(
% 6.46/1.26    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 6.46/1.26    inference(subsumption_resolution,[],[f221,f195])).
% 6.46/1.26  fof(f221,plain,(
% 6.46/1.26    k1_xboole_0 != sK0 | k1_xboole_0 = sK1 | ~v1_relat_1(sK1)),
% 6.46/1.26    inference(superposition,[],[f112,f219])).
% 6.46/1.26  % SZS output end Proof for theBenchmark
% 6.46/1.26  % (13874)------------------------------
% 6.46/1.26  % (13874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.46/1.26  % (13874)Termination reason: Refutation
% 6.46/1.26  
% 6.46/1.26  % (13874)Memory used [KB]: 13944
% 6.46/1.26  % (13874)Time elapsed: 0.292 s
% 6.46/1.26  % (13874)------------------------------
% 6.46/1.26  % (13874)------------------------------
% 6.46/1.26  % (13805)Success in time 0.886 s
%------------------------------------------------------------------------------
