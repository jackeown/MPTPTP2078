%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 192 expanded)
%              Number of leaves         :   32 (  89 expanded)
%              Depth                    :    8
%              Number of atoms          :  370 ( 876 expanded)
%              Number of equality atoms :   69 ( 155 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f284,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f95,f99,f103,f107,f111,f115,f134,f164,f171,f260,f274,f277,f280,f282,f283])).

fof(f283,plain,
    ( k1_xboole_0 != sK1
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f282,plain,
    ( ~ spl7_2
    | spl7_7
    | spl7_23 ),
    inference(avatar_split_clause,[],[f281,f272,f113,f93])).

fof(f93,plain,
    ( spl7_2
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f113,plain,
    ( spl7_7
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f272,plain,
    ( spl7_23
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f281,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK3,sK0)
    | spl7_23 ),
    inference(resolution,[],[f273,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f273,plain,
    ( ~ r2_hidden(sK3,sK0)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f272])).

fof(f280,plain,
    ( ~ spl7_3
    | spl7_22 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | ~ spl7_3
    | spl7_22 ),
    inference(subsumption_resolution,[],[f98,f278])).

fof(f278,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | spl7_22 ),
    inference(resolution,[],[f269,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f269,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | spl7_22 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl7_22
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f98,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl7_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f277,plain,
    ( ~ spl7_3
    | spl7_21 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | ~ spl7_3
    | spl7_21 ),
    inference(subsumption_resolution,[],[f98,f275])).

fof(f275,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_21 ),
    inference(resolution,[],[f266,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f266,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl7_21
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f274,plain,
    ( ~ spl7_21
    | ~ spl7_22
    | ~ spl7_5
    | ~ spl7_23
    | ~ spl7_13
    | spl7_20 ),
    inference(avatar_split_clause,[],[f263,f258,f168,f272,f105,f268,f265])).

fof(f105,plain,
    ( spl7_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f168,plain,
    ( spl7_13
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f258,plain,
    ( spl7_20
  <=> k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f263,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl7_13
    | spl7_20 ),
    inference(forward_demodulation,[],[f262,f169])).

fof(f169,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f168])).

fof(f262,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | spl7_20 ),
    inference(trivial_inequality_removal,[],[f261])).

fof(f261,plain,
    ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,sK3)
    | ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | spl7_20 ),
    inference(superposition,[],[f259,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f259,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f258])).

fof(f260,plain,
    ( spl7_7
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_3
    | ~ spl7_20
    | spl7_1
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f253,f105,f89,f258,f97,f101,f93,f113])).

fof(f101,plain,
    ( spl7_4
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f89,plain,
    ( spl7_1
  <=> k3_funct_2(sK0,sK1,sK2,sK3) = k7_partfun1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f253,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK3,sK0)
    | v1_xboole_0(sK0)
    | spl7_1
    | ~ spl7_5 ),
    inference(superposition,[],[f90,f252])).

fof(f252,plain,
    ( ! [X2,X0,X1] :
        ( k3_funct_2(X1,X2,sK2,X0) = k1_funct_1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_2(sK2,X1,X2)
        | ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1) )
    | ~ spl7_5 ),
    inference(resolution,[],[f80,f106])).

fof(f106,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f90,plain,
    ( k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f171,plain,
    ( ~ spl7_3
    | spl7_13
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f166,f162,f168,f97])).

fof(f162,plain,
    ( spl7_12
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f166,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_12 ),
    inference(superposition,[],[f68,f163])).

fof(f163,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f162])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f164,plain,
    ( ~ spl7_3
    | spl7_11
    | spl7_12
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f155,f101,f162,f159,f97])).

fof(f159,plain,
    ( spl7_11
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f155,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_4 ),
    inference(resolution,[],[f70,f102])).

fof(f102,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f134,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f130,f132])).

fof(f132,plain,
    ( spl7_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f130,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f129,f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f129,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f66,f57])).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f115,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f50,f113])).

fof(f50,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f39,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                    & m1_subset_1(X3,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_partfun1(X1,X2,X3) != k3_funct_2(sK0,X1,X2,X3)
                  & m1_subset_1(X3,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
              & v1_funct_2(X2,sK0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k7_partfun1(X1,X2,X3) != k3_funct_2(sK0,X1,X2,X3)
                & m1_subset_1(X3,sK0) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
            & v1_funct_2(X2,sK0,X1)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k3_funct_2(sK0,sK1,X2,X3) != k7_partfun1(sK1,X2,X3)
              & m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X2,sK0,sK1)
          & v1_funct_1(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k3_funct_2(sK0,sK1,X2,X3) != k7_partfun1(sK1,X2,X3)
            & m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X2,sK0,sK1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k3_funct_2(sK0,sK1,sK2,X3) != k7_partfun1(sK1,sK2,X3)
          & m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X3] :
        ( k3_funct_2(sK0,sK1,sK2,X3) != k7_partfun1(sK1,sK2,X3)
        & m1_subset_1(X3,sK0) )
   => ( k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)
      & m1_subset_1(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

fof(f111,plain,(
    ~ spl7_6 ),
    inference(avatar_split_clause,[],[f51,f109])).

fof(f109,plain,
    ( spl7_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f51,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f107,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f52,f105])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f103,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f53,f101])).

fof(f53,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f99,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f54,f97])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f95,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f55,f93])).

fof(f55,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f56,f89])).

fof(f56,plain,(
    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:37:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (21913)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (21919)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (21927)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (21913)Refutation not found, incomplete strategy% (21913)------------------------------
% 0.21/0.51  % (21913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21914)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (21923)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (21919)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (21921)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f91,f95,f99,f103,f107,f111,f115,f134,f164,f171,f260,f274,f277,f280,f282,f283])).
% 0.21/0.51  fof(f283,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | v1_xboole_0(sK1) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f282,plain,(
% 0.21/0.51    ~spl7_2 | spl7_7 | spl7_23),
% 0.21/0.51    inference(avatar_split_clause,[],[f281,f272,f113,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl7_2 <=> m1_subset_1(sK3,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl7_7 <=> v1_xboole_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    spl7_23 <=> r2_hidden(sK3,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.21/0.51  fof(f281,plain,(
% 0.21/0.51    v1_xboole_0(sK0) | ~m1_subset_1(sK3,sK0) | spl7_23),
% 0.21/0.51    inference(resolution,[],[f273,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    ~r2_hidden(sK3,sK0) | spl7_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f272])).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    ~spl7_3 | spl7_22),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f279])).
% 0.21/0.51  fof(f279,plain,(
% 0.21/0.51    $false | (~spl7_3 | spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f98,f278])).
% 0.21/0.51  fof(f278,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | spl7_22),
% 0.21/0.51    inference(resolution,[],[f269,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    ~v5_relat_1(sK2,sK1) | spl7_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f268])).
% 0.21/0.51  fof(f268,plain,(
% 0.21/0.51    spl7_22 <=> v5_relat_1(sK2,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl7_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.51  fof(f277,plain,(
% 0.21/0.51    ~spl7_3 | spl7_21),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f276])).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    $false | (~spl7_3 | spl7_21)),
% 0.21/0.51    inference(subsumption_resolution,[],[f98,f275])).
% 0.21/0.51  fof(f275,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_21),
% 0.21/0.51    inference(resolution,[],[f266,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | spl7_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f265])).
% 0.21/0.51  fof(f265,plain,(
% 0.21/0.51    spl7_21 <=> v1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    ~spl7_21 | ~spl7_22 | ~spl7_5 | ~spl7_23 | ~spl7_13 | spl7_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f263,f258,f168,f272,f105,f268,f265])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl7_5 <=> v1_funct_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    spl7_13 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    spl7_20 <=> k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.51  fof(f263,plain,(
% 0.21/0.51    ~r2_hidden(sK3,sK0) | ~v1_funct_1(sK2) | ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | (~spl7_13 | spl7_20)),
% 0.21/0.51    inference(forward_demodulation,[],[f262,f169])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK2) | ~spl7_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f168])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    ~r2_hidden(sK3,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | spl7_20),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f261])).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    k1_funct_1(sK2,sK3) != k1_funct_1(sK2,sK3) | ~r2_hidden(sK3,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | spl7_20),
% 0.21/0.51    inference(superposition,[],[f259,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | spl7_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f258])).
% 0.21/0.51  fof(f260,plain,(
% 0.21/0.51    spl7_7 | ~spl7_2 | ~spl7_4 | ~spl7_3 | ~spl7_20 | spl7_1 | ~spl7_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f253,f105,f89,f258,f97,f101,f93,f113])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    spl7_4 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    spl7_1 <=> k3_funct_2(sK0,sK1,sK2,sK3) = k7_partfun1(sK1,sK2,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK3,sK0) | v1_xboole_0(sK0) | (spl7_1 | ~spl7_5)),
% 0.21/0.51    inference(superposition,[],[f90,f252])).
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_funct_2(X1,X2,sK2,X0) = k1_funct_1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(sK2,X1,X2) | ~m1_subset_1(X0,X1) | v1_xboole_0(X1)) ) | ~spl7_5),
% 0.21/0.51    inference(resolution,[],[f80,f106])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    v1_funct_1(sK2) | ~spl7_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f105])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) | spl7_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f89])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    ~spl7_3 | spl7_13 | ~spl7_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f166,f162,f168,f97])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    spl7_12 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_12),
% 0.21/0.51    inference(superposition,[],[f68,f163])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f162])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ~spl7_3 | spl7_11 | spl7_12 | ~spl7_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f155,f101,f162,f159,f97])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    spl7_11 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_4),
% 0.21/0.51    inference(resolution,[],[f70,f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    v1_funct_2(sK2,sK0,sK1) | ~spl7_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f101])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    spl7_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f130,f132])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    spl7_10 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    inference(resolution,[],[f129,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.52    inference(rectify,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(resolution,[],[f66,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    ~spl7_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f50,f113])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ~v1_xboole_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    (((k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) & m1_subset_1(sK3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f39,f38,f37,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(sK0,X1,X2,X3) & m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(sK0,X1,X2,X3) & m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (k3_funct_2(sK0,sK1,X2,X3) != k7_partfun1(sK1,X2,X3) & m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) & ~v1_xboole_0(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ? [X2] : (? [X3] : (k3_funct_2(sK0,sK1,X2,X3) != k7_partfun1(sK1,X2,X3) & m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) => (? [X3] : (k3_funct_2(sK0,sK1,sK2,X3) != k7_partfun1(sK1,sK2,X3) & m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ? [X3] : (k3_funct_2(sK0,sK1,sK2,X3) != k7_partfun1(sK1,sK2,X3) & m1_subset_1(X3,sK0)) => (k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) & m1_subset_1(sK3,sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f15])).
% 0.21/0.52  fof(f15,conjecture,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ~spl7_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f51,f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    spl7_6 <=> v1_xboole_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ~v1_xboole_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    spl7_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f52,f105])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    v1_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    spl7_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f53,f101])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl7_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f54,f97])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    spl7_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f55,f93])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    m1_subset_1(sK3,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ~spl7_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f56,f89])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (21919)------------------------------
% 0.21/0.52  % (21919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21919)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (21919)Memory used [KB]: 10746
% 0.21/0.52  % (21919)Time elapsed: 0.084 s
% 0.21/0.52  % (21919)------------------------------
% 0.21/0.52  % (21919)------------------------------
% 0.21/0.52  % (21912)Success in time 0.156 s
%------------------------------------------------------------------------------
