%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 141 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :  249 ( 517 expanded)
%              Number of equality atoms :   50 (  90 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f70,f76,f89,f94,f101,f108,f117,f120,f126])).

fof(f126,plain,
    ( spl4_10
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f124,f115,f56,f92])).

fof(f92,plain,
    ( spl4_10
  <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f56,plain,
    ( spl4_3
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f115,plain,
    ( spl4_14
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f124,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(resolution,[],[f116,f57])).

fof(f57,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f115])).

fof(f120,plain,
    ( ~ spl4_4
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl4_4
    | spl4_13 ),
    inference(subsumption_resolution,[],[f61,f118])).

fof(f118,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_13 ),
    inference(resolution,[],[f112,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f112,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_13
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f61,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f117,plain,
    ( ~ spl4_13
    | ~ spl4_6
    | spl4_14
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f109,f105,f115,f68,f111])).

fof(f68,plain,
    ( spl4_6
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f105,plain,
    ( spl4_12
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_12 ),
    inference(superposition,[],[f31,f106])).

fof(f106,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f108,plain,
    ( ~ spl4_4
    | spl4_12
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f103,f97,f105,f60])).

fof(f97,plain,
    ( spl4_11
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f103,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_11 ),
    inference(superposition,[],[f33,f98])).

fof(f98,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f101,plain,
    ( spl4_11
    | spl4_2
    | ~ spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f95,f60,f64,f52,f97])).

fof(f52,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f64,plain,
    ( spl4_5
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f95,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f36,f61])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f94,plain,
    ( ~ spl4_4
    | ~ spl4_10
    | spl4_9 ),
    inference(avatar_split_clause,[],[f90,f87,f92,f60])).

fof(f87,plain,
    ( spl4_9
  <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f90,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_9 ),
    inference(superposition,[],[f88,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f88,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,
    ( ~ spl4_9
    | spl4_1
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f85,f74,f48,f87])).

fof(f48,plain,
    ( spl4_1
  <=> r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f74,plain,
    ( spl4_7
  <=> m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f85,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f77,f49])).

fof(f49,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f77,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_relset_1(sK0,sK1,sK3)) )
    | ~ spl4_7 ),
    inference(resolution,[],[f75,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f75,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f76,plain,
    ( spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f72,f60,f74])).

fof(f72,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f35,f61])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f70,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f24,f68])).

fof(f24,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1)
    & k1_xboole_0 != sK1
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1)
      & k1_xboole_0 != sK1
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),X1)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f66,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f25,f64])).

fof(f25,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f27,f56])).

fof(f27,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f28,f52])).

fof(f28,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f29,f48])).

fof(f29,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.40  % (12366)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.41  % (12366)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f127,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f70,f76,f89,f94,f101,f108,f117,f120,f126])).
% 0.20/0.41  fof(f126,plain,(
% 0.20/0.41    spl4_10 | ~spl4_3 | ~spl4_14),
% 0.20/0.41    inference(avatar_split_clause,[],[f124,f115,f56,f92])).
% 0.20/0.41  fof(f92,plain,(
% 0.20/0.41    spl4_10 <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.41  fof(f56,plain,(
% 0.20/0.41    spl4_3 <=> r2_hidden(sK2,sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.41  fof(f115,plain,(
% 0.20/0.41    spl4_14 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.41  fof(f124,plain,(
% 0.20/0.41    r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) | (~spl4_3 | ~spl4_14)),
% 0.20/0.41    inference(resolution,[],[f116,f57])).
% 0.20/0.41  fof(f57,plain,(
% 0.20/0.41    r2_hidden(sK2,sK0) | ~spl4_3),
% 0.20/0.41    inference(avatar_component_clause,[],[f56])).
% 0.20/0.41  fof(f116,plain,(
% 0.20/0.41    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))) ) | ~spl4_14),
% 0.20/0.41    inference(avatar_component_clause,[],[f115])).
% 0.20/0.41  fof(f120,plain,(
% 0.20/0.41    ~spl4_4 | spl4_13),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f119])).
% 0.20/0.41  fof(f119,plain,(
% 0.20/0.41    $false | (~spl4_4 | spl4_13)),
% 0.20/0.41    inference(subsumption_resolution,[],[f61,f118])).
% 0.20/0.41  fof(f118,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_13),
% 0.20/0.41    inference(resolution,[],[f112,f32])).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.41    inference(ennf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.41  fof(f112,plain,(
% 0.20/0.41    ~v1_relat_1(sK3) | spl4_13),
% 0.20/0.41    inference(avatar_component_clause,[],[f111])).
% 0.20/0.41  fof(f111,plain,(
% 0.20/0.41    spl4_13 <=> v1_relat_1(sK3)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.41  fof(f61,plain,(
% 0.20/0.41    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.20/0.41    inference(avatar_component_clause,[],[f60])).
% 0.20/0.41  fof(f60,plain,(
% 0.20/0.41    spl4_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.41  fof(f117,plain,(
% 0.20/0.41    ~spl4_13 | ~spl4_6 | spl4_14 | ~spl4_12),
% 0.20/0.41    inference(avatar_split_clause,[],[f109,f105,f115,f68,f111])).
% 0.20/0.41  fof(f68,plain,(
% 0.20/0.41    spl4_6 <=> v1_funct_1(sK3)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.41  fof(f105,plain,(
% 0.20/0.41    spl4_12 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.41  fof(f109,plain,(
% 0.20/0.41    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl4_12),
% 0.20/0.41    inference(superposition,[],[f31,f106])).
% 0.20/0.41  fof(f106,plain,(
% 0.20/0.41    sK0 = k1_relat_1(sK3) | ~spl4_12),
% 0.20/0.41    inference(avatar_component_clause,[],[f105])).
% 0.20/0.41  fof(f31,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.41    inference(flattening,[],[f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.41    inference(ennf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.20/0.41  fof(f108,plain,(
% 0.20/0.41    ~spl4_4 | spl4_12 | ~spl4_11),
% 0.20/0.41    inference(avatar_split_clause,[],[f103,f97,f105,f60])).
% 0.20/0.41  fof(f97,plain,(
% 0.20/0.41    spl4_11 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.41  fof(f103,plain,(
% 0.20/0.41    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_11),
% 0.20/0.41    inference(superposition,[],[f33,f98])).
% 0.20/0.41  fof(f98,plain,(
% 0.20/0.41    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_11),
% 0.20/0.41    inference(avatar_component_clause,[],[f97])).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.41    inference(ennf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.41  fof(f101,plain,(
% 0.20/0.41    spl4_11 | spl4_2 | ~spl4_5 | ~spl4_4),
% 0.20/0.41    inference(avatar_split_clause,[],[f95,f60,f64,f52,f97])).
% 0.20/0.41  fof(f52,plain,(
% 0.20/0.41    spl4_2 <=> k1_xboole_0 = sK1),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.41  fof(f64,plain,(
% 0.20/0.41    spl4_5 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.41  fof(f95,plain,(
% 0.20/0.41    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_4),
% 0.20/0.41    inference(resolution,[],[f36,f61])).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.41    inference(cnf_transformation,[],[f23])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.41    inference(nnf_transformation,[],[f20])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.41    inference(flattening,[],[f19])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.41    inference(ennf_transformation,[],[f7])).
% 0.20/0.41  fof(f7,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.41  fof(f94,plain,(
% 0.20/0.41    ~spl4_4 | ~spl4_10 | spl4_9),
% 0.20/0.41    inference(avatar_split_clause,[],[f90,f87,f92,f60])).
% 0.20/0.41  fof(f87,plain,(
% 0.20/0.41    spl4_9 <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.41  fof(f90,plain,(
% 0.20/0.41    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_9),
% 0.20/0.41    inference(superposition,[],[f88,f34])).
% 0.20/0.41  fof(f34,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.41  fof(f88,plain,(
% 0.20/0.41    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | spl4_9),
% 0.20/0.41    inference(avatar_component_clause,[],[f87])).
% 0.20/0.41  fof(f89,plain,(
% 0.20/0.41    ~spl4_9 | spl4_1 | ~spl4_7),
% 0.20/0.41    inference(avatar_split_clause,[],[f85,f74,f48,f87])).
% 0.20/0.41  fof(f48,plain,(
% 0.20/0.41    spl4_1 <=> r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.41  fof(f74,plain,(
% 0.20/0.41    spl4_7 <=> m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.41  fof(f85,plain,(
% 0.20/0.41    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | (spl4_1 | ~spl4_7)),
% 0.20/0.41    inference(resolution,[],[f77,f49])).
% 0.20/0.41  fof(f49,plain,(
% 0.20/0.41    ~r2_hidden(k1_funct_1(sK3,sK2),sK1) | spl4_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f48])).
% 0.20/0.41  fof(f77,plain,(
% 0.20/0.41    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,k2_relset_1(sK0,sK1,sK3))) ) | ~spl4_7),
% 0.20/0.41    inference(resolution,[],[f75,f30])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.41  fof(f75,plain,(
% 0.20/0.41    m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) | ~spl4_7),
% 0.20/0.41    inference(avatar_component_clause,[],[f74])).
% 0.20/0.41  fof(f76,plain,(
% 0.20/0.41    spl4_7 | ~spl4_4),
% 0.20/0.41    inference(avatar_split_clause,[],[f72,f60,f74])).
% 0.20/0.41  fof(f72,plain,(
% 0.20/0.41    m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) | ~spl4_4),
% 0.20/0.41    inference(resolution,[],[f35,f61])).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.20/0.41  fof(f70,plain,(
% 0.20/0.41    spl4_6),
% 0.20/0.41    inference(avatar_split_clause,[],[f24,f68])).
% 0.20/0.41  fof(f24,plain,(
% 0.20/0.41    v1_funct_1(sK3)),
% 0.20/0.41    inference(cnf_transformation,[],[f22])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    ~r2_hidden(k1_funct_1(sK3,sK2),sK1) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.20/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f21])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(k1_funct_1(sK3,sK2),sK1) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.41    inference(flattening,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.41    inference(ennf_transformation,[],[f9])).
% 0.20/0.41  fof(f9,negated_conjecture,(
% 0.20/0.41    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.20/0.41    inference(negated_conjecture,[],[f8])).
% 0.20/0.41  fof(f8,conjecture,(
% 0.20/0.41    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.20/0.41  fof(f66,plain,(
% 0.20/0.41    spl4_5),
% 0.20/0.41    inference(avatar_split_clause,[],[f25,f64])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f22])).
% 0.20/0.41  fof(f62,plain,(
% 0.20/0.41    spl4_4),
% 0.20/0.41    inference(avatar_split_clause,[],[f26,f60])).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.41    inference(cnf_transformation,[],[f22])).
% 0.20/0.41  fof(f58,plain,(
% 0.20/0.41    spl4_3),
% 0.20/0.41    inference(avatar_split_clause,[],[f27,f56])).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    r2_hidden(sK2,sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f22])).
% 0.20/0.41  fof(f54,plain,(
% 0.20/0.41    ~spl4_2),
% 0.20/0.41    inference(avatar_split_clause,[],[f28,f52])).
% 0.20/0.41  fof(f28,plain,(
% 0.20/0.41    k1_xboole_0 != sK1),
% 0.20/0.41    inference(cnf_transformation,[],[f22])).
% 0.20/0.41  fof(f50,plain,(
% 0.20/0.41    ~spl4_1),
% 0.20/0.41    inference(avatar_split_clause,[],[f29,f48])).
% 0.20/0.41  fof(f29,plain,(
% 0.20/0.41    ~r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f22])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (12366)------------------------------
% 0.20/0.41  % (12366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (12366)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (12366)Memory used [KB]: 10618
% 0.20/0.41  % (12366)Time elapsed: 0.028 s
% 0.20/0.41  % (12366)------------------------------
% 0.20/0.41  % (12366)------------------------------
% 0.20/0.41  % (12374)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.43  % (12357)Success in time 0.076 s
%------------------------------------------------------------------------------
