%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t32_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:43 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 118 expanded)
%              Number of leaves         :   16 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  226 ( 438 expanded)
%              Number of equality atoms :   61 ( 117 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f269,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f92,f96,f100,f113,f121,f138,f142,f170,f187,f192,f268])).

fof(f268,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_18
    | spl5_21
    | ~ spl5_36 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_18
    | ~ spl5_21
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f266,f141])).

fof(f141,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl5_21
  <=> k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f266,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) = sK2
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_18
    | ~ spl5_36 ),
    inference(resolution,[],[f198,f95])).

fof(f95,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_4
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0 )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f197,f137])).

fof(f137,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl5_18
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK3)
        | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0 )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f196,f91])).

fof(f91,plain,
    ( v2_funct_1(sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_2
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v2_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0 )
    | ~ spl5_0
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f194,f87])).

fof(f87,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_0
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_funct_1(sK3)
        | ~ v2_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0 )
    | ~ spl5_36 ),
    inference(superposition,[],[f57,f190])).

fof(f190,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl5_36
  <=> k1_relat_1(sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t32_funct_2.p',t56_funct_1)).

fof(f192,plain,
    ( spl5_36
    | ~ spl5_28
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f191,f185,f168,f189])).

fof(f168,plain,
    ( spl5_28
  <=> k1_relset_1(sK0,sK1,sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f185,plain,
    ( spl5_34
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f191,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl5_28
    | ~ spl5_34 ),
    inference(forward_demodulation,[],[f186,f169])).

fof(f169,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f168])).

fof(f186,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f185])).

fof(f187,plain,
    ( spl5_34
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f126,f119,f185])).

fof(f119,plain,
    ( spl5_14
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f126,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl5_14 ),
    inference(resolution,[],[f120,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t32_funct_2.p',redefinition_k1_relset_1)).

fof(f120,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f170,plain,
    ( spl5_28
    | spl5_7
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f134,f119,f111,f98,f168])).

fof(f98,plain,
    ( spl5_7
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f111,plain,
    ( spl5_10
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f134,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f133,f112])).

fof(f112,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f133,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f130,f99])).

fof(f99,plain,
    ( k1_xboole_0 != sK1
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f130,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_14 ),
    inference(resolution,[],[f120,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t32_funct_2.p',d1_funct_2)).

fof(f142,plain,(
    ~ spl5_21 ),
    inference(avatar_split_clause,[],[f56,f140])).

fof(f56,plain,(
    k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & v2_funct_1(X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & v2_funct_1(X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( ( r2_hidden(X2,X0)
            & v2_funct_1(X3) )
         => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t32_funct_2.p',t32_funct_2)).

fof(f138,plain,
    ( spl5_18
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f128,f119,f136])).

fof(f128,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_14 ),
    inference(resolution,[],[f120,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t32_funct_2.p',cc1_relset_1)).

fof(f121,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f52,f119])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f113,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f51,f111])).

fof(f51,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f55,f98])).

fof(f55,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f96,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f54,f94])).

fof(f54,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f53,f90])).

fof(f53,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f50,f86])).

fof(f50,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
