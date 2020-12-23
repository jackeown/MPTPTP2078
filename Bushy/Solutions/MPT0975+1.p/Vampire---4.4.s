%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t21_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:42 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 128 expanded)
%              Number of leaves         :   17 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  249 ( 519 expanded)
%              Number of equality atoms :   59 ( 123 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f366,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f92,f96,f107,f111,f124,f132,f149,f153,f176,f194,f199,f365])).

fof(f365,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_20
    | spl6_23
    | ~ spl6_34 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_20
    | ~ spl6_23
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f363,f152])).

fof(f152,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl6_23
  <=> k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f363,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK2) = k1_funct_1(sK4,k1_funct_1(sK3,sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_20
    | ~ spl6_34 ),
    inference(resolution,[],[f240,f106])).

fof(f106,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl6_6
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_20
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f239,f95])).

fof(f95,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_funct_1(sK3)
        | k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_20
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f238,f148])).

fof(f148,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl6_20
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_34 ),
    inference(superposition,[],[f103,f197])).

fof(f197,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl6_34
  <=> k1_relat_1(sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f103,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k1_relat_1(X2))
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | k1_funct_1(k5_relat_1(X2,sK4),X3) = k1_funct_1(sK4,k1_funct_1(X2,X3)) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f99,f91])).

fof(f91,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_2
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f99,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(sK4)
        | ~ r2_hidden(X3,k1_relat_1(X2))
        | k1_funct_1(k5_relat_1(X2,sK4),X3) = k1_funct_1(sK4,k1_funct_1(X2,X3)) )
    | ~ spl6_0 ),
    inference(resolution,[],[f87,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t21_funct_2.p',t23_funct_1)).

fof(f87,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_0
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f199,plain,
    ( spl6_34
    | ~ spl6_28
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f198,f192,f174,f196])).

fof(f174,plain,
    ( spl6_28
  <=> k1_relset_1(sK0,sK1,sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f192,plain,
    ( spl6_32
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f198,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl6_28
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f193,f175])).

fof(f175,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f174])).

fof(f193,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f192])).

fof(f194,plain,
    ( spl6_32
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f137,f130,f192])).

fof(f130,plain,
    ( spl6_16
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f137,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl6_16 ),
    inference(resolution,[],[f131,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t21_funct_2.p',redefinition_k1_relset_1)).

fof(f131,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f130])).

fof(f176,plain,
    ( spl6_28
    | spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f145,f130,f122,f109,f174])).

fof(f109,plain,
    ( spl6_9
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f122,plain,
    ( spl6_12
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f145,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f144,f123])).

fof(f123,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f122])).

fof(f144,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_9
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f141,f110])).

fof(f110,plain,
    ( k1_xboole_0 != sK1
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f141,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_16 ),
    inference(resolution,[],[f131,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t21_funct_2.p',d1_funct_2)).

fof(f153,plain,(
    ~ spl6_23 ),
    inference(avatar_split_clause,[],[f54,f151])).

fof(f54,plain,(
    k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X4,k1_funct_1(X3,X2)) != k1_funct_1(k5_relat_1(X3,X4),X2)
          & k1_xboole_0 != X1
          & r2_hidden(X2,X0)
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X4,k1_funct_1(X3,X2)) != k1_funct_1(k5_relat_1(X3,X4),X2)
          & k1_xboole_0 != X1
          & r2_hidden(X2,X0)
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_relat_1(X4) )
           => ( r2_hidden(X2,X0)
             => ( k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2)
                | k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_relat_1(X4) )
         => ( r2_hidden(X2,X0)
           => ( k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t21_funct_2.p',t21_funct_2)).

fof(f149,plain,
    ( spl6_20
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f139,f130,f147])).

fof(f139,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_16 ),
    inference(resolution,[],[f131,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t21_funct_2.p',cc1_relset_1)).

fof(f132,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f57,f130])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f124,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f56,f122])).

fof(f56,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f111,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f53,f109])).

fof(f53,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f107,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f52,f105])).

fof(f52,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f96,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f55,f94])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f51,f90])).

fof(f51,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f50,f86])).

fof(f50,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
