%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 231 expanded)
%              Number of leaves         :   33 ( 116 expanded)
%              Depth                    :    7
%              Number of atoms          :  401 (1464 expanded)
%              Number of equality atoms :   74 ( 323 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f70,f74,f78,f82,f86,f93,f110,f111,f118,f126,f135,f138,f143,f149,f152])).

fof(f152,plain,
    ( spl7_2
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f150,f147,f52])).

fof(f52,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f147,plain,
    ( spl7_20
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f150,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_20 ),
    inference(resolution,[],[f148,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f148,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f147])).

fof(f149,plain,
    ( ~ spl7_4
    | spl7_20
    | spl7_19 ),
    inference(avatar_split_clause,[],[f144,f141,f147,f60])).

fof(f60,plain,
    ( spl7_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f141,plain,
    ( spl7_19
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f144,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5,sK1)
    | spl7_19 ),
    inference(resolution,[],[f142,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f142,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( spl7_13
    | ~ spl7_19
    | ~ spl7_8
    | ~ spl7_7
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f139,f133,f72,f76,f141,f108])).

fof(f108,plain,
    ( spl7_13
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f76,plain,
    ( spl7_8
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f72,plain,
    ( spl7_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f133,plain,
    ( spl7_18
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ r2_hidden(sK5,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f139,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ r2_hidden(sK5,sK1)
    | k1_xboole_0 = sK2
    | ~ spl7_7
    | ~ spl7_18 ),
    inference(resolution,[],[f134,f73])).

fof(f73,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ r2_hidden(sK5,X1)
        | k1_xboole_0 = X0 )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f133])).

fof(f138,plain,
    ( ~ spl7_5
    | spl7_17 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl7_5
    | spl7_17 ),
    inference(subsumption_resolution,[],[f65,f136])).

fof(f136,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_17 ),
    inference(resolution,[],[f131,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f131,plain,
    ( ~ v1_relat_1(sK4)
    | spl7_17 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl7_17
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f65,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl7_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f135,plain,
    ( ~ spl7_9
    | ~ spl7_17
    | ~ spl7_6
    | spl7_18
    | spl7_16 ),
    inference(avatar_split_clause,[],[f128,f124,f133,f68,f130,f80])).

fof(f80,plain,
    ( spl7_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f68,plain,
    ( spl7_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f124,plain,
    ( spl7_16
  <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(sK5,X1)
        | ~ v1_funct_1(sK4)
        | ~ v1_relat_1(sK4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ v1_funct_1(sK3) )
    | spl7_16 ),
    inference(trivial_inequality_removal,[],[f127])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
        | k1_xboole_0 = X0
        | ~ r2_hidden(sK5,X1)
        | ~ v1_funct_1(sK4)
        | ~ v1_relat_1(sK4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ v1_funct_1(sK3) )
    | spl7_16 ),
    inference(superposition,[],[f125,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
          | k1_xboole_0 = X1
          | ~ r2_hidden(X2,X0)
          | ~ v1_funct_1(X4)
          | ~ v1_relat_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
          | k1_xboole_0 = X1
          | ~ r2_hidden(X2,X0)
          | ~ v1_funct_1(X4)
          | ~ v1_relat_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_relat_1(X4) )
         => ( r2_hidden(X2,X0)
           => ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_2)).

fof(f125,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f124])).

fof(f126,plain,
    ( ~ spl7_16
    | spl7_1
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f122,f115,f48,f124])).

fof(f48,plain,
    ( spl7_1
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f115,plain,
    ( spl7_14
  <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f122,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | spl7_1
    | ~ spl7_14 ),
    inference(superposition,[],[f49,f116])).

fof(f116,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f115])).

fof(f49,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f118,plain,
    ( ~ spl7_9
    | ~ spl7_7
    | ~ spl7_6
    | ~ spl7_5
    | spl7_14
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f113,f105,f115,f64,f68,f72,f80])).

fof(f105,plain,
    ( spl7_12
  <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f113,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ spl7_12 ),
    inference(superposition,[],[f46,f106])).

fof(f106,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f111,plain,
    ( k1_xboole_0 != sK2
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f110,plain,
    ( ~ spl7_9
    | ~ spl7_8
    | ~ spl7_7
    | ~ spl7_6
    | ~ spl7_5
    | spl7_12
    | spl7_13
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f98,f56,f108,f105,f64,f68,f72,f76,f80])).

fof(f56,plain,
    ( spl7_3
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f98,plain,
    ( k1_xboole_0 = sK2
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f45,f57])).

fof(f57,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | k1_xboole_0 = X1
      | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

fof(f93,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f89,f91])).

fof(f91,plain,
    ( spl7_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f89,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f41,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = sK6(X0) ),
    inference(resolution,[],[f39,f41])).

fof(f41,plain,(
    ! [X0] : v1_xboole_0(sK6(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(sK6(X0))
      & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f2,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK6(X0))
        & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f86,plain,(
    ~ spl7_10 ),
    inference(avatar_split_clause,[],[f29,f84])).

fof(f84,plain,
    ( spl7_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f29,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5)
                  & k1_xboole_0 != sK1
                  & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5)
                & k1_xboole_0 != sK1
                & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k1_funct_1(X4,k1_funct_1(sK3,X5))
              & k1_xboole_0 != sK1
              & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k1_funct_1(X4,k1_funct_1(sK3,X5))
            & k1_xboole_0 != sK1
            & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k1_funct_1(sK4,k1_funct_1(sK3,X5))
          & k1_xboole_0 != sK1
          & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k1_funct_1(sK4,k1_funct_1(sK3,X5))
        & k1_xboole_0 != sK1
        & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
        & m1_subset_1(X5,sK1) )
   => ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
      & k1_xboole_0 != sK1
      & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f82,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f30,f80])).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f31,f76])).

fof(f31,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f32,f72])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f34,f64])).

fof(f34,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f35,f60])).

fof(f35,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f36,f56])).

fof(f36,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f37,f52])).

fof(f37,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f38,f48])).

fof(f38,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (4769)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.43  % (4783)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.43  % (4769)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f153,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f70,f74,f78,f82,f86,f93,f110,f111,f118,f126,f135,f138,f143,f149,f152])).
% 0.20/0.43  fof(f152,plain,(
% 0.20/0.43    spl7_2 | ~spl7_20),
% 0.20/0.43    inference(avatar_split_clause,[],[f150,f147,f52])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    spl7_2 <=> k1_xboole_0 = sK1),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.43  fof(f147,plain,(
% 0.20/0.43    spl7_20 <=> v1_xboole_0(sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.20/0.43  fof(f150,plain,(
% 0.20/0.43    k1_xboole_0 = sK1 | ~spl7_20),
% 0.20/0.43    inference(resolution,[],[f148,f39])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.43  fof(f148,plain,(
% 0.20/0.43    v1_xboole_0(sK1) | ~spl7_20),
% 0.20/0.43    inference(avatar_component_clause,[],[f147])).
% 0.20/0.43  fof(f149,plain,(
% 0.20/0.43    ~spl7_4 | spl7_20 | spl7_19),
% 0.20/0.43    inference(avatar_split_clause,[],[f144,f141,f147,f60])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    spl7_4 <=> m1_subset_1(sK5,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.43  fof(f141,plain,(
% 0.20/0.43    spl7_19 <=> r2_hidden(sK5,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.20/0.43  fof(f144,plain,(
% 0.20/0.43    v1_xboole_0(sK1) | ~m1_subset_1(sK5,sK1) | spl7_19),
% 0.20/0.43    inference(resolution,[],[f142,f42])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.43    inference(flattening,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.43  fof(f142,plain,(
% 0.20/0.43    ~r2_hidden(sK5,sK1) | spl7_19),
% 0.20/0.43    inference(avatar_component_clause,[],[f141])).
% 0.20/0.43  fof(f143,plain,(
% 0.20/0.43    spl7_13 | ~spl7_19 | ~spl7_8 | ~spl7_7 | ~spl7_18),
% 0.20/0.43    inference(avatar_split_clause,[],[f139,f133,f72,f76,f141,f108])).
% 0.20/0.43  fof(f108,plain,(
% 0.20/0.43    spl7_13 <=> k1_xboole_0 = sK2),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.43  fof(f76,plain,(
% 0.20/0.43    spl7_8 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    spl7_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.43  fof(f133,plain,(
% 0.20/0.43    spl7_18 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~v1_funct_2(sK3,X1,X0) | ~r2_hidden(sK5,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.20/0.43  fof(f139,plain,(
% 0.20/0.43    ~v1_funct_2(sK3,sK1,sK2) | ~r2_hidden(sK5,sK1) | k1_xboole_0 = sK2 | (~spl7_7 | ~spl7_18)),
% 0.20/0.43    inference(resolution,[],[f134,f73])).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f72])).
% 0.20/0.43  fof(f134,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~r2_hidden(sK5,X1) | k1_xboole_0 = X0) ) | ~spl7_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f133])).
% 0.20/0.43  fof(f138,plain,(
% 0.20/0.43    ~spl7_5 | spl7_17),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f137])).
% 0.20/0.43  fof(f137,plain,(
% 0.20/0.43    $false | (~spl7_5 | spl7_17)),
% 0.20/0.43    inference(subsumption_resolution,[],[f65,f136])).
% 0.20/0.43  fof(f136,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_17),
% 0.20/0.43    inference(resolution,[],[f131,f43])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.43  fof(f131,plain,(
% 0.20/0.43    ~v1_relat_1(sK4) | spl7_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f130])).
% 0.20/0.43  fof(f130,plain,(
% 0.20/0.43    spl7_17 <=> v1_relat_1(sK4)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl7_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f64])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    spl7_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.43  fof(f135,plain,(
% 0.20/0.43    ~spl7_9 | ~spl7_17 | ~spl7_6 | spl7_18 | spl7_16),
% 0.20/0.43    inference(avatar_split_clause,[],[f128,f124,f133,f68,f130,f80])).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    spl7_9 <=> v1_funct_1(sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    spl7_6 <=> v1_funct_1(sK4)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.43  fof(f124,plain,(
% 0.20/0.43    spl7_16 <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.20/0.43  fof(f128,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(sK5,X1) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~v1_funct_1(sK3)) ) | spl7_16),
% 0.20/0.43    inference(trivial_inequality_removal,[],[f127])).
% 0.20/0.43  fof(f127,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k1_xboole_0 = X0 | ~r2_hidden(sK5,X1) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~v1_funct_1(sK3)) ) | spl7_16),
% 0.20/0.43    inference(superposition,[],[f125,f44])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X3,X1] : (k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.43    inference(flattening,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (! [X4] : (((k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~v1_funct_1(X4) | ~v1_relat_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => (r2_hidden(X2,X0) => (k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_2)).
% 0.20/0.43  fof(f125,plain,(
% 0.20/0.43    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | spl7_16),
% 0.20/0.43    inference(avatar_component_clause,[],[f124])).
% 0.20/0.43  fof(f126,plain,(
% 0.20/0.43    ~spl7_16 | spl7_1 | ~spl7_14),
% 0.20/0.43    inference(avatar_split_clause,[],[f122,f115,f48,f124])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    spl7_1 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.43  fof(f115,plain,(
% 0.20/0.43    spl7_14 <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | (spl7_1 | ~spl7_14)),
% 0.20/0.43    inference(superposition,[],[f49,f116])).
% 0.20/0.43  fof(f116,plain,(
% 0.20/0.43    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | ~spl7_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f115])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl7_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f48])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    ~spl7_9 | ~spl7_7 | ~spl7_6 | ~spl7_5 | spl7_14 | ~spl7_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f113,f105,f115,f64,f68,f72,f80])).
% 0.20/0.43  fof(f105,plain,(
% 0.20/0.43    spl7_12 <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.43  fof(f113,plain,(
% 0.20/0.43    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3) | ~spl7_12),
% 0.20/0.43    inference(superposition,[],[f46,f106])).
% 0.20/0.43  fof(f106,plain,(
% 0.20/0.43    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~spl7_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f105])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.43    inference(flattening,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.20/0.43  fof(f111,plain,(
% 0.20/0.43    k1_xboole_0 != sK2 | v1_xboole_0(sK2) | ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.43  fof(f110,plain,(
% 0.20/0.43    ~spl7_9 | ~spl7_8 | ~spl7_7 | ~spl7_6 | ~spl7_5 | spl7_12 | spl7_13 | ~spl7_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f98,f56,f108,f105,f64,f68,f72,f76,f80])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    spl7_3 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.43  fof(f98,plain,(
% 0.20/0.43    k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~spl7_3),
% 0.20/0.43    inference(resolution,[],[f45,f57])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl7_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f56])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | k1_xboole_0 = X1 | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.43    inference(flattening,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).
% 0.20/0.43  fof(f93,plain,(
% 0.20/0.43    spl7_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f89,f91])).
% 0.20/0.43  fof(f91,plain,(
% 0.20/0.43    spl7_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.43  fof(f89,plain,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    inference(superposition,[],[f41,f87])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = sK6(X0)) )),
% 0.20/0.43    inference(resolution,[],[f39,f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ( ! [X0] : (v1_xboole_0(sK6(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ! [X0] : (v1_xboole_0(sK6(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f2,f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK6(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(X0))))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).
% 0.20/0.43  fof(f86,plain,(
% 0.20/0.43    ~spl7_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f29,f84])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    spl7_10 <=> v1_xboole_0(sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ~v1_xboole_0(sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f25,f24,f23,f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k1_funct_1(X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k1_funct_1(X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k1_funct_1(sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k1_funct_1(sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) => (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.20/0.43    inference(flattening,[],[f10])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.20/0.44    inference(ennf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.20/0.44    inference(negated_conjecture,[],[f8])).
% 0.20/0.44  fof(f8,conjecture,(
% 0.20/0.44    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.20/0.44  fof(f82,plain,(
% 0.20/0.44    spl7_9),
% 0.20/0.44    inference(avatar_split_clause,[],[f30,f80])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    v1_funct_1(sK3)),
% 0.20/0.44    inference(cnf_transformation,[],[f26])).
% 0.20/0.44  fof(f78,plain,(
% 0.20/0.44    spl7_8),
% 0.20/0.44    inference(avatar_split_clause,[],[f31,f76])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f26])).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    spl7_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f32,f72])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.44    inference(cnf_transformation,[],[f26])).
% 0.20/0.44  fof(f70,plain,(
% 0.20/0.44    spl7_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f33,f68])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    v1_funct_1(sK4)),
% 0.20/0.44    inference(cnf_transformation,[],[f26])).
% 0.20/0.44  fof(f66,plain,(
% 0.20/0.44    spl7_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f34,f64])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.20/0.44    inference(cnf_transformation,[],[f26])).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    spl7_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f35,f60])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    m1_subset_1(sK5,sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f26])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    spl7_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f36,f56])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.20/0.44    inference(cnf_transformation,[],[f26])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    ~spl7_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f37,f52])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    k1_xboole_0 != sK1),
% 0.20/0.44    inference(cnf_transformation,[],[f26])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    ~spl7_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f38,f48])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.44    inference(cnf_transformation,[],[f26])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (4769)------------------------------
% 0.20/0.44  % (4769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (4769)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (4769)Memory used [KB]: 10746
% 0.20/0.44  % (4769)Time elapsed: 0.050 s
% 0.20/0.44  % (4769)------------------------------
% 0.20/0.44  % (4769)------------------------------
% 0.20/0.44  % (4762)Success in time 0.084 s
%------------------------------------------------------------------------------
