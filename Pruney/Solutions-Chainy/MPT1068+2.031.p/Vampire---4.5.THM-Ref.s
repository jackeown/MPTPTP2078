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
% DateTime   : Thu Dec  3 13:07:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 240 expanded)
%              Number of leaves         :   36 ( 122 expanded)
%              Depth                    :    7
%              Number of atoms          :  418 (1482 expanded)
%              Number of equality atoms :   76 ( 325 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f55,f59,f63,f67,f71,f75,f79,f83,f87,f91,f96,f118,f119,f126,f134,f145,f151,f154,f159,f165,f168])).

fof(f168,plain,
    ( spl7_2
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f166,f163,f53])).

fof(f53,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f163,plain,
    ( spl7_23
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f166,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_23 ),
    inference(resolution,[],[f164,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f164,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f163])).

fof(f165,plain,
    ( ~ spl7_4
    | spl7_23
    | spl7_22 ),
    inference(avatar_split_clause,[],[f160,f157,f163,f61])).

fof(f61,plain,
    ( spl7_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f157,plain,
    ( spl7_22
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f160,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5,sK1)
    | spl7_22 ),
    inference(resolution,[],[f158,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f158,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl7_22 ),
    inference(avatar_component_clause,[],[f157])).

fof(f159,plain,
    ( spl7_15
    | ~ spl7_22
    | ~ spl7_8
    | ~ spl7_7
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f155,f143,f73,f77,f157,f116])).

fof(f116,plain,
    ( spl7_15
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f77,plain,
    ( spl7_8
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f73,plain,
    ( spl7_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f143,plain,
    ( spl7_20
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ r2_hidden(sK5,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f155,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ r2_hidden(sK5,sK1)
    | k1_xboole_0 = sK2
    | ~ spl7_7
    | ~ spl7_20 ),
    inference(resolution,[],[f144,f74])).

fof(f74,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ r2_hidden(sK5,X1)
        | k1_xboole_0 = X0 )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f143])).

fof(f154,plain,(
    spl7_21 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl7_21 ),
    inference(resolution,[],[f150,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f150,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | spl7_21 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl7_21
  <=> v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f151,plain,
    ( ~ spl7_21
    | ~ spl7_5
    | spl7_19 ),
    inference(avatar_split_clause,[],[f147,f140,f65,f149])).

fof(f65,plain,
    ( spl7_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f140,plain,
    ( spl7_19
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f147,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | ~ spl7_5
    | spl7_19 ),
    inference(resolution,[],[f146,f66])).

fof(f66,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl7_19 ),
    inference(resolution,[],[f141,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f141,plain,
    ( ~ v1_relat_1(sK4)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f140])).

fof(f145,plain,
    ( ~ spl7_9
    | ~ spl7_19
    | ~ spl7_6
    | spl7_20
    | spl7_18 ),
    inference(avatar_split_clause,[],[f138,f132,f143,f69,f140,f81])).

fof(f81,plain,
    ( spl7_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f69,plain,
    ( spl7_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f132,plain,
    ( spl7_18
  <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(sK5,X1)
        | ~ v1_funct_1(sK4)
        | ~ v1_relat_1(sK4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ v1_funct_1(sK3) )
    | spl7_18 ),
    inference(trivial_inequality_removal,[],[f137])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
        | k1_xboole_0 = X0
        | ~ r2_hidden(sK5,X1)
        | ~ v1_funct_1(sK4)
        | ~ v1_relat_1(sK4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ v1_funct_1(sK3) )
    | spl7_18 ),
    inference(superposition,[],[f133,f44])).

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
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f133,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | spl7_18 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,
    ( ~ spl7_18
    | spl7_1
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f130,f123,f49,f132])).

fof(f49,plain,
    ( spl7_1
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f123,plain,
    ( spl7_16
  <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f130,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | spl7_1
    | ~ spl7_16 ),
    inference(superposition,[],[f50,f124])).

fof(f124,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f123])).

fof(f50,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f126,plain,
    ( ~ spl7_9
    | ~ spl7_7
    | ~ spl7_6
    | ~ spl7_5
    | spl7_16
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f121,f113,f123,f65,f69,f73,f81])).

fof(f113,plain,
    ( spl7_14
  <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f121,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ spl7_14 ),
    inference(superposition,[],[f46,f114])).

fof(f114,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f113])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f119,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK6
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK6) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f118,plain,
    ( ~ spl7_9
    | ~ spl7_8
    | ~ spl7_7
    | ~ spl7_6
    | ~ spl7_5
    | spl7_14
    | spl7_15
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f106,f57,f116,f113,f65,f69,f73,f77,f81])).

fof(f57,plain,
    ( spl7_3
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f106,plain,
    ( k1_xboole_0 = sK2
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f45,f58])).

fof(f58,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f57])).

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
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

% (6260)Refutation not found, incomplete strategy% (6260)------------------------------
% (6260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6260)Termination reason: Refutation not found, incomplete strategy

% (6260)Memory used [KB]: 1663
% (6260)Time elapsed: 0.093 s
% (6260)------------------------------
% (6260)------------------------------
fof(f96,plain,
    ( spl7_12
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f92,f89,f94])).

fof(f94,plain,
    ( spl7_12
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f89,plain,
    ( spl7_11
  <=> v1_xboole_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f92,plain,
    ( k1_xboole_0 = sK6
    | ~ spl7_11 ),
    inference(resolution,[],[f40,f90])).

fof(f90,plain,
    ( v1_xboole_0(sK6)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f89])).

fof(f91,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f47,f89])).

fof(f47,plain,(
    v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    v1_xboole_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f2,f28])).

fof(f28,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK6) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f87,plain,(
    ~ spl7_10 ),
    inference(avatar_split_clause,[],[f30,f85])).

fof(f85,plain,
    ( spl7_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f30,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f26,f25,f24,f23])).

fof(f23,plain,
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

fof(f24,plain,
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

fof(f25,plain,
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

fof(f26,plain,
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

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f83,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f31,f81])).

fof(f31,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f32,f77])).

fof(f32,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f33,f73])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f34,f69])).

fof(f34,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f35,f65])).

fof(f35,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f36,f61])).

fof(f36,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f37,f57])).

fof(f37,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f38,f53])).

fof(f38,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f39,f49])).

fof(f39,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:14:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (6252)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (6261)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (6253)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (6258)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (6266)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (6260)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (6253)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f51,f55,f59,f63,f67,f71,f75,f79,f83,f87,f91,f96,f118,f119,f126,f134,f145,f151,f154,f159,f165,f168])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    spl7_2 | ~spl7_23),
% 0.21/0.52    inference(avatar_split_clause,[],[f166,f163,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    spl7_2 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    spl7_23 <=> v1_xboole_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl7_23),
% 0.21/0.52    inference(resolution,[],[f164,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | ~spl7_23),
% 0.21/0.52    inference(avatar_component_clause,[],[f163])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ~spl7_4 | spl7_23 | spl7_22),
% 0.21/0.52    inference(avatar_split_clause,[],[f160,f157,f163,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl7_4 <=> m1_subset_1(sK5,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    spl7_22 <=> r2_hidden(sK5,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | ~m1_subset_1(sK5,sK1) | spl7_22),
% 0.21/0.52    inference(resolution,[],[f158,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ~r2_hidden(sK5,sK1) | spl7_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f157])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    spl7_15 | ~spl7_22 | ~spl7_8 | ~spl7_7 | ~spl7_20),
% 0.21/0.52    inference(avatar_split_clause,[],[f155,f143,f73,f77,f157,f116])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    spl7_15 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl7_8 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl7_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    spl7_20 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~v1_funct_2(sK3,X1,X0) | ~r2_hidden(sK5,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    ~v1_funct_2(sK3,sK1,sK2) | ~r2_hidden(sK5,sK1) | k1_xboole_0 = sK2 | (~spl7_7 | ~spl7_20)),
% 0.21/0.52    inference(resolution,[],[f144,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f73])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~r2_hidden(sK5,X1) | k1_xboole_0 = X0) ) | ~spl7_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f143])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    spl7_21),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f152])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    $false | spl7_21),
% 0.21/0.52    inference(resolution,[],[f150,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | spl7_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f149])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    spl7_21 <=> v1_relat_1(k2_zfmisc_1(sK2,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    ~spl7_21 | ~spl7_5 | spl7_19),
% 0.21/0.52    inference(avatar_split_clause,[],[f147,f140,f65,f149])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    spl7_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    spl7_19 <=> v1_relat_1(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | (~spl7_5 | spl7_19)),
% 0.21/0.52    inference(resolution,[],[f146,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl7_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f65])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl7_19),
% 0.21/0.52    inference(resolution,[],[f141,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ~v1_relat_1(sK4) | spl7_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f140])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    ~spl7_9 | ~spl7_19 | ~spl7_6 | spl7_20 | spl7_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f138,f132,f143,f69,f140,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl7_9 <=> v1_funct_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl7_6 <=> v1_funct_1(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    spl7_18 <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(sK5,X1) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~v1_funct_1(sK3)) ) | spl7_18),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f137])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k1_xboole_0 = X0 | ~r2_hidden(sK5,X1) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~v1_funct_1(sK3)) ) | spl7_18),
% 0.21/0.52    inference(superposition,[],[f133,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (! [X4] : (((k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~v1_funct_1(X4) | ~v1_relat_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => (r2_hidden(X2,X0) => (k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_2)).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | spl7_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f132])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ~spl7_18 | spl7_1 | ~spl7_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f130,f123,f49,f132])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    spl7_1 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    spl7_16 <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | (spl7_1 | ~spl7_16)),
% 0.21/0.52    inference(superposition,[],[f50,f124])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | ~spl7_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f123])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl7_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f49])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    ~spl7_9 | ~spl7_7 | ~spl7_6 | ~spl7_5 | spl7_16 | ~spl7_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f121,f113,f123,f65,f69,f73,f81])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl7_14 <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3) | ~spl7_14),
% 0.21/0.52    inference(superposition,[],[f46,f114])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~spl7_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f113])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    k1_xboole_0 != sK2 | k1_xboole_0 != sK6 | v1_xboole_0(sK2) | ~v1_xboole_0(sK6)),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ~spl7_9 | ~spl7_8 | ~spl7_7 | ~spl7_6 | ~spl7_5 | spl7_14 | spl7_15 | ~spl7_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f106,f57,f116,f113,f65,f69,f73,f77,f81])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    spl7_3 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~spl7_3),
% 0.21/0.52    inference(resolution,[],[f45,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl7_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f57])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | k1_xboole_0 = X1 | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).
% 0.21/0.52  % (6260)Refutation not found, incomplete strategy% (6260)------------------------------
% 0.21/0.52  % (6260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6260)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6260)Memory used [KB]: 1663
% 0.21/0.52  % (6260)Time elapsed: 0.093 s
% 0.21/0.52  % (6260)------------------------------
% 0.21/0.52  % (6260)------------------------------
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl7_12 | ~spl7_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f92,f89,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    spl7_12 <=> k1_xboole_0 = sK6),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    spl7_11 <=> v1_xboole_0(sK6)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    k1_xboole_0 = sK6 | ~spl7_11),
% 0.21/0.52    inference(resolution,[],[f40,f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    v1_xboole_0(sK6) | ~spl7_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f89])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    spl7_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f47,f89])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    v1_xboole_0(sK6)),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    v1_xboole_0(sK6)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f2,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK6)),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ? [X0] : v1_xboole_0(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ~spl7_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f30,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl7_10 <=> v1_xboole_0(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ~v1_xboole_0(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f26,f25,f24,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k1_funct_1(X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k1_funct_1(X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k1_funct_1(sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k1_funct_1(sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) => (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f9])).
% 0.21/0.52  fof(f9,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    spl7_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f31,f81])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    v1_funct_1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    spl7_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f32,f77])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    spl7_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f33,f73])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl7_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f34,f69])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    v1_funct_1(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    spl7_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f35,f65])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl7_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f36,f61])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    m1_subset_1(sK5,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    spl7_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f37,f57])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ~spl7_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f38,f53])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ~spl7_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f39,f49])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (6253)------------------------------
% 0.21/0.52  % (6253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6253)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (6253)Memory used [KB]: 10746
% 0.21/0.52  % (6253)Time elapsed: 0.090 s
% 0.21/0.52  % (6253)------------------------------
% 0.21/0.52  % (6253)------------------------------
% 0.21/0.52  % (6249)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.52  % (6246)Success in time 0.163 s
%------------------------------------------------------------------------------
