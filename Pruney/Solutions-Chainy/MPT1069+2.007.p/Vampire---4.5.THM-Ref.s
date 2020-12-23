%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 363 expanded)
%              Number of leaves         :   52 ( 176 expanded)
%              Depth                    :   11
%              Number of atoms          :  710 (1944 expanded)
%              Number of equality atoms :  100 ( 379 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f722,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f111,f115,f119,f123,f127,f131,f135,f139,f143,f183,f271,f283,f293,f313,f362,f374,f377,f380,f430,f436,f447,f485,f498,f581,f590,f598,f698,f718,f721])).

fof(f721,plain,
    ( spl7_17
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_13
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f719,f434,f181,f133,f129,f250])).

fof(f250,plain,
    ( spl7_17
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f129,plain,
    ( spl7_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f133,plain,
    ( spl7_8
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f181,plain,
    ( spl7_13
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f434,plain,
    ( spl7_37
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_2(sK3,sK1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f719,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_xboole_0 = sK2
    | ~ spl7_13
    | ~ spl7_37 ),
    inference(resolution,[],[f435,f182])).

fof(f182,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f181])).

fof(f435,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4))
        | ~ v1_funct_2(sK3,sK1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | k1_xboole_0 = X0 )
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f434])).

fof(f718,plain,
    ( spl7_2
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f710,f496,f109])).

fof(f109,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f496,plain,
    ( spl7_47
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f710,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_47 ),
    inference(resolution,[],[f497,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f497,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f496])).

fof(f698,plain,
    ( ~ spl7_7
    | spl7_10
    | spl7_47
    | ~ spl7_8
    | ~ spl7_59 ),
    inference(avatar_split_clause,[],[f695,f596,f133,f496,f141,f129])).

fof(f141,plain,
    ( spl7_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f596,plain,
    ( spl7_59
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(sK3,X0,X1)
        | v1_xboole_0(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f695,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_8
    | ~ spl7_59 ),
    inference(resolution,[],[f597,f134])).

fof(f134,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f597,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK3,X0,X1)
        | v1_xboole_0(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_59 ),
    inference(avatar_component_clause,[],[f596])).

fof(f598,plain,
    ( ~ spl7_9
    | spl7_59
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f591,f588,f596,f137])).

fof(f137,plain,
    ( spl7_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f588,plain,
    ( spl7_58
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f591,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK3,X0,X1)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | v1_xboole_0(X0) )
    | ~ spl7_58 ),
    inference(resolution,[],[f589,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

fof(f589,plain,
    ( v1_xboole_0(sK3)
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f588])).

fof(f590,plain,
    ( spl7_58
    | ~ spl7_12
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f586,f579,f157,f588])).

fof(f157,plain,
    ( spl7_12
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f579,plain,
    ( spl7_56
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f586,plain,
    ( v1_xboole_0(sK3)
    | ~ spl7_12
    | ~ spl7_56 ),
    inference(resolution,[],[f580,f315])).

fof(f315,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X2) )
    | ~ spl7_12 ),
    inference(resolution,[],[f158,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f158,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f580,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f579])).

fof(f581,plain,
    ( ~ spl7_9
    | ~ spl7_8
    | ~ spl7_7
    | spl7_56
    | spl7_17
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f575,f445,f250,f579,f129,f133,f137])).

fof(f445,plain,
    ( spl7_39
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f575,plain,
    ( k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | ~ spl7_39 ),
    inference(resolution,[],[f446,f332])).

fof(f332,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relset_1(X0,X2,X1),k1_xboole_0)
      | k1_xboole_0 = X2
      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(X1,X0,X2)
      | ~ v1_funct_1(X1) ) ),
    inference(superposition,[],[f97,f99])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(f446,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f445])).

fof(f498,plain,
    ( ~ spl7_4
    | spl7_47
    | spl7_44 ),
    inference(avatar_split_clause,[],[f494,f483,f496,f117])).

fof(f117,plain,
    ( spl7_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f483,plain,
    ( spl7_44
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f494,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5,sK1)
    | spl7_44 ),
    inference(resolution,[],[f484,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f484,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl7_44 ),
    inference(avatar_component_clause,[],[f483])).

fof(f485,plain,
    ( ~ spl7_44
    | spl7_28
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f476,f425,f372,f483])).

fof(f372,plain,
    ( spl7_28
  <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f425,plain,
    ( spl7_35
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r2_hidden(k1_funct_1(sK3,X1),k1_relat_1(sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f476,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl7_28
    | ~ spl7_35 ),
    inference(resolution,[],[f426,f373])).

fof(f373,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | spl7_28 ),
    inference(avatar_component_clause,[],[f372])).

fof(f426,plain,
    ( ! [X1] :
        ( r2_hidden(k1_funct_1(sK3,X1),k1_relat_1(sK4))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f425])).

fof(f447,plain,
    ( spl7_39
    | ~ spl7_13
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f443,f422,f181,f445])).

fof(f422,plain,
    ( spl7_34
  <=> k1_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f443,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)
    | ~ spl7_13
    | ~ spl7_34 ),
    inference(superposition,[],[f182,f423])).

fof(f423,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f422])).

fof(f436,plain,
    ( ~ spl7_9
    | spl7_37
    | spl7_36 ),
    inference(avatar_split_clause,[],[f431,f428,f434,f137])).

fof(f428,plain,
    ( spl7_36
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f431,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(sK3,sK1,X0)
        | ~ v1_funct_1(sK3) )
    | spl7_36 ),
    inference(resolution,[],[f429,f97])).

fof(f429,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))
    | spl7_36 ),
    inference(avatar_component_clause,[],[f428])).

fof(f430,plain,
    ( spl7_34
    | spl7_35
    | ~ spl7_36
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f409,f291,f181,f428,f425,f422])).

fof(f291,plain,
    ( spl7_22
  <=> ! [X3,X2] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
        | ~ r2_hidden(X3,sK1)
        | r2_hidden(k1_funct_1(sK3,X3),X2)
        | k1_xboole_0 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f409,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))
        | ~ r2_hidden(X1,sK1)
        | r2_hidden(k1_funct_1(sK3,X1),k1_relat_1(sK4))
        | k1_xboole_0 = k1_relat_1(sK4) )
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(resolution,[],[f292,f182])).

fof(f292,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
        | ~ r2_hidden(X3,sK1)
        | r2_hidden(k1_funct_1(sK3,X3),X2)
        | k1_xboole_0 = X2 )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f291])).

fof(f380,plain,
    ( ~ spl7_5
    | spl7_27 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | ~ spl7_5
    | spl7_27 ),
    inference(subsumption_resolution,[],[f122,f378])).

fof(f378,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl7_27 ),
    inference(resolution,[],[f370,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f370,plain,
    ( ~ v5_relat_1(sK4,sK0)
    | spl7_27 ),
    inference(avatar_component_clause,[],[f369])).

fof(f369,plain,
    ( spl7_27
  <=> v5_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f122,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl7_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f377,plain,
    ( ~ spl7_5
    | spl7_26 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | ~ spl7_5
    | spl7_26 ),
    inference(subsumption_resolution,[],[f122,f375])).

fof(f375,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_26 ),
    inference(resolution,[],[f367,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f367,plain,
    ( ~ v1_relat_1(sK4)
    | spl7_26 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl7_26
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f374,plain,
    ( ~ spl7_26
    | ~ spl7_27
    | ~ spl7_6
    | ~ spl7_28
    | spl7_25 ),
    inference(avatar_split_clause,[],[f364,f360,f372,f125,f369,f366])).

fof(f125,plain,
    ( spl7_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f360,plain,
    ( spl7_25
  <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f364,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | spl7_25 ),
    inference(trivial_inequality_removal,[],[f363])).

fof(f363,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | spl7_25 ),
    inference(superposition,[],[f361,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f361,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f360])).

fof(f362,plain,
    ( spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_7
    | ~ spl7_6
    | ~ spl7_5
    | ~ spl7_4
    | ~ spl7_3
    | spl7_2
    | ~ spl7_25
    | spl7_1 ),
    inference(avatar_split_clause,[],[f352,f105,f360,f109,f113,f117,f121,f125,f129,f133,f137,f141])).

fof(f113,plain,
    ( spl7_3
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f105,plain,
    ( spl7_1
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f352,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | spl7_1 ),
    inference(superposition,[],[f106,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f106,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f313,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f312,f157])).

fof(f312,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(global_subsumption,[],[f310])).

fof(f310,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(global_subsumption,[],[f308])).

fof(f308,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(global_subsumption,[],[f68,f172])).

fof(f172,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f150,f147])).

fof(f147,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f72,f99])).

fof(f72,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f150,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK6(X2,X3),X2)
      | v1_xboole_0(X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f76,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f29,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f68,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f293,plain,
    ( ~ spl7_9
    | spl7_22
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f285,f281,f291,f137])).

fof(f281,plain,
    ( spl7_20
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
        | v1_funct_2(sK3,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f285,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)
        | k1_xboole_0 = X2
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
        | r2_hidden(k1_funct_1(sK3,X3),X2)
        | ~ v1_funct_1(sK3) )
    | ~ spl7_20 ),
    inference(resolution,[],[f282,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f282,plain,
    ( ! [X0] :
        ( v1_funct_2(sK3,sK1,X0)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f281])).

fof(f283,plain,
    ( ~ spl7_9
    | ~ spl7_7
    | spl7_20
    | spl7_17
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f279,f133,f250,f281,f129,f137])).

fof(f279,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK2
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | v1_funct_2(sK3,sK1,X0)
        | ~ v1_funct_1(sK3) )
    | ~ spl7_8 ),
    inference(resolution,[],[f95,f134])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X3,X0,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f271,plain,
    ( k1_xboole_0 != sK2
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f183,plain,
    ( ~ spl7_5
    | spl7_13
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f178,f113,f181,f121])).

fof(f178,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl7_3 ),
    inference(superposition,[],[f114,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f114,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f143,plain,(
    ~ spl7_10 ),
    inference(avatar_split_clause,[],[f58,f141])).

fof(f58,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f25,f51,f50,f49,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
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
                  ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
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

fof(f49,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
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
              ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
              & k1_xboole_0 != sK1
              & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
            & k1_xboole_0 != sK1
            & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
          & k1_xboole_0 != sK1
          & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
        & k1_xboole_0 != sK1
        & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
        & m1_subset_1(X5,sK1) )
   => ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
      & k1_xboole_0 != sK1
      & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(f139,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f59,f137])).

fof(f59,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f135,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f60,f133])).

fof(f60,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f131,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f61,f129])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f52])).

fof(f127,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f62,f125])).

fof(f62,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f123,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f63,f121])).

fof(f63,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f119,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f64,f117])).

fof(f64,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f115,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f65,f113])).

fof(f65,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f52])).

fof(f111,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f66,f109])).

fof(f66,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f52])).

fof(f107,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f67,f105])).

fof(f67,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:28:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (10350)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.47  % (10349)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (10362)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  % (10360)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (10348)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (10358)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (10347)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (10349)Refutation not found, incomplete strategy% (10349)------------------------------
% 0.22/0.49  % (10349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (10349)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (10349)Memory used [KB]: 10874
% 0.22/0.49  % (10349)Time elapsed: 0.066 s
% 0.22/0.49  % (10349)------------------------------
% 0.22/0.49  % (10349)------------------------------
% 0.22/0.50  % (10366)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (10366)Refutation not found, incomplete strategy% (10366)------------------------------
% 0.22/0.50  % (10366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (10366)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (10366)Memory used [KB]: 10618
% 0.22/0.50  % (10366)Time elapsed: 0.076 s
% 0.22/0.50  % (10366)------------------------------
% 0.22/0.50  % (10366)------------------------------
% 0.22/0.50  % (10364)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (10356)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (10355)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (10365)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (10352)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (10347)Refutation not found, incomplete strategy% (10347)------------------------------
% 0.22/0.51  % (10347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (10347)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (10347)Memory used [KB]: 10746
% 0.22/0.51  % (10347)Time elapsed: 0.072 s
% 0.22/0.51  % (10347)------------------------------
% 0.22/0.51  % (10347)------------------------------
% 0.22/0.51  % (10351)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (10361)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (10357)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (10346)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (10363)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (10353)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (10359)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (10354)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.53  % (10359)Refutation not found, incomplete strategy% (10359)------------------------------
% 0.22/0.53  % (10359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10359)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10359)Memory used [KB]: 1918
% 0.22/0.54  % (10359)Time elapsed: 0.116 s
% 0.22/0.54  % (10359)------------------------------
% 0.22/0.54  % (10359)------------------------------
% 0.22/0.55  % (10346)Refutation not found, incomplete strategy% (10346)------------------------------
% 0.22/0.55  % (10346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10346)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (10346)Memory used [KB]: 6780
% 0.22/0.55  % (10346)Time elapsed: 0.109 s
% 0.22/0.55  % (10346)------------------------------
% 0.22/0.55  % (10346)------------------------------
% 0.22/0.55  % (10352)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f722,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f107,f111,f115,f119,f123,f127,f131,f135,f139,f143,f183,f271,f283,f293,f313,f362,f374,f377,f380,f430,f436,f447,f485,f498,f581,f590,f598,f698,f718,f721])).
% 0.22/0.55  fof(f721,plain,(
% 0.22/0.55    spl7_17 | ~spl7_7 | ~spl7_8 | ~spl7_13 | ~spl7_37),
% 0.22/0.55    inference(avatar_split_clause,[],[f719,f434,f181,f133,f129,f250])).
% 0.22/0.55  fof(f250,plain,(
% 0.22/0.55    spl7_17 <=> k1_xboole_0 = sK2),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.22/0.55  fof(f129,plain,(
% 0.22/0.55    spl7_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    spl7_8 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.55  fof(f181,plain,(
% 0.22/0.55    spl7_13 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.55  fof(f434,plain,(
% 0.22/0.55    spl7_37 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_funct_2(sK3,sK1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.22/0.55  fof(f719,plain,(
% 0.22/0.55    ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | k1_xboole_0 = sK2 | (~spl7_13 | ~spl7_37)),
% 0.22/0.55    inference(resolution,[],[f435,f182])).
% 0.22/0.55  fof(f182,plain,(
% 0.22/0.55    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~spl7_13),
% 0.22/0.55    inference(avatar_component_clause,[],[f181])).
% 0.22/0.55  fof(f435,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4)) | ~v1_funct_2(sK3,sK1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | k1_xboole_0 = X0) ) | ~spl7_37),
% 0.22/0.55    inference(avatar_component_clause,[],[f434])).
% 0.22/0.55  fof(f718,plain,(
% 0.22/0.55    spl7_2 | ~spl7_47),
% 0.22/0.55    inference(avatar_split_clause,[],[f710,f496,f109])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    spl7_2 <=> k1_xboole_0 = sK1),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.55  fof(f496,plain,(
% 0.22/0.55    spl7_47 <=> v1_xboole_0(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 0.22/0.55  fof(f710,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | ~spl7_47),
% 0.22/0.55    inference(resolution,[],[f497,f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.55  fof(f497,plain,(
% 0.22/0.55    v1_xboole_0(sK1) | ~spl7_47),
% 0.22/0.55    inference(avatar_component_clause,[],[f496])).
% 0.22/0.55  fof(f698,plain,(
% 0.22/0.55    ~spl7_7 | spl7_10 | spl7_47 | ~spl7_8 | ~spl7_59),
% 0.22/0.55    inference(avatar_split_clause,[],[f695,f596,f133,f496,f141,f129])).
% 0.22/0.55  fof(f141,plain,(
% 0.22/0.55    spl7_10 <=> v1_xboole_0(sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.55  fof(f596,plain,(
% 0.22/0.55    spl7_59 <=> ! [X1,X0] : (~v1_funct_2(sK3,X0,X1) | v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).
% 0.22/0.55  fof(f695,plain,(
% 0.22/0.55    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl7_8 | ~spl7_59)),
% 0.22/0.55    inference(resolution,[],[f597,f134])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    v1_funct_2(sK3,sK1,sK2) | ~spl7_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f133])).
% 0.22/0.55  fof(f597,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_funct_2(sK3,X0,X1) | v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl7_59),
% 0.22/0.55    inference(avatar_component_clause,[],[f596])).
% 0.22/0.55  fof(f598,plain,(
% 0.22/0.55    ~spl7_9 | spl7_59 | ~spl7_58),
% 0.22/0.55    inference(avatar_split_clause,[],[f591,f588,f596,f137])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    spl7_9 <=> v1_funct_1(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.55  fof(f588,plain,(
% 0.22/0.55    spl7_58 <=> v1_xboole_0(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).
% 0.22/0.55  fof(f591,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_funct_2(sK3,X0,X1) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) ) | ~spl7_58),
% 0.22/0.55    inference(resolution,[],[f589,f80])).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.55    inference(flattening,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,axiom,(
% 0.22/0.56    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).
% 0.22/0.56  fof(f589,plain,(
% 0.22/0.56    v1_xboole_0(sK3) | ~spl7_58),
% 0.22/0.56    inference(avatar_component_clause,[],[f588])).
% 0.22/0.56  fof(f590,plain,(
% 0.22/0.56    spl7_58 | ~spl7_12 | ~spl7_56),
% 0.22/0.56    inference(avatar_split_clause,[],[f586,f579,f157,f588])).
% 0.22/0.56  fof(f157,plain,(
% 0.22/0.56    spl7_12 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.56  fof(f579,plain,(
% 0.22/0.56    spl7_56 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 0.22/0.56  fof(f586,plain,(
% 0.22/0.56    v1_xboole_0(sK3) | (~spl7_12 | ~spl7_56)),
% 0.22/0.56    inference(resolution,[],[f580,f315])).
% 0.22/0.56  fof(f315,plain,(
% 0.22/0.56    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X2)) ) | ~spl7_12),
% 0.22/0.56    inference(resolution,[],[f158,f71])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.56  fof(f158,plain,(
% 0.22/0.56    v1_xboole_0(k1_xboole_0) | ~spl7_12),
% 0.22/0.56    inference(avatar_component_clause,[],[f157])).
% 0.22/0.56  fof(f580,plain,(
% 0.22/0.56    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl7_56),
% 0.22/0.56    inference(avatar_component_clause,[],[f579])).
% 0.22/0.56  fof(f581,plain,(
% 0.22/0.56    ~spl7_9 | ~spl7_8 | ~spl7_7 | spl7_56 | spl7_17 | ~spl7_39),
% 0.22/0.56    inference(avatar_split_clause,[],[f575,f445,f250,f579,f129,f133,f137])).
% 0.22/0.56  fof(f445,plain,(
% 0.22/0.56    spl7_39 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.22/0.56  fof(f575,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~spl7_39),
% 0.22/0.56    inference(resolution,[],[f446,f332])).
% 0.22/0.56  fof(f332,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(X0,X2,X1),k1_xboole_0) | k1_xboole_0 = X2 | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X1,X0,X2) | ~v1_funct_1(X1)) )),
% 0.22/0.56    inference(superposition,[],[f97,f99])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f87])).
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    inference(flattening,[],[f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.56    inference(flattening,[],[f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.56    inference(ennf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 0.22/0.56  fof(f446,plain,(
% 0.22/0.56    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) | ~spl7_39),
% 0.22/0.56    inference(avatar_component_clause,[],[f445])).
% 0.22/0.56  fof(f498,plain,(
% 0.22/0.56    ~spl7_4 | spl7_47 | spl7_44),
% 0.22/0.56    inference(avatar_split_clause,[],[f494,f483,f496,f117])).
% 0.22/0.56  fof(f117,plain,(
% 0.22/0.56    spl7_4 <=> m1_subset_1(sK5,sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.56  fof(f483,plain,(
% 0.22/0.56    spl7_44 <=> r2_hidden(sK5,sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.22/0.56  fof(f494,plain,(
% 0.22/0.56    v1_xboole_0(sK1) | ~m1_subset_1(sK5,sK1) | spl7_44),
% 0.22/0.56    inference(resolution,[],[f484,f78])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.56    inference(flattening,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.56  fof(f484,plain,(
% 0.22/0.56    ~r2_hidden(sK5,sK1) | spl7_44),
% 0.22/0.56    inference(avatar_component_clause,[],[f483])).
% 0.22/0.56  fof(f485,plain,(
% 0.22/0.56    ~spl7_44 | spl7_28 | ~spl7_35),
% 0.22/0.56    inference(avatar_split_clause,[],[f476,f425,f372,f483])).
% 0.22/0.56  fof(f372,plain,(
% 0.22/0.56    spl7_28 <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.22/0.56  fof(f425,plain,(
% 0.22/0.56    spl7_35 <=> ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(k1_funct_1(sK3,X1),k1_relat_1(sK4)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.22/0.56  fof(f476,plain,(
% 0.22/0.56    ~r2_hidden(sK5,sK1) | (spl7_28 | ~spl7_35)),
% 0.22/0.56    inference(resolution,[],[f426,f373])).
% 0.22/0.56  fof(f373,plain,(
% 0.22/0.56    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | spl7_28),
% 0.22/0.56    inference(avatar_component_clause,[],[f372])).
% 0.22/0.56  fof(f426,plain,(
% 0.22/0.56    ( ! [X1] : (r2_hidden(k1_funct_1(sK3,X1),k1_relat_1(sK4)) | ~r2_hidden(X1,sK1)) ) | ~spl7_35),
% 0.22/0.56    inference(avatar_component_clause,[],[f425])).
% 0.22/0.56  fof(f447,plain,(
% 0.22/0.56    spl7_39 | ~spl7_13 | ~spl7_34),
% 0.22/0.56    inference(avatar_split_clause,[],[f443,f422,f181,f445])).
% 0.22/0.56  fof(f422,plain,(
% 0.22/0.56    spl7_34 <=> k1_xboole_0 = k1_relat_1(sK4)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.22/0.56  fof(f443,plain,(
% 0.22/0.56    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) | (~spl7_13 | ~spl7_34)),
% 0.22/0.56    inference(superposition,[],[f182,f423])).
% 0.22/0.56  fof(f423,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(sK4) | ~spl7_34),
% 0.22/0.56    inference(avatar_component_clause,[],[f422])).
% 0.22/0.56  fof(f436,plain,(
% 0.22/0.56    ~spl7_9 | spl7_37 | spl7_36),
% 0.22/0.56    inference(avatar_split_clause,[],[f431,f428,f434,f137])).
% 0.22/0.56  fof(f428,plain,(
% 0.22/0.56    spl7_36 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.22/0.56  fof(f431,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(sK3,sK1,X0) | ~v1_funct_1(sK3)) ) | spl7_36),
% 0.22/0.56    inference(resolution,[],[f429,f97])).
% 0.22/0.56  fof(f429,plain,(
% 0.22/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) | spl7_36),
% 0.22/0.56    inference(avatar_component_clause,[],[f428])).
% 0.22/0.56  fof(f430,plain,(
% 0.22/0.56    spl7_34 | spl7_35 | ~spl7_36 | ~spl7_13 | ~spl7_22),
% 0.22/0.56    inference(avatar_split_clause,[],[f409,f291,f181,f428,f425,f422])).
% 0.22/0.56  fof(f291,plain,(
% 0.22/0.56    spl7_22 <=> ! [X3,X2] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~r2_hidden(X3,sK1) | r2_hidden(k1_funct_1(sK3,X3),X2) | k1_xboole_0 = X2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.22/0.56  fof(f409,plain,(
% 0.22/0.56    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) | ~r2_hidden(X1,sK1) | r2_hidden(k1_funct_1(sK3,X1),k1_relat_1(sK4)) | k1_xboole_0 = k1_relat_1(sK4)) ) | (~spl7_13 | ~spl7_22)),
% 0.22/0.56    inference(resolution,[],[f292,f182])).
% 0.22/0.56  fof(f292,plain,(
% 0.22/0.56    ( ! [X2,X3] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~r2_hidden(X3,sK1) | r2_hidden(k1_funct_1(sK3,X3),X2) | k1_xboole_0 = X2) ) | ~spl7_22),
% 0.22/0.56    inference(avatar_component_clause,[],[f291])).
% 0.22/0.56  fof(f380,plain,(
% 0.22/0.56    ~spl7_5 | spl7_27),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f379])).
% 0.22/0.56  fof(f379,plain,(
% 0.22/0.56    $false | (~spl7_5 | spl7_27)),
% 0.22/0.56    inference(subsumption_resolution,[],[f122,f378])).
% 0.22/0.56  fof(f378,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | spl7_27),
% 0.22/0.56    inference(resolution,[],[f370,f91])).
% 0.22/0.56  fof(f91,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.22/0.56    inference(pure_predicate_removal,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.56  fof(f370,plain,(
% 0.22/0.56    ~v5_relat_1(sK4,sK0) | spl7_27),
% 0.22/0.56    inference(avatar_component_clause,[],[f369])).
% 0.22/0.56  fof(f369,plain,(
% 0.22/0.56    spl7_27 <=> v5_relat_1(sK4,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl7_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f121])).
% 0.22/0.56  fof(f121,plain,(
% 0.22/0.56    spl7_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.56  fof(f377,plain,(
% 0.22/0.56    ~spl7_5 | spl7_26),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f376])).
% 0.22/0.56  fof(f376,plain,(
% 0.22/0.56    $false | (~spl7_5 | spl7_26)),
% 0.22/0.56    inference(subsumption_resolution,[],[f122,f375])).
% 0.22/0.56  fof(f375,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_26),
% 0.22/0.56    inference(resolution,[],[f367,f89])).
% 0.22/0.56  fof(f89,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.56  fof(f367,plain,(
% 0.22/0.56    ~v1_relat_1(sK4) | spl7_26),
% 0.22/0.56    inference(avatar_component_clause,[],[f366])).
% 0.22/0.56  fof(f366,plain,(
% 0.22/0.56    spl7_26 <=> v1_relat_1(sK4)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.56  fof(f374,plain,(
% 0.22/0.56    ~spl7_26 | ~spl7_27 | ~spl7_6 | ~spl7_28 | spl7_25),
% 0.22/0.56    inference(avatar_split_clause,[],[f364,f360,f372,f125,f369,f366])).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    spl7_6 <=> v1_funct_1(sK4)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.56  fof(f360,plain,(
% 0.22/0.56    spl7_25 <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.22/0.56  fof(f364,plain,(
% 0.22/0.56    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,sK0) | ~v1_relat_1(sK4) | spl7_25),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f363])).
% 0.22/0.56  fof(f363,plain,(
% 0.22/0.56    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,sK0) | ~v1_relat_1(sK4) | spl7_25),
% 0.22/0.56    inference(superposition,[],[f361,f82])).
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 0.22/0.56  fof(f361,plain,(
% 0.22/0.56    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl7_25),
% 0.22/0.56    inference(avatar_component_clause,[],[f360])).
% 0.22/0.56  fof(f362,plain,(
% 0.22/0.56    spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_7 | ~spl7_6 | ~spl7_5 | ~spl7_4 | ~spl7_3 | spl7_2 | ~spl7_25 | spl7_1),
% 0.22/0.56    inference(avatar_split_clause,[],[f352,f105,f360,f109,f113,f117,f121,f125,f129,f133,f137,f141])).
% 0.22/0.56  fof(f113,plain,(
% 0.22/0.56    spl7_3 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    spl7_1 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.56  fof(f352,plain,(
% 0.22/0.56    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_xboole_0(sK2) | spl7_1),
% 0.22/0.56    inference(superposition,[],[f106,f88])).
% 0.22/0.56  fof(f88,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.22/0.56    inference(flattening,[],[f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.22/0.56    inference(ennf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) | spl7_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f105])).
% 0.22/0.56  fof(f313,plain,(
% 0.22/0.56    spl7_12),
% 0.22/0.56    inference(avatar_split_clause,[],[f312,f157])).
% 0.22/0.56  fof(f312,plain,(
% 0.22/0.56    v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    inference(global_subsumption,[],[f310])).
% 0.22/0.56  fof(f310,plain,(
% 0.22/0.56    v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    inference(global_subsumption,[],[f308])).
% 0.22/0.56  fof(f308,plain,(
% 0.22/0.56    v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    inference(global_subsumption,[],[f68,f172])).
% 0.22/0.56  fof(f172,plain,(
% 0.22/0.56    ( ! [X0] : (v1_xboole_0(k1_xboole_0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.56    inference(resolution,[],[f150,f147])).
% 0.22/0.56  fof(f147,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.56    inference(superposition,[],[f72,f99])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.56  fof(f150,plain,(
% 0.22/0.56    ( ! [X2,X3] : (r2_hidden(sK6(X2,X3),X2) | v1_xboole_0(X2) | ~r1_tarski(X2,X3)) )),
% 0.22/0.56    inference(resolution,[],[f76,f73])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f29,f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.56    inference(rectify,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.22/0.56    inference(flattening,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.56  fof(f293,plain,(
% 0.22/0.56    ~spl7_9 | spl7_22 | ~spl7_20),
% 0.22/0.56    inference(avatar_split_clause,[],[f285,f281,f291,f137])).
% 0.22/0.56  fof(f281,plain,(
% 0.22/0.56    spl7_20 <=> ! [X0] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | v1_funct_2(sK3,sK1,X0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.22/0.56  fof(f285,plain,(
% 0.22/0.56    ( ! [X2,X3] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) | k1_xboole_0 = X2 | ~r2_hidden(X3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | r2_hidden(k1_funct_1(sK3,X3),X2) | ~v1_funct_1(sK3)) ) | ~spl7_20),
% 0.22/0.56    inference(resolution,[],[f282,f92])).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_1(X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.56    inference(flattening,[],[f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.56    inference(ennf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.22/0.56  fof(f282,plain,(
% 0.22/0.56    ( ! [X0] : (v1_funct_2(sK3,sK1,X0) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)) ) | ~spl7_20),
% 0.22/0.56    inference(avatar_component_clause,[],[f281])).
% 0.22/0.56  fof(f283,plain,(
% 0.22/0.56    ~spl7_9 | ~spl7_7 | spl7_20 | spl7_17 | ~spl7_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f279,f133,f250,f281,f129,f137])).
% 0.22/0.56  fof(f279,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | v1_funct_2(sK3,sK1,X0) | ~v1_funct_1(sK3)) ) | ~spl7_8),
% 0.22/0.56    inference(resolution,[],[f95,f134])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f47])).
% 0.22/0.56  fof(f271,plain,(
% 0.22/0.56    k1_xboole_0 != sK2 | v1_xboole_0(sK2) | ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.56  fof(f183,plain,(
% 0.22/0.56    ~spl7_5 | spl7_13 | ~spl7_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f178,f113,f181,f121])).
% 0.22/0.56  fof(f178,plain,(
% 0.22/0.56    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl7_3),
% 0.22/0.56    inference(superposition,[],[f114,f90])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.56  fof(f114,plain,(
% 0.22/0.56    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl7_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f113])).
% 0.22/0.56  fof(f143,plain,(
% 0.22/0.56    ~spl7_10),
% 0.22/0.56    inference(avatar_split_clause,[],[f58,f141])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ~v1_xboole_0(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f25,f51,f50,f49,f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) => (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.22/0.56    inference(flattening,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.22/0.56    inference(ennf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.56    inference(negated_conjecture,[],[f20])).
% 0.22/0.56  fof(f20,conjecture,(
% 0.22/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 0.22/0.56  fof(f139,plain,(
% 0.22/0.56    spl7_9),
% 0.22/0.56    inference(avatar_split_clause,[],[f59,f137])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    v1_funct_1(sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f52])).
% 0.22/0.56  fof(f135,plain,(
% 0.22/0.56    spl7_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f60,f133])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f52])).
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    spl7_7),
% 0.22/0.56    inference(avatar_split_clause,[],[f61,f129])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.56    inference(cnf_transformation,[],[f52])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    spl7_6),
% 0.22/0.56    inference(avatar_split_clause,[],[f62,f125])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    v1_funct_1(sK4)),
% 0.22/0.56    inference(cnf_transformation,[],[f52])).
% 0.22/0.56  fof(f123,plain,(
% 0.22/0.56    spl7_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f63,f121])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.56    inference(cnf_transformation,[],[f52])).
% 0.22/0.56  fof(f119,plain,(
% 0.22/0.56    spl7_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f64,f117])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    m1_subset_1(sK5,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f52])).
% 0.22/0.56  fof(f115,plain,(
% 0.22/0.56    spl7_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f65,f113])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.56    inference(cnf_transformation,[],[f52])).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    ~spl7_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f66,f109])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    k1_xboole_0 != sK1),
% 0.22/0.56    inference(cnf_transformation,[],[f52])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    ~spl7_1),
% 0.22/0.56    inference(avatar_split_clause,[],[f67,f105])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.56    inference(cnf_transformation,[],[f52])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (10352)------------------------------
% 0.22/0.56  % (10352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (10352)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (10352)Memory used [KB]: 11129
% 0.22/0.56  % (10352)Time elapsed: 0.121 s
% 0.22/0.56  % (10352)------------------------------
% 0.22/0.56  % (10352)------------------------------
% 0.22/0.56  % (10345)Success in time 0.193 s
%------------------------------------------------------------------------------
