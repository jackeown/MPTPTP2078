%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:51 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 188 expanded)
%              Number of leaves         :   31 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :  328 ( 497 expanded)
%              Number of equality atoms :   53 (  80 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f330,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f95,f105,f109,f113,f125,f129,f135,f146,f152,f159,f199,f226,f230,f276,f293,f324,f329])).

fof(f329,plain,
    ( spl7_5
    | ~ spl7_32 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl7_5
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f325,f108])).

fof(f108,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl7_5
  <=> sK1 = k1_funct_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f325,plain,
    ( sK1 = k1_funct_1(sK3,sK2)
    | ~ spl7_32 ),
    inference(resolution,[],[f323,f75])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f323,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k1_tarski(sK1))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl7_32
  <=> r2_hidden(k1_funct_1(sK3,sK2),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f324,plain,
    ( spl7_32
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f319,f274,f322])).

fof(f274,plain,
    ( spl7_30
  <=> m1_subset_1(k1_funct_1(sK3,sK2),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f319,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k1_tarski(sK1))
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f318,f59])).

fof(f59,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f318,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | r2_hidden(k1_funct_1(sK3,sK2),k1_tarski(sK1))
    | ~ spl7_30 ),
    inference(resolution,[],[f275,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f275,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK2),k1_tarski(sK1))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f274])).

fof(f293,plain,(
    ~ spl7_24 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f290,f63])).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f290,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | ~ spl7_24 ),
    inference(resolution,[],[f229,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f229,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl7_24
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f276,plain,
    ( spl7_30
    | ~ spl7_11
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f268,f224,f144,f274])).

fof(f144,plain,
    ( spl7_11
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f224,plain,
    ( spl7_23
  <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f268,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK2),k1_tarski(sK1))
    | ~ spl7_11
    | ~ spl7_23 ),
    inference(resolution,[],[f246,f145])).

fof(f145,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_tarski(sK1)))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f144])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(X0))
        | m1_subset_1(k1_funct_1(sK3,sK2),X0) )
    | ~ spl7_23 ),
    inference(resolution,[],[f225,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f225,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f224])).

fof(f230,plain,
    ( spl7_24
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f171,f157,f228])).

fof(f157,plain,
    ( spl7_14
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f171,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl7_14 ),
    inference(superposition,[],[f77,f158])).

fof(f158,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f157])).

fof(f77,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f226,plain,
    ( spl7_23
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f220,f195,f123,f93,f89,f224])).

fof(f89,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f93,plain,
    ( spl7_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f123,plain,
    ( spl7_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f195,plain,
    ( spl7_21
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f220,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_21 ),
    inference(resolution,[],[f217,f94])).

fof(f94,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) )
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f216,f124])).

fof(f124,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK3)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) )
    | ~ spl7_1
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f215,f90])).

fof(f90,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) )
    | ~ spl7_21 ),
    inference(superposition,[],[f46,f196])).

fof(f196,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f195])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f199,plain,
    ( spl7_21
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f197,f154,f150,f195])).

fof(f150,plain,
    ( spl7_12
  <=> k1_relset_1(sK0,k1_tarski(sK1),sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f154,plain,
    ( spl7_13
  <=> sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f197,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(superposition,[],[f155,f151])).

fof(f151,plain,
    ( k1_relset_1(sK0,k1_tarski(sK1),sK3) = k1_relat_1(sK3)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f150])).

fof(f155,plain,
    ( sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f159,plain,
    ( spl7_13
    | spl7_14
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f121,f111,f103,f157,f154])).

fof(f103,plain,
    ( spl7_4
  <=> v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f111,plain,
    ( spl7_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f121,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f117,f104])).

fof(f104,plain,
    ( v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f117,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)
    | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl7_6 ),
    inference(resolution,[],[f112,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f112,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f152,plain,
    ( spl7_12
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f115,f111,f150])).

fof(f115,plain,
    ( k1_relset_1(sK0,k1_tarski(sK1),sK3) = k1_relat_1(sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f112,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f146,plain,
    ( spl7_11
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f141,f133,f144])).

fof(f133,plain,
    ( spl7_9
  <=> r1_tarski(k2_relat_1(sK3),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f141,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_tarski(sK1)))
    | ~ spl7_9 ),
    inference(resolution,[],[f134,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f134,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_tarski(sK1))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f135,plain,
    ( spl7_9
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f131,f127,f123,f133])).

fof(f127,plain,
    ( spl7_8
  <=> v5_relat_1(sK3,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f131,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_tarski(sK1))
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f130,f124])).

fof(f130,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_tarski(sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl7_8 ),
    inference(resolution,[],[f128,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f128,plain,
    ( v5_relat_1(sK3,k1_tarski(sK1))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f129,plain,
    ( spl7_8
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f114,f111,f127])).

fof(f114,plain,
    ( v5_relat_1(sK3,k1_tarski(sK1))
    | ~ spl7_6 ),
    inference(resolution,[],[f112,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f125,plain,
    ( spl7_7
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f118,f111,f123])).

fof(f118,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f112,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f113,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f39,f111])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f109,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f41,f107])).

fof(f41,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f105,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f38,f103])).

fof(f38,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f95,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f40,f93])).

fof(f40,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f91,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f37,f89])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (803700737)
% 0.13/0.36  ipcrm: permission denied for id (802422787)
% 0.13/0.37  ipcrm: permission denied for id (803831814)
% 0.13/0.37  ipcrm: permission denied for id (803897352)
% 0.13/0.37  ipcrm: permission denied for id (802455562)
% 0.13/0.37  ipcrm: permission denied for id (803962891)
% 0.13/0.37  ipcrm: permission denied for id (803995660)
% 0.13/0.38  ipcrm: permission denied for id (804061198)
% 0.13/0.38  ipcrm: permission denied for id (804126736)
% 0.13/0.38  ipcrm: permission denied for id (802553876)
% 0.13/0.39  ipcrm: permission denied for id (804356119)
% 0.13/0.39  ipcrm: permission denied for id (804454426)
% 0.13/0.39  ipcrm: permission denied for id (802619420)
% 0.13/0.39  ipcrm: permission denied for id (802652189)
% 0.13/0.40  ipcrm: permission denied for id (804519966)
% 0.20/0.40  ipcrm: permission denied for id (804651042)
% 0.20/0.41  ipcrm: permission denied for id (804814887)
% 0.20/0.41  ipcrm: permission denied for id (802750504)
% 0.20/0.41  ipcrm: permission denied for id (804945964)
% 0.20/0.42  ipcrm: permission denied for id (802848815)
% 0.20/0.42  ipcrm: permission denied for id (805044272)
% 0.20/0.42  ipcrm: permission denied for id (805077041)
% 0.20/0.42  ipcrm: permission denied for id (802881587)
% 0.20/0.42  ipcrm: permission denied for id (805142580)
% 0.20/0.42  ipcrm: permission denied for id (805175349)
% 0.20/0.42  ipcrm: permission denied for id (805208118)
% 0.20/0.43  ipcrm: permission denied for id (805273656)
% 0.20/0.43  ipcrm: permission denied for id (805306425)
% 0.20/0.43  ipcrm: permission denied for id (805339194)
% 0.20/0.43  ipcrm: permission denied for id (805404732)
% 0.20/0.43  ipcrm: permission denied for id (802979901)
% 0.20/0.44  ipcrm: permission denied for id (805470271)
% 0.20/0.44  ipcrm: permission denied for id (803045440)
% 0.20/0.44  ipcrm: permission denied for id (803078213)
% 0.20/0.45  ipcrm: permission denied for id (803143756)
% 0.20/0.45  ipcrm: permission denied for id (805863502)
% 0.20/0.45  ipcrm: permission denied for id (805929040)
% 0.20/0.46  ipcrm: permission denied for id (806027347)
% 0.20/0.46  ipcrm: permission denied for id (806092885)
% 0.20/0.46  ipcrm: permission denied for id (806125654)
% 0.20/0.46  ipcrm: permission denied for id (806158423)
% 0.20/0.46  ipcrm: permission denied for id (806191192)
% 0.20/0.47  ipcrm: permission denied for id (806289499)
% 0.20/0.47  ipcrm: permission denied for id (803209309)
% 0.20/0.47  ipcrm: permission denied for id (806355038)
% 0.20/0.47  ipcrm: permission denied for id (806387807)
% 0.20/0.48  ipcrm: permission denied for id (803274850)
% 0.20/0.48  ipcrm: permission denied for id (806486115)
% 0.20/0.48  ipcrm: permission denied for id (803307622)
% 0.20/0.48  ipcrm: permission denied for id (806584423)
% 0.20/0.48  ipcrm: permission denied for id (803340392)
% 0.20/0.49  ipcrm: permission denied for id (806649962)
% 0.20/0.49  ipcrm: permission denied for id (806715500)
% 0.20/0.49  ipcrm: permission denied for id (806748269)
% 0.20/0.49  ipcrm: permission denied for id (806781038)
% 0.20/0.49  ipcrm: permission denied for id (806879344)
% 0.20/0.50  ipcrm: permission denied for id (803471473)
% 0.20/0.50  ipcrm: permission denied for id (803569780)
% 0.20/0.50  ipcrm: permission denied for id (807010422)
% 0.20/0.51  ipcrm: permission denied for id (807239805)
% 1.06/0.64  % (6063)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.06/0.64  % (6036)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.06/0.65  % (6054)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.06/0.65  % (6054)Refutation not found, incomplete strategy% (6054)------------------------------
% 1.06/0.65  % (6054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.06/0.65  % (6054)Termination reason: Refutation not found, incomplete strategy
% 1.06/0.65  
% 1.06/0.65  % (6054)Memory used [KB]: 1791
% 1.06/0.65  % (6054)Time elapsed: 0.103 s
% 1.06/0.65  % (6054)------------------------------
% 1.06/0.65  % (6054)------------------------------
% 1.23/0.66  % (6045)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.23/0.66  % (6059)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.23/0.66  % (6040)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.67  % (6063)Refutation found. Thanks to Tanya!
% 1.23/0.67  % SZS status Theorem for theBenchmark
% 1.23/0.67  % SZS output start Proof for theBenchmark
% 1.23/0.67  fof(f330,plain,(
% 1.23/0.67    $false),
% 1.23/0.67    inference(avatar_sat_refutation,[],[f91,f95,f105,f109,f113,f125,f129,f135,f146,f152,f159,f199,f226,f230,f276,f293,f324,f329])).
% 1.23/0.67  fof(f329,plain,(
% 1.23/0.67    spl7_5 | ~spl7_32),
% 1.23/0.67    inference(avatar_contradiction_clause,[],[f328])).
% 1.23/0.67  fof(f328,plain,(
% 1.23/0.67    $false | (spl7_5 | ~spl7_32)),
% 1.23/0.67    inference(subsumption_resolution,[],[f325,f108])).
% 1.23/0.67  fof(f108,plain,(
% 1.23/0.67    sK1 != k1_funct_1(sK3,sK2) | spl7_5),
% 1.23/0.67    inference(avatar_component_clause,[],[f107])).
% 1.23/0.67  fof(f107,plain,(
% 1.23/0.67    spl7_5 <=> sK1 = k1_funct_1(sK3,sK2)),
% 1.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.23/0.67  fof(f325,plain,(
% 1.23/0.67    sK1 = k1_funct_1(sK3,sK2) | ~spl7_32),
% 1.23/0.67    inference(resolution,[],[f323,f75])).
% 1.23/0.67  fof(f75,plain,(
% 1.23/0.67    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.23/0.67    inference(equality_resolution,[],[f43])).
% 1.23/0.67  fof(f43,plain,(
% 1.23/0.67    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.23/0.67    inference(cnf_transformation,[],[f3])).
% 1.23/0.67  fof(f3,axiom,(
% 1.23/0.67    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.23/0.67  fof(f323,plain,(
% 1.23/0.67    r2_hidden(k1_funct_1(sK3,sK2),k1_tarski(sK1)) | ~spl7_32),
% 1.23/0.67    inference(avatar_component_clause,[],[f322])).
% 1.23/0.67  fof(f322,plain,(
% 1.23/0.67    spl7_32 <=> r2_hidden(k1_funct_1(sK3,sK2),k1_tarski(sK1))),
% 1.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 1.23/0.67  fof(f324,plain,(
% 1.23/0.67    spl7_32 | ~spl7_30),
% 1.23/0.67    inference(avatar_split_clause,[],[f319,f274,f322])).
% 1.23/0.67  fof(f274,plain,(
% 1.23/0.67    spl7_30 <=> m1_subset_1(k1_funct_1(sK3,sK2),k1_tarski(sK1))),
% 1.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 1.23/0.67  fof(f319,plain,(
% 1.23/0.67    r2_hidden(k1_funct_1(sK3,sK2),k1_tarski(sK1)) | ~spl7_30),
% 1.23/0.67    inference(subsumption_resolution,[],[f318,f59])).
% 1.23/0.67  fof(f59,plain,(
% 1.23/0.67    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.23/0.67    inference(cnf_transformation,[],[f7])).
% 1.23/0.67  fof(f7,axiom,(
% 1.23/0.67    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.23/0.67  fof(f318,plain,(
% 1.23/0.67    v1_xboole_0(k1_tarski(sK1)) | r2_hidden(k1_funct_1(sK3,sK2),k1_tarski(sK1)) | ~spl7_30),
% 1.23/0.67    inference(resolution,[],[f275,f65])).
% 1.23/0.67  fof(f65,plain,(
% 1.23/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f34])).
% 1.23/0.67  fof(f34,plain,(
% 1.23/0.67    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.23/0.67    inference(flattening,[],[f33])).
% 1.23/0.67  fof(f33,plain,(
% 1.23/0.67    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.23/0.67    inference(ennf_transformation,[],[f8])).
% 1.23/0.67  fof(f8,axiom,(
% 1.23/0.67    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.23/0.67  fof(f275,plain,(
% 1.23/0.67    m1_subset_1(k1_funct_1(sK3,sK2),k1_tarski(sK1)) | ~spl7_30),
% 1.23/0.67    inference(avatar_component_clause,[],[f274])).
% 1.23/0.67  fof(f293,plain,(
% 1.23/0.67    ~spl7_24),
% 1.23/0.67    inference(avatar_contradiction_clause,[],[f292])).
% 1.23/0.67  fof(f292,plain,(
% 1.23/0.67    $false | ~spl7_24),
% 1.23/0.67    inference(subsumption_resolution,[],[f290,f63])).
% 1.23/0.67  fof(f63,plain,(
% 1.23/0.67    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f1])).
% 1.23/0.67  fof(f1,axiom,(
% 1.23/0.67    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.23/0.67  fof(f290,plain,(
% 1.23/0.67    ~r1_tarski(k1_xboole_0,sK1) | ~spl7_24),
% 1.23/0.67    inference(resolution,[],[f229,f48])).
% 1.23/0.67  fof(f48,plain,(
% 1.23/0.67    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f27])).
% 1.23/0.67  fof(f27,plain,(
% 1.23/0.67    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.23/0.67    inference(ennf_transformation,[],[f13])).
% 1.23/0.67  fof(f13,axiom,(
% 1.23/0.67    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.23/0.67  fof(f229,plain,(
% 1.23/0.67    r2_hidden(sK1,k1_xboole_0) | ~spl7_24),
% 1.23/0.67    inference(avatar_component_clause,[],[f228])).
% 1.23/0.67  fof(f228,plain,(
% 1.23/0.67    spl7_24 <=> r2_hidden(sK1,k1_xboole_0)),
% 1.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 1.23/0.67  fof(f276,plain,(
% 1.23/0.67    spl7_30 | ~spl7_11 | ~spl7_23),
% 1.23/0.67    inference(avatar_split_clause,[],[f268,f224,f144,f274])).
% 1.23/0.67  fof(f144,plain,(
% 1.23/0.67    spl7_11 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_tarski(sK1)))),
% 1.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.23/0.67  fof(f224,plain,(
% 1.23/0.67    spl7_23 <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))),
% 1.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 1.23/0.67  fof(f268,plain,(
% 1.23/0.67    m1_subset_1(k1_funct_1(sK3,sK2),k1_tarski(sK1)) | (~spl7_11 | ~spl7_23)),
% 1.23/0.67    inference(resolution,[],[f246,f145])).
% 1.23/0.67  fof(f145,plain,(
% 1.23/0.67    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_tarski(sK1))) | ~spl7_11),
% 1.23/0.67    inference(avatar_component_clause,[],[f144])).
% 1.23/0.67  fof(f246,plain,(
% 1.23/0.67    ( ! [X0] : (~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(X0)) | m1_subset_1(k1_funct_1(sK3,sK2),X0)) ) | ~spl7_23),
% 1.23/0.67    inference(resolution,[],[f225,f47])).
% 1.23/0.67  fof(f47,plain,(
% 1.23/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f26])).
% 1.23/0.67  fof(f26,plain,(
% 1.23/0.67    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.23/0.67    inference(flattening,[],[f25])).
% 1.23/0.67  fof(f25,plain,(
% 1.23/0.67    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.23/0.67    inference(ennf_transformation,[],[f10])).
% 1.23/0.67  fof(f10,axiom,(
% 1.23/0.67    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.23/0.67  fof(f225,plain,(
% 1.23/0.67    r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) | ~spl7_23),
% 1.23/0.67    inference(avatar_component_clause,[],[f224])).
% 1.23/0.67  fof(f230,plain,(
% 1.23/0.67    spl7_24 | ~spl7_14),
% 1.23/0.67    inference(avatar_split_clause,[],[f171,f157,f228])).
% 1.23/0.67  fof(f157,plain,(
% 1.23/0.67    spl7_14 <=> k1_xboole_0 = k1_tarski(sK1)),
% 1.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.23/0.67  fof(f171,plain,(
% 1.23/0.67    r2_hidden(sK1,k1_xboole_0) | ~spl7_14),
% 1.23/0.67    inference(superposition,[],[f77,f158])).
% 1.23/0.67  fof(f158,plain,(
% 1.23/0.67    k1_xboole_0 = k1_tarski(sK1) | ~spl7_14),
% 1.23/0.67    inference(avatar_component_clause,[],[f157])).
% 1.23/0.67  fof(f77,plain,(
% 1.23/0.67    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 1.23/0.67    inference(equality_resolution,[],[f76])).
% 1.23/0.67  fof(f76,plain,(
% 1.23/0.67    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 1.23/0.67    inference(equality_resolution,[],[f42])).
% 1.23/0.67  fof(f42,plain,(
% 1.23/0.67    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.23/0.67    inference(cnf_transformation,[],[f3])).
% 1.23/0.67  fof(f226,plain,(
% 1.23/0.67    spl7_23 | ~spl7_1 | ~spl7_2 | ~spl7_7 | ~spl7_21),
% 1.23/0.67    inference(avatar_split_clause,[],[f220,f195,f123,f93,f89,f224])).
% 1.23/0.67  fof(f89,plain,(
% 1.23/0.67    spl7_1 <=> v1_funct_1(sK3)),
% 1.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.23/0.67  fof(f93,plain,(
% 1.23/0.67    spl7_2 <=> r2_hidden(sK2,sK0)),
% 1.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.23/0.67  fof(f123,plain,(
% 1.23/0.67    spl7_7 <=> v1_relat_1(sK3)),
% 1.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.23/0.67  fof(f195,plain,(
% 1.23/0.67    spl7_21 <=> sK0 = k1_relat_1(sK3)),
% 1.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 1.23/0.67  fof(f220,plain,(
% 1.23/0.67    r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) | (~spl7_1 | ~spl7_2 | ~spl7_7 | ~spl7_21)),
% 1.23/0.67    inference(resolution,[],[f217,f94])).
% 1.23/0.67  fof(f94,plain,(
% 1.23/0.67    r2_hidden(sK2,sK0) | ~spl7_2),
% 1.23/0.67    inference(avatar_component_clause,[],[f93])).
% 1.23/0.67  fof(f217,plain,(
% 1.23/0.67    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))) ) | (~spl7_1 | ~spl7_7 | ~spl7_21)),
% 1.23/0.67    inference(subsumption_resolution,[],[f216,f124])).
% 1.23/0.67  fof(f124,plain,(
% 1.23/0.67    v1_relat_1(sK3) | ~spl7_7),
% 1.23/0.67    inference(avatar_component_clause,[],[f123])).
% 1.23/0.67  fof(f216,plain,(
% 1.23/0.67    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK3) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))) ) | (~spl7_1 | ~spl7_21)),
% 1.23/0.67    inference(subsumption_resolution,[],[f215,f90])).
% 1.23/0.67  fof(f90,plain,(
% 1.23/0.67    v1_funct_1(sK3) | ~spl7_1),
% 1.23/0.67    inference(avatar_component_clause,[],[f89])).
% 1.23/0.67  fof(f215,plain,(
% 1.23/0.67    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))) ) | ~spl7_21),
% 1.23/0.67    inference(superposition,[],[f46,f196])).
% 1.23/0.67  fof(f196,plain,(
% 1.23/0.67    sK0 = k1_relat_1(sK3) | ~spl7_21),
% 1.23/0.67    inference(avatar_component_clause,[],[f195])).
% 1.23/0.67  fof(f46,plain,(
% 1.23/0.67    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))) )),
% 1.23/0.67    inference(cnf_transformation,[],[f24])).
% 1.23/0.67  fof(f24,plain,(
% 1.23/0.67    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.23/0.67    inference(flattening,[],[f23])).
% 1.23/0.67  fof(f23,plain,(
% 1.23/0.67    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.23/0.67    inference(ennf_transformation,[],[f12])).
% 1.23/0.67  fof(f12,axiom,(
% 1.23/0.67    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 1.23/0.67  fof(f199,plain,(
% 1.23/0.67    spl7_21 | ~spl7_12 | ~spl7_13),
% 1.23/0.67    inference(avatar_split_clause,[],[f197,f154,f150,f195])).
% 1.23/0.67  fof(f150,plain,(
% 1.23/0.67    spl7_12 <=> k1_relset_1(sK0,k1_tarski(sK1),sK3) = k1_relat_1(sK3)),
% 1.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.23/0.67  fof(f154,plain,(
% 1.23/0.67    spl7_13 <=> sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)),
% 1.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.23/0.67  fof(f197,plain,(
% 1.23/0.67    sK0 = k1_relat_1(sK3) | (~spl7_12 | ~spl7_13)),
% 1.23/0.67    inference(superposition,[],[f155,f151])).
% 1.23/0.67  fof(f151,plain,(
% 1.23/0.67    k1_relset_1(sK0,k1_tarski(sK1),sK3) = k1_relat_1(sK3) | ~spl7_12),
% 1.23/0.67    inference(avatar_component_clause,[],[f150])).
% 1.23/0.67  fof(f155,plain,(
% 1.23/0.67    sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) | ~spl7_13),
% 1.23/0.67    inference(avatar_component_clause,[],[f154])).
% 1.23/0.67  fof(f159,plain,(
% 1.23/0.67    spl7_13 | spl7_14 | ~spl7_4 | ~spl7_6),
% 1.23/0.67    inference(avatar_split_clause,[],[f121,f111,f103,f157,f154])).
% 1.23/0.67  fof(f103,plain,(
% 1.23/0.67    spl7_4 <=> v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.23/0.67  fof(f111,plain,(
% 1.23/0.67    spl7_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.23/0.67  fof(f121,plain,(
% 1.23/0.67    k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) | (~spl7_4 | ~spl7_6)),
% 1.23/0.67    inference(subsumption_resolution,[],[f117,f104])).
% 1.23/0.67  fof(f104,plain,(
% 1.23/0.67    v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~spl7_4),
% 1.23/0.67    inference(avatar_component_clause,[],[f103])).
% 1.23/0.67  fof(f117,plain,(
% 1.23/0.67    k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~spl7_6),
% 1.23/0.67    inference(resolution,[],[f112,f57])).
% 1.23/0.67  fof(f57,plain,(
% 1.23/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f30])).
% 1.23/0.67  fof(f30,plain,(
% 1.23/0.67    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.67    inference(flattening,[],[f29])).
% 1.23/0.67  fof(f29,plain,(
% 1.23/0.67    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.67    inference(ennf_transformation,[],[f17])).
% 1.23/0.67  fof(f17,axiom,(
% 1.23/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.23/0.67  fof(f112,plain,(
% 1.23/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl7_6),
% 1.23/0.67    inference(avatar_component_clause,[],[f111])).
% 1.23/0.67  fof(f152,plain,(
% 1.23/0.67    spl7_12 | ~spl7_6),
% 1.23/0.67    inference(avatar_split_clause,[],[f115,f111,f150])).
% 1.23/0.67  fof(f115,plain,(
% 1.23/0.67    k1_relset_1(sK0,k1_tarski(sK1),sK3) = k1_relat_1(sK3) | ~spl7_6),
% 1.23/0.67    inference(resolution,[],[f112,f62])).
% 1.23/0.67  fof(f62,plain,(
% 1.23/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f32])).
% 1.23/0.67  fof(f32,plain,(
% 1.23/0.67    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.67    inference(ennf_transformation,[],[f16])).
% 1.23/0.67  fof(f16,axiom,(
% 1.23/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.23/0.67  fof(f146,plain,(
% 1.23/0.67    spl7_11 | ~spl7_9),
% 1.23/0.67    inference(avatar_split_clause,[],[f141,f133,f144])).
% 1.23/0.67  fof(f133,plain,(
% 1.23/0.67    spl7_9 <=> r1_tarski(k2_relat_1(sK3),k1_tarski(sK1))),
% 1.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.23/0.67  fof(f141,plain,(
% 1.23/0.67    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_tarski(sK1))) | ~spl7_9),
% 1.23/0.67    inference(resolution,[],[f134,f49])).
% 1.23/0.67  fof(f49,plain,(
% 1.23/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.23/0.67    inference(cnf_transformation,[],[f9])).
% 1.23/0.67  fof(f9,axiom,(
% 1.23/0.67    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.23/0.67  fof(f134,plain,(
% 1.23/0.67    r1_tarski(k2_relat_1(sK3),k1_tarski(sK1)) | ~spl7_9),
% 1.23/0.67    inference(avatar_component_clause,[],[f133])).
% 1.23/0.67  fof(f135,plain,(
% 1.23/0.67    spl7_9 | ~spl7_7 | ~spl7_8),
% 1.23/0.67    inference(avatar_split_clause,[],[f131,f127,f123,f133])).
% 1.23/0.67  fof(f127,plain,(
% 1.23/0.67    spl7_8 <=> v5_relat_1(sK3,k1_tarski(sK1))),
% 1.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.23/0.67  fof(f131,plain,(
% 1.23/0.67    r1_tarski(k2_relat_1(sK3),k1_tarski(sK1)) | (~spl7_7 | ~spl7_8)),
% 1.23/0.67    inference(subsumption_resolution,[],[f130,f124])).
% 1.23/0.67  fof(f130,plain,(
% 1.23/0.67    r1_tarski(k2_relat_1(sK3),k1_tarski(sK1)) | ~v1_relat_1(sK3) | ~spl7_8),
% 1.23/0.67    inference(resolution,[],[f128,f61])).
% 1.23/0.67  fof(f61,plain,(
% 1.23/0.67    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f31])).
% 1.23/0.67  fof(f31,plain,(
% 1.23/0.67    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.23/0.67    inference(ennf_transformation,[],[f11])).
% 1.23/0.67  fof(f11,axiom,(
% 1.23/0.67    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.23/0.67  fof(f128,plain,(
% 1.23/0.67    v5_relat_1(sK3,k1_tarski(sK1)) | ~spl7_8),
% 1.23/0.67    inference(avatar_component_clause,[],[f127])).
% 1.23/0.67  fof(f129,plain,(
% 1.23/0.67    spl7_8 | ~spl7_6),
% 1.23/0.67    inference(avatar_split_clause,[],[f114,f111,f127])).
% 1.23/0.67  fof(f114,plain,(
% 1.23/0.67    v5_relat_1(sK3,k1_tarski(sK1)) | ~spl7_6),
% 1.23/0.67    inference(resolution,[],[f112,f66])).
% 1.23/0.67  fof(f66,plain,(
% 1.23/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f35])).
% 1.23/0.67  fof(f35,plain,(
% 1.23/0.67    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.67    inference(ennf_transformation,[],[f20])).
% 1.23/0.67  fof(f20,plain,(
% 1.23/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.23/0.67    inference(pure_predicate_removal,[],[f15])).
% 1.23/0.67  fof(f15,axiom,(
% 1.23/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.23/0.67  fof(f125,plain,(
% 1.23/0.67    spl7_7 | ~spl7_6),
% 1.23/0.67    inference(avatar_split_clause,[],[f118,f111,f123])).
% 1.23/0.67  fof(f118,plain,(
% 1.23/0.67    v1_relat_1(sK3) | ~spl7_6),
% 1.23/0.67    inference(resolution,[],[f112,f51])).
% 1.23/0.67  fof(f51,plain,(
% 1.23/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f28])).
% 1.23/0.67  fof(f28,plain,(
% 1.23/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.67    inference(ennf_transformation,[],[f14])).
% 1.23/0.67  fof(f14,axiom,(
% 1.23/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.23/0.67  fof(f113,plain,(
% 1.23/0.67    spl7_6),
% 1.23/0.67    inference(avatar_split_clause,[],[f39,f111])).
% 1.23/0.67  fof(f39,plain,(
% 1.23/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.23/0.67    inference(cnf_transformation,[],[f22])).
% 1.23/0.67  fof(f22,plain,(
% 1.23/0.67    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.23/0.67    inference(flattening,[],[f21])).
% 1.23/0.67  fof(f21,plain,(
% 1.23/0.67    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.23/0.67    inference(ennf_transformation,[],[f19])).
% 1.23/0.67  fof(f19,negated_conjecture,(
% 1.23/0.67    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.23/0.67    inference(negated_conjecture,[],[f18])).
% 1.23/0.67  fof(f18,conjecture,(
% 1.23/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 1.23/0.67  fof(f109,plain,(
% 1.23/0.67    ~spl7_5),
% 1.23/0.67    inference(avatar_split_clause,[],[f41,f107])).
% 1.23/0.67  fof(f41,plain,(
% 1.23/0.67    sK1 != k1_funct_1(sK3,sK2)),
% 1.23/0.67    inference(cnf_transformation,[],[f22])).
% 1.23/0.67  fof(f105,plain,(
% 1.23/0.67    spl7_4),
% 1.23/0.67    inference(avatar_split_clause,[],[f38,f103])).
% 1.23/0.67  fof(f38,plain,(
% 1.23/0.67    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.23/0.67    inference(cnf_transformation,[],[f22])).
% 1.23/0.67  fof(f95,plain,(
% 1.23/0.67    spl7_2),
% 1.23/0.67    inference(avatar_split_clause,[],[f40,f93])).
% 1.23/0.67  fof(f40,plain,(
% 1.23/0.67    r2_hidden(sK2,sK0)),
% 1.23/0.67    inference(cnf_transformation,[],[f22])).
% 1.23/0.67  fof(f91,plain,(
% 1.23/0.67    spl7_1),
% 1.23/0.67    inference(avatar_split_clause,[],[f37,f89])).
% 1.23/0.67  fof(f37,plain,(
% 1.23/0.67    v1_funct_1(sK3)),
% 1.23/0.67    inference(cnf_transformation,[],[f22])).
% 1.23/0.67  % SZS output end Proof for theBenchmark
% 1.23/0.67  % (6063)------------------------------
% 1.23/0.67  % (6063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.67  % (6063)Termination reason: Refutation
% 1.23/0.67  
% 1.23/0.67  % (6063)Memory used [KB]: 6396
% 1.23/0.67  % (6063)Time elapsed: 0.113 s
% 1.23/0.67  % (6063)------------------------------
% 1.23/0.67  % (6063)------------------------------
% 1.23/0.67  % (5883)Success in time 0.311 s
%------------------------------------------------------------------------------
