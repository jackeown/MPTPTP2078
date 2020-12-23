%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 154 expanded)
%              Number of leaves         :   26 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :  278 ( 555 expanded)
%              Number of equality atoms :   51 (  91 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f181,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f86,f96,f112,f120,f134,f140,f152,f166,f180])).

fof(f180,plain,
    ( sK3 != k1_relset_1(sK3,sK4,sK6)
    | k1_relset_1(sK3,sK4,sK6) != k1_relat_1(sK6)
    | r2_hidden(sK5,k1_relat_1(sK6))
    | ~ r2_hidden(sK5,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f166,plain,
    ( spl7_15
    | spl7_2
    | ~ spl7_5
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f157,f116,f78,f63,f163])).

fof(f163,plain,
    ( spl7_15
  <=> sK3 = k1_relset_1(sK3,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f63,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f78,plain,
    ( spl7_5
  <=> v1_funct_2(sK6,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f116,plain,
    ( spl7_10
  <=> sP1(sK3,sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f157,plain,
    ( sK3 = k1_relset_1(sK3,sK4,sK6)
    | spl7_2
    | ~ spl7_5
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f87,f118,f80,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f80,plain,
    ( v1_funct_2(sK6,sK3,sK4)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f118,plain,
    ( sP1(sK3,sK6,sK4)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f87,plain,
    ( ! [X0] : ~ sP0(X0,sK4)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f65,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f65,plain,
    ( k1_xboole_0 != sK4
    | spl7_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f152,plain,
    ( ~ spl7_14
    | ~ spl7_6
    | ~ spl7_7
    | spl7_12 ),
    inference(avatar_split_clause,[],[f151,f131,f91,f83,f146])).

fof(f146,plain,
    ( spl7_14
  <=> r2_hidden(sK5,k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f83,plain,
    ( spl7_6
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f91,plain,
    ( spl7_7
  <=> v1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f131,plain,
    ( spl7_12
  <=> r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f151,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK6))
    | ~ spl7_6
    | ~ spl7_7
    | spl7_12 ),
    inference(subsumption_resolution,[],[f150,f93])).

fof(f93,plain,
    ( v1_relat_1(sK6)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f150,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | ~ spl7_6
    | spl7_12 ),
    inference(subsumption_resolution,[],[f142,f85])).

fof(f85,plain,
    ( v1_funct_1(sK6)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f142,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl7_12 ),
    inference(resolution,[],[f40,f133])).

fof(f133,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f140,plain,
    ( spl7_13
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f135,f73,f137])).

fof(f137,plain,
    ( spl7_13
  <=> k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f73,plain,
    ( spl7_4
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f135,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f75,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f75,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f134,plain,
    ( ~ spl7_12
    | spl7_1
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f129,f108,f91,f58,f131])).

fof(f58,plain,
    ( spl7_1
  <=> r2_hidden(k1_funct_1(sK6,sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f108,plain,
    ( spl7_9
  <=> v5_relat_1(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f129,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6))
    | spl7_1
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f93,f110,f60,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(X1))
      | r2_hidden(X2,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

fof(f60,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK5),sK4)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f110,plain,
    ( v5_relat_1(sK6,sK4)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f108])).

fof(f120,plain,
    ( spl7_10
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f114,f73,f116])).

fof(f114,plain,
    ( sP1(sK3,sK6,sK4)
    | ~ spl7_4 ),
    inference(resolution,[],[f51,f75])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f20,f23,f22,f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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

fof(f112,plain,
    ( spl7_9
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f106,f73,f108])).

fof(f106,plain,
    ( v5_relat_1(sK6,sK4)
    | ~ spl7_4 ),
    inference(resolution,[],[f44,f75])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f96,plain,
    ( spl7_7
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f95,f73,f91])).

fof(f95,plain,
    ( v1_relat_1(sK6)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f89,f39])).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f89,plain,
    ( v1_relat_1(sK6)
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | ~ spl7_4 ),
    inference(resolution,[],[f38,f75])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f86,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f32,f83])).

fof(f32,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK5),sK4)
    & k1_xboole_0 != sK4
    & r2_hidden(sK5,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f11,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(k1_funct_1(sK6,sK5),sK4)
      & k1_xboole_0 != sK4
      & r2_hidden(sK5,sK3)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
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

fof(f81,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f33,f78])).

fof(f33,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f34,f73])).

fof(f34,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f35,f68])).

fof(f68,plain,
    ( spl7_3
  <=> r2_hidden(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f35,plain,(
    r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f36,f63])).

fof(f36,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f37,f58])).

fof(f37,plain,(
    ~ r2_hidden(k1_funct_1(sK6,sK5),sK4) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:08:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (2381)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.43  % (2381)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f181,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f86,f96,f112,f120,f134,f140,f152,f166,f180])).
% 0.21/0.43  fof(f180,plain,(
% 0.21/0.43    sK3 != k1_relset_1(sK3,sK4,sK6) | k1_relset_1(sK3,sK4,sK6) != k1_relat_1(sK6) | r2_hidden(sK5,k1_relat_1(sK6)) | ~r2_hidden(sK5,sK3)),
% 0.21/0.43    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.43  fof(f166,plain,(
% 0.21/0.43    spl7_15 | spl7_2 | ~spl7_5 | ~spl7_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f157,f116,f78,f63,f163])).
% 0.21/0.43  fof(f163,plain,(
% 0.21/0.43    spl7_15 <=> sK3 = k1_relset_1(sK3,sK4,sK6)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    spl7_2 <=> k1_xboole_0 = sK4),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    spl7_5 <=> v1_funct_2(sK6,sK3,sK4)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.43  fof(f116,plain,(
% 0.21/0.43    spl7_10 <=> sP1(sK3,sK6,sK4)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.43  fof(f157,plain,(
% 0.21/0.43    sK3 = k1_relset_1(sK3,sK4,sK6) | (spl7_2 | ~spl7_5 | ~spl7_10)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f87,f118,f80,f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.21/0.43    inference(rectify,[],[f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.43    inference(nnf_transformation,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.43    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    v1_funct_2(sK6,sK3,sK4) | ~spl7_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f78])).
% 0.21/0.43  fof(f118,plain,(
% 0.21/0.43    sP1(sK3,sK6,sK4) | ~spl7_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f116])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    ( ! [X0] : (~sP0(X0,sK4)) ) | spl7_2),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f65,f49])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.43    inference(cnf_transformation,[],[f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.43    inference(nnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.43    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    k1_xboole_0 != sK4 | spl7_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f63])).
% 0.21/0.43  fof(f152,plain,(
% 0.21/0.43    ~spl7_14 | ~spl7_6 | ~spl7_7 | spl7_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f151,f131,f91,f83,f146])).
% 0.21/0.43  fof(f146,plain,(
% 0.21/0.43    spl7_14 <=> r2_hidden(sK5,k1_relat_1(sK6))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    spl7_6 <=> v1_funct_1(sK6)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    spl7_7 <=> v1_relat_1(sK6)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.43  fof(f131,plain,(
% 0.21/0.43    spl7_12 <=> r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.43  fof(f151,plain,(
% 0.21/0.43    ~r2_hidden(sK5,k1_relat_1(sK6)) | (~spl7_6 | ~spl7_7 | spl7_12)),
% 0.21/0.43    inference(subsumption_resolution,[],[f150,f93])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    v1_relat_1(sK6) | ~spl7_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f91])).
% 0.21/0.43  fof(f150,plain,(
% 0.21/0.43    ~r2_hidden(sK5,k1_relat_1(sK6)) | ~v1_relat_1(sK6) | (~spl7_6 | spl7_12)),
% 0.21/0.43    inference(subsumption_resolution,[],[f142,f85])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    v1_funct_1(sK6) | ~spl7_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f83])).
% 0.21/0.43  fof(f142,plain,(
% 0.21/0.43    ~r2_hidden(sK5,k1_relat_1(sK6)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl7_12),
% 0.21/0.43    inference(resolution,[],[f40,f133])).
% 0.21/0.43  fof(f133,plain,(
% 0.21/0.43    ~r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) | spl7_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f131])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.21/0.43  fof(f140,plain,(
% 0.21/0.43    spl7_13 | ~spl7_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f135,f73,f137])).
% 0.21/0.43  fof(f137,plain,(
% 0.21/0.43    spl7_13 <=> k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    spl7_4 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.43  fof(f135,plain,(
% 0.21/0.43    k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) | ~spl7_4),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f75,f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~spl7_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f73])).
% 0.21/0.43  fof(f134,plain,(
% 0.21/0.43    ~spl7_12 | spl7_1 | ~spl7_7 | ~spl7_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f129,f108,f91,f58,f131])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    spl7_1 <=> r2_hidden(k1_funct_1(sK6,sK5),sK4)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.43  fof(f108,plain,(
% 0.21/0.43    spl7_9 <=> v5_relat_1(sK6,sK4)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.43  fof(f129,plain,(
% 0.21/0.43    ~r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) | (spl7_1 | ~spl7_7 | ~spl7_9)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f93,f110,f60,f41])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_relat_1(X1)) | r2_hidden(X2,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    ~r2_hidden(k1_funct_1(sK6,sK5),sK4) | spl7_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f58])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    v5_relat_1(sK6,sK4) | ~spl7_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f108])).
% 0.21/0.43  fof(f120,plain,(
% 0.21/0.43    spl7_10 | ~spl7_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f114,f73,f116])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    sP1(sK3,sK6,sK4) | ~spl7_4),
% 0.21/0.43    inference(resolution,[],[f51,f75])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(definition_folding,[],[f20,f23,f22,f21])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.21/0.43    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(flattening,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    spl7_9 | ~spl7_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f106,f73,f108])).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    v5_relat_1(sK6,sK4) | ~spl7_4),
% 0.21/0.43    inference(resolution,[],[f44,f75])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.43  fof(f96,plain,(
% 0.21/0.43    spl7_7 | ~spl7_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f95,f73,f91])).
% 0.21/0.43  fof(f95,plain,(
% 0.21/0.43    v1_relat_1(sK6) | ~spl7_4),
% 0.21/0.43    inference(subsumption_resolution,[],[f89,f39])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    v1_relat_1(sK6) | ~v1_relat_1(k2_zfmisc_1(sK3,sK4)) | ~spl7_4),
% 0.21/0.43    inference(resolution,[],[f38,f75])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    spl7_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f32,f83])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    v1_funct_1(sK6)),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ~r2_hidden(k1_funct_1(sK6,sK5),sK4) & k1_xboole_0 != sK4 & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f11,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(k1_funct_1(sK6,sK5),sK4) & k1_xboole_0 != sK4 & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.43    inference(flattening,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.43    inference(negated_conjecture,[],[f8])).
% 0.21/0.43  fof(f8,conjecture,(
% 0.21/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    spl7_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f33,f78])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    v1_funct_2(sK6,sK3,sK4)),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    spl7_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f34,f73])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    spl7_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f35,f68])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    spl7_3 <=> r2_hidden(sK5,sK3)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    r2_hidden(sK5,sK3)),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    ~spl7_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f36,f63])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    k1_xboole_0 != sK4),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    ~spl7_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f37,f58])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ~r2_hidden(k1_funct_1(sK6,sK5),sK4)),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (2381)------------------------------
% 0.21/0.43  % (2381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (2381)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (2381)Memory used [KB]: 10746
% 0.21/0.43  % (2381)Time elapsed: 0.009 s
% 0.21/0.43  % (2381)------------------------------
% 0.21/0.43  % (2381)------------------------------
% 0.21/0.43  % (2364)Success in time 0.082 s
%------------------------------------------------------------------------------
