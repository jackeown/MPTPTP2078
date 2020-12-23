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
% DateTime   : Thu Dec  3 13:03:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 204 expanded)
%              Number of leaves         :   30 (  94 expanded)
%              Depth                    :   10
%              Number of atoms          :  403 ( 986 expanded)
%              Number of equality atoms :   82 ( 215 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f71,f75,f79,f83,f87,f91,f95,f101,f109,f115,f118,f126,f172,f180,f181,f204,f214])).

fof(f214,plain,
    ( ~ spl7_3
    | ~ spl7_4
    | spl7_9
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f208,f202,f124,f99,f77,f73])).

fof(f73,plain,
    ( spl7_3
  <=> r2_hidden(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f77,plain,
    ( spl7_4
  <=> r2_hidden(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f99,plain,
    ( spl7_9
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f124,plain,
    ( spl7_14
  <=> r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f202,plain,
    ( spl7_25
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,X2)
        | r2_hidden(X1,k9_relat_1(sK3,X2))
        | ~ r2_hidden(k4_tarski(X0,X1),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f208,plain,
    ( ~ r2_hidden(sK5,sK0)
    | ~ r2_hidden(sK5,sK2)
    | spl7_9
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(resolution,[],[f206,f125])).

fof(f125,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f124])).

fof(f206,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_tarski(X1,sK4),sK3)
        | ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X1,sK2) )
    | spl7_9
    | ~ spl7_25 ),
    inference(resolution,[],[f203,f100])).

fof(f100,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f203,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X1,k9_relat_1(sK3,X2))
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK3) )
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f202])).

fof(f204,plain,
    ( ~ spl7_12
    | spl7_25
    | ~ spl7_6
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f200,f177,f85,f202,f113])).

fof(f113,plain,
    ( spl7_12
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f85,plain,
    ( spl7_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f177,plain,
    ( spl7_21
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f200,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | r2_hidden(X1,k9_relat_1(sK3,X2))
        | ~ r2_hidden(X0,X2)
        | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl7_6
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f199,f178])).

fof(f178,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f177])).

fof(f199,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(X1,k9_relat_1(sK3,X2))
        | ~ r2_hidden(X0,X2)
        | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f163,f86])).

fof(f86,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f163,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
      | ~ r2_hidden(k4_tarski(X5,X7),X8)
      | ~ r2_hidden(X5,k1_relat_1(X8))
      | r2_hidden(X7,k9_relat_1(X8,X6))
      | ~ r2_hidden(X5,X6)
      | ~ v1_relat_1(X9) ) ),
    inference(resolution,[],[f47,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
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

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
            & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f181,plain,
    ( sK0 != k1_relat_1(sK3)
    | r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK5,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f180,plain,
    ( ~ spl7_6
    | spl7_21
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f174,f168,f177,f85])).

fof(f168,plain,
    ( spl7_20
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f174,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_20 ),
    inference(superposition,[],[f48,f169])).

fof(f169,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f168])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f172,plain,
    ( spl7_20
    | spl7_5
    | ~ spl7_7
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f166,f85,f89,f81,f168])).

fof(f81,plain,
    ( spl7_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f89,plain,
    ( spl7_7
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f166,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f49,f86])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f126,plain,
    ( ~ spl7_13
    | spl7_14
    | ~ spl7_2
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f119,f107,f69,f124,f121])).

fof(f121,plain,
    ( spl7_13
  <=> r2_hidden(sK5,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f69,plain,
    ( spl7_2
  <=> sK4 = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f107,plain,
    ( spl7_11
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f119,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ spl7_2
    | ~ spl7_11 ),
    inference(superposition,[],[f108,f70])).

fof(f70,plain,
    ( sK4 = k1_funct_1(sK3,sK5)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f108,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
        | ~ r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f118,plain,(
    spl7_12 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl7_12 ),
    inference(resolution,[],[f114,f43])).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f114,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,
    ( ~ spl7_12
    | ~ spl7_6
    | spl7_10 ),
    inference(avatar_split_clause,[],[f111,f104,f85,f113])).

fof(f104,plain,
    ( spl7_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f111,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl7_6
    | spl7_10 ),
    inference(resolution,[],[f110,f86])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl7_10 ),
    inference(resolution,[],[f105,f38])).

fof(f105,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f109,plain,
    ( ~ spl7_10
    | spl7_11
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f102,f93,f107,f104])).

fof(f93,plain,
    ( spl7_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl7_8 ),
    inference(resolution,[],[f58,f94])).

fof(f94,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f101,plain,
    ( ~ spl7_9
    | spl7_1
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f97,f85,f65,f99])).

fof(f65,plain,
    ( spl7_1
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f97,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | spl7_1
    | ~ spl7_6 ),
    inference(superposition,[],[f66,f96])).

fof(f96,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl7_6 ),
    inference(resolution,[],[f55,f86])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f66,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f95,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f30,f93])).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & sK4 = k1_funct_1(sK3,sK5)
    & r2_hidden(sK5,sK2)
    & r2_hidden(sK5,sK0)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
            & ? [X5] :
                ( k1_funct_1(X3,X5) = X4
                & r2_hidden(X5,X2)
                & r2_hidden(X5,X0) ) )
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))
          & ? [X5] :
              ( k1_funct_1(sK3,X5) = X4
              & r2_hidden(X5,sK2)
              & r2_hidden(X5,sK0) ) )
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X4] :
        ( ~ r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))
        & ? [X5] :
            ( k1_funct_1(sK3,X5) = X4
            & r2_hidden(X5,sK2)
            & r2_hidden(X5,sK0) ) )
   => ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
      & ? [X5] :
          ( k1_funct_1(sK3,X5) = sK4
          & r2_hidden(X5,sK2)
          & r2_hidden(X5,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X5] :
        ( k1_funct_1(sK3,X5) = sK4
        & r2_hidden(X5,sK2)
        & r2_hidden(X5,sK0) )
   => ( sK4 = k1_funct_1(sK3,sK5)
      & r2_hidden(sK5,sK2)
      & r2_hidden(sK5,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => ! [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
             => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( ? [X5] :
                ( k1_funct_1(X3,X5) = X4
                & r2_hidden(X5,X2)
                & r2_hidden(X5,X0) )
           => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_2)).

fof(f91,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f31,f89])).

fof(f31,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f87,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f32,f85])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f33,f81])).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f34,f77])).

fof(f34,plain,(
    r2_hidden(sK5,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f35,f73])).

fof(f35,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f36,f69])).

fof(f36,plain,(
    sK4 = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f37,f65])).

fof(f37,plain,(
    ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (11306)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  % (11305)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (11306)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (11314)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (11304)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f215,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f67,f71,f75,f79,f83,f87,f91,f95,f101,f109,f115,f118,f126,f172,f180,f181,f204,f214])).
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    ~spl7_3 | ~spl7_4 | spl7_9 | ~spl7_14 | ~spl7_25),
% 0.20/0.47    inference(avatar_split_clause,[],[f208,f202,f124,f99,f77,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    spl7_3 <=> r2_hidden(sK5,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    spl7_4 <=> r2_hidden(sK5,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    spl7_9 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    spl7_14 <=> r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.20/0.47  fof(f202,plain,(
% 0.20/0.47    spl7_25 <=> ! [X1,X0,X2] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,X2) | r2_hidden(X1,k9_relat_1(sK3,X2)) | ~r2_hidden(k4_tarski(X0,X1),sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.20/0.47  fof(f208,plain,(
% 0.20/0.47    ~r2_hidden(sK5,sK0) | ~r2_hidden(sK5,sK2) | (spl7_9 | ~spl7_14 | ~spl7_25)),
% 0.20/0.47    inference(resolution,[],[f206,f125])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~spl7_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f124])).
% 0.20/0.47  fof(f206,plain,(
% 0.20/0.47    ( ! [X1] : (~r2_hidden(k4_tarski(X1,sK4),sK3) | ~r2_hidden(X1,sK0) | ~r2_hidden(X1,sK2)) ) | (spl7_9 | ~spl7_25)),
% 0.20/0.47    inference(resolution,[],[f203,f100])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | spl7_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f99])).
% 0.20/0.47  fof(f203,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(X1,k9_relat_1(sK3,X2)) | ~r2_hidden(X0,X2) | ~r2_hidden(X0,sK0) | ~r2_hidden(k4_tarski(X0,X1),sK3)) ) | ~spl7_25),
% 0.20/0.47    inference(avatar_component_clause,[],[f202])).
% 0.20/0.47  fof(f204,plain,(
% 0.20/0.47    ~spl7_12 | spl7_25 | ~spl7_6 | ~spl7_21),
% 0.20/0.47    inference(avatar_split_clause,[],[f200,f177,f85,f202,f113])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    spl7_12 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    spl7_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    spl7_21 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.20/0.47  fof(f200,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(k4_tarski(X0,X1),sK3) | r2_hidden(X1,k9_relat_1(sK3,X2)) | ~r2_hidden(X0,X2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))) ) | (~spl7_6 | ~spl7_21)),
% 0.20/0.47    inference(forward_demodulation,[],[f199,f178])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK3) | ~spl7_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f177])).
% 0.20/0.47  fof(f199,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | ~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(X1,k9_relat_1(sK3,X2)) | ~r2_hidden(X0,X2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))) ) | ~spl7_6),
% 0.20/0.47    inference(resolution,[],[f163,f86])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f85])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    ( ! [X6,X8,X7,X5,X9] : (~m1_subset_1(X8,k1_zfmisc_1(X9)) | ~r2_hidden(k4_tarski(X5,X7),X8) | ~r2_hidden(X5,k1_relat_1(X8)) | r2_hidden(X7,k9_relat_1(X8,X6)) | ~r2_hidden(X5,X6) | ~v1_relat_1(X9)) )),
% 0.20/0.47    inference(resolution,[],[f47,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(rectify,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(nnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.20/0.47  fof(f181,plain,(
% 0.20/0.47    sK0 != k1_relat_1(sK3) | r2_hidden(sK5,k1_relat_1(sK3)) | ~r2_hidden(sK5,sK0)),
% 0.20/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    ~spl7_6 | spl7_21 | ~spl7_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f174,f168,f177,f85])).
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    spl7_20 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_20),
% 0.20/0.47    inference(superposition,[],[f48,f169])).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f168])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    spl7_20 | spl7_5 | ~spl7_7 | ~spl7_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f166,f85,f89,f81,f168])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    spl7_5 <=> k1_xboole_0 = sK1),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    spl7_7 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_6),
% 0.20/0.47    inference(resolution,[],[f49,f86])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(nnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(flattening,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    ~spl7_13 | spl7_14 | ~spl7_2 | ~spl7_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f119,f107,f69,f124,f121])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    spl7_13 <=> r2_hidden(sK5,k1_relat_1(sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl7_2 <=> sK4 = k1_funct_1(sK3,sK5)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    spl7_11 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~r2_hidden(sK5,k1_relat_1(sK3)) | (~spl7_2 | ~spl7_11)),
% 0.20/0.47    inference(superposition,[],[f108,f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    sK4 = k1_funct_1(sK3,sK5) | ~spl7_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f69])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~r2_hidden(X0,k1_relat_1(sK3))) ) | ~spl7_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f107])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    spl7_12),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f116])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    $false | spl7_12),
% 0.20/0.47    inference(resolution,[],[f114,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl7_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f113])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    ~spl7_12 | ~spl7_6 | spl7_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f111,f104,f85,f113])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    spl7_10 <=> v1_relat_1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl7_6 | spl7_10)),
% 0.20/0.47    inference(resolution,[],[f110,f86])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl7_10),
% 0.20/0.47    inference(resolution,[],[f105,f38])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    ~v1_relat_1(sK3) | spl7_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f104])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    ~spl7_10 | spl7_11 | ~spl7_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f102,f93,f107,f104])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    spl7_8 <=> v1_funct_1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~v1_relat_1(sK3)) ) | ~spl7_8),
% 0.20/0.47    inference(resolution,[],[f58,f94])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    v1_funct_1(sK3) | ~spl7_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f93])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    ~spl7_9 | spl7_1 | ~spl7_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f97,f85,f65,f99])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    spl7_1 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (spl7_1 | ~spl7_6)),
% 0.20/0.47    inference(superposition,[],[f66,f96])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl7_6),
% 0.20/0.47    inference(resolution,[],[f55,f86])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | spl7_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f65])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    spl7_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f93])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    v1_funct_1(sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    (~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) & (sK4 = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK5,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f22,f21,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (~r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) & ? [X5] : (k1_funct_1(sK3,X5) = X4 & r2_hidden(X5,sK2) & r2_hidden(X5,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ? [X4] : (~r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) & ? [X5] : (k1_funct_1(sK3,X5) = X4 & r2_hidden(X5,sK2) & r2_hidden(X5,sK0))) => (~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) & ? [X5] : (k1_funct_1(sK3,X5) = sK4 & r2_hidden(X5,sK2) & r2_hidden(X5,sK0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ? [X5] : (k1_funct_1(sK3,X5) = sK4 & r2_hidden(X5,sK2) & r2_hidden(X5,sK0)) => (sK4 = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK5,sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : ((? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f8])).
% 0.20/0.47  fof(f8,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_2)).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    spl7_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f31,f89])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    spl7_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f32,f85])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    ~spl7_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f33,f81])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    k1_xboole_0 != sK1),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    spl7_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f34,f77])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    r2_hidden(sK5,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    spl7_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f35,f73])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    r2_hidden(sK5,sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl7_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f36,f69])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    sK4 = k1_funct_1(sK3,sK5)),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ~spl7_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f37,f65])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (11306)------------------------------
% 0.20/0.47  % (11306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (11306)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (11306)Memory used [KB]: 10746
% 0.20/0.47  % (11306)Time elapsed: 0.057 s
% 0.20/0.47  % (11306)------------------------------
% 0.20/0.47  % (11306)------------------------------
% 0.20/0.47  % (11300)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (11315)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (11297)Success in time 0.118 s
%------------------------------------------------------------------------------
