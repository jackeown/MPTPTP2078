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
% DateTime   : Thu Dec  3 12:59:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 274 expanded)
%              Number of leaves         :   31 ( 108 expanded)
%              Depth                    :   12
%              Number of atoms          :  555 (1259 expanded)
%              Number of equality atoms :  240 ( 568 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f502,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f73,f77,f81,f85,f98,f123,f132,f149,f158,f173,f182,f274,f280,f293,f320,f413,f501])).

fof(f501,plain,
    ( spl7_3
    | spl7_4
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f483,f397,f79,f75])).

fof(f75,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f79,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f397,plain,
    ( spl7_36
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f483,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl7_36 ),
    inference(trivial_inequality_removal,[],[f482])).

fof(f482,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl7_36 ),
    inference(superposition,[],[f45,f398])).

fof(f398,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f397])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f413,plain,
    ( spl7_2
    | spl7_36
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f380,f291,f397,f71])).

fof(f71,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f291,plain,
    ( spl7_29
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f380,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl7_29 ),
    inference(trivial_inequality_removal,[],[f379])).

fof(f379,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl7_29 ),
    inference(superposition,[],[f45,f292])).

fof(f292,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f291])).

fof(f320,plain,
    ( spl7_28
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f315,f164,f83,f264])).

fof(f264,plain,
    ( spl7_28
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f83,plain,
    ( spl7_5
  <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f164,plain,
    ( spl7_13
  <=> ! [X4] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f315,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(resolution,[],[f308,f84])).

fof(f84,plain,
    ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f308,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) )
    | ~ spl7_13 ),
    inference(resolution,[],[f305,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

% (1510)Termination reason: Refutation not found, incomplete strategy

% (1510)Memory used [KB]: 1791
% (1510)Time elapsed: 0.156 s
% (1510)------------------------------
% (1510)------------------------------
fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f305,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
    | ~ spl7_13 ),
    inference(resolution,[],[f165,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f165,plain,
    ( ! [X4] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X4))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f164])).

fof(f293,plain,
    ( spl7_29
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f286,f264,f291])).

fof(f286,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl7_28 ),
    inference(resolution,[],[f284,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f284,plain,
    ( ! [X2] : ~ r2_hidden(X2,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_28 ),
    inference(resolution,[],[f265,f38])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
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

fof(f265,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f264])).

fof(f280,plain,
    ( spl7_28
    | ~ spl7_5
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f275,f171,f83,f264])).

fof(f171,plain,
    ( spl7_15
  <=> ! [X0] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f275,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_5
    | ~ spl7_15 ),
    inference(resolution,[],[f255,f84])).

fof(f255,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) )
    | ~ spl7_15 ),
    inference(resolution,[],[f240,f41])).

fof(f240,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
    | ~ spl7_15 ),
    inference(resolution,[],[f172,f50])).

fof(f172,plain,
    ( ! [X0] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f171])).

fof(f274,plain,
    ( spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f270,f180,f83,f79,f75])).

fof(f180,plain,
    ( spl7_16
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X0),sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f270,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl7_5
    | ~ spl7_16 ),
    inference(resolution,[],[f181,f84])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X0),sK2))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( spl7_2
    | spl7_16
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f178,f168,f180,f71])).

fof(f168,plain,
    ( spl7_14
  <=> ! [X1,X3,X2] :
        ( ~ m1_subset_1(k7_mcart_1(X1,X2,X3,sK4),sK2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X3
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X0),sK2))
        | k1_xboole_0 = X1 )
    | ~ spl7_14 ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X0),sK2))
        | k1_xboole_0 = X1
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X0),sK2)) )
    | ~ spl7_14 ),
    inference(resolution,[],[f169,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f56,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f169,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(k7_mcart_1(X1,X2,X3,sK4),sK2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X3
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
        | k1_xboole_0 = X1 )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f168])).

fof(f173,plain,
    ( spl7_13
    | spl7_6
    | spl7_14
    | spl7_15
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f162,f147,f171,f168,f96,f164])).

fof(f96,plain,
    ( spl7_6
  <=> sK3 = k2_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f147,plain,
    ( spl7_12
  <=> ! [X1,X3,X0,X2,X4] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(k1_mcart_1(k1_mcart_1(X3)),sK0)
        | ~ r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1))
        | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2)
        | sK4 != X3
        | k2_mcart_1(k1_mcart_1(X3)) = sK3
        | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f162,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))
        | ~ m1_subset_1(k7_mcart_1(X1,X2,X3,sK4),sK2)
        | k1_xboole_0 = X1
        | sK3 = k2_mcart_1(k1_mcart_1(sK4))
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X4)) )
    | ~ spl7_12 ),
    inference(equality_resolution,[],[f160])).

fof(f160,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( sK4 != X1
        | ~ r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(X2,sK1))
        | ~ m1_subset_1(k7_mcart_1(X0,X3,X4,X1),sK2)
        | k1_xboole_0 = X0
        | sK3 = k2_mcart_1(k1_mcart_1(X1))
        | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X0,X3),X4))
        | k1_xboole_0 = X4
        | k1_xboole_0 = X3
        | ~ r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(sK0,X5)) )
    | ~ spl7_12 ),
    inference(resolution,[],[f148,f50])).

fof(f148,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(X3)),sK0)
        | k1_xboole_0 = X0
        | ~ r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1))
        | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2)
        | sK4 != X3
        | k2_mcart_1(k1_mcart_1(X3)) = sK3
        | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1 )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f158,plain,
    ( spl7_4
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f154,f139,f79])).

fof(f139,plain,
    ( spl7_10
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f154,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_10 ),
    inference(resolution,[],[f152,f40])).

fof(f152,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK0)
    | ~ spl7_10 ),
    inference(resolution,[],[f140,f38])).

fof(f140,plain,
    ( v1_xboole_0(sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f139])).

fof(f149,plain,
    ( spl7_10
    | spl7_12
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f145,f121,f147,f139])).

fof(f121,plain,
    ( spl7_9
  <=> ! [X9,X7,X8,X6] :
        ( sK3 = k2_mcart_1(k1_mcart_1(X6))
        | ~ r2_hidden(k2_mcart_1(k1_mcart_1(X6)),sK1)
        | k1_xboole_0 = X7
        | k1_xboole_0 = X8
        | k1_xboole_0 = X9
        | ~ m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(X7,X8),X9))
        | ~ m1_subset_1(k5_mcart_1(X7,X8,X9,X6),sK0)
        | sK4 != X6
        | ~ m1_subset_1(k7_mcart_1(X7,X8,X9,X6),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f145,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k1_xboole_0 = X2
        | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k2_mcart_1(k1_mcart_1(X3)) = sK3
        | sK4 != X3
        | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2)
        | ~ r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1))
        | ~ r2_hidden(k1_mcart_1(k1_mcart_1(X3)),sK0)
        | v1_xboole_0(sK0) )
    | ~ spl7_9 ),
    inference(resolution,[],[f137,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f137,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),sK0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k1_xboole_0 = X2
        | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k2_mcart_1(k1_mcart_1(X3)) = sK3
        | sK4 != X3
        | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2)
        | ~ r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1)) )
    | ~ spl7_9 ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),sK0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k1_xboole_0 = X2
        | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k2_mcart_1(k1_mcart_1(X3)) = sK3
        | sK4 != X3
        | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2)
        | ~ r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1))
        | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl7_9 ),
    inference(superposition,[],[f133,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f53,f49])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f133,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(k5_mcart_1(X1,X2,X3,X0),sK0)
        | k1_xboole_0 = X1
        | k1_xboole_0 = X2
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
        | sK3 = k2_mcart_1(k1_mcart_1(X0))
        | sK4 != X0
        | ~ m1_subset_1(k7_mcart_1(X1,X2,X3,X0),sK2)
        | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,sK1)) )
    | ~ spl7_9 ),
    inference(resolution,[],[f122,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f122,plain,
    ( ! [X6,X8,X7,X9] :
        ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(X6)),sK1)
        | sK3 = k2_mcart_1(k1_mcart_1(X6))
        | k1_xboole_0 = X7
        | k1_xboole_0 = X8
        | k1_xboole_0 = X9
        | ~ m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(X7,X8),X9))
        | ~ m1_subset_1(k5_mcart_1(X7,X8,X9,X6),sK0)
        | sK4 != X6
        | ~ m1_subset_1(k7_mcart_1(X7,X8,X9,X6),sK2) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f132,plain,
    ( spl7_3
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f128,f111,f75])).

fof(f111,plain,
    ( spl7_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f128,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_7 ),
    inference(resolution,[],[f126,f40])).

fof(f126,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK1)
    | ~ spl7_7 ),
    inference(resolution,[],[f112,f38])).

fof(f112,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f123,plain,
    ( spl7_7
    | spl7_9 ),
    inference(avatar_split_clause,[],[f118,f121,f111])).

fof(f118,plain,(
    ! [X6,X8,X7,X9] :
      ( sK3 = k2_mcart_1(k1_mcart_1(X6))
      | ~ m1_subset_1(k7_mcart_1(X7,X8,X9,X6),sK2)
      | sK4 != X6
      | ~ m1_subset_1(k5_mcart_1(X7,X8,X9,X6),sK0)
      | ~ m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(X7,X8),X9))
      | k1_xboole_0 = X9
      | k1_xboole_0 = X8
      | k1_xboole_0 = X7
      | ~ r2_hidden(k2_mcart_1(k1_mcart_1(X6)),sK1)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f109,f42])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),sK1)
      | k2_mcart_1(k1_mcart_1(X3)) = sK3
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2)
      | sK4 != X3
      | ~ m1_subset_1(k5_mcart_1(X0,X1,X2,X3),sK0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),sK1)
      | k2_mcart_1(k1_mcart_1(X3)) = sK3
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2)
      | sK4 != X3
      | ~ m1_subset_1(k5_mcart_1(X0,X1,X2,X3),sK0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f102,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f54,f49])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k6_mcart_1(X0,X1,X2,X3),sK1)
      | k6_mcart_1(X0,X1,X2,X3) = sK3
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2)
      | sK4 != X3
      | ~ m1_subset_1(k5_mcart_1(X0,X1,X2,X3),sK0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f57,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f48,f49])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f57,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X6
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f33,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X6
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X6
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k6_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X6
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X6
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X6 ) ) ) )
         => ( k6_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X6 ) ) ) )
       => ( k6_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

fof(f98,plain,
    ( spl7_4
    | spl7_3
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | spl7_1 ),
    inference(avatar_split_clause,[],[f90,f67,f96,f83,f71,f75,f79])).

fof(f67,plain,
    ( spl7_1
  <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f90,plain,
    ( sK3 != k2_mcart_1(k1_mcart_1(sK4))
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl7_1 ),
    inference(superposition,[],[f68,f61])).

fof(f68,plain,
    ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f85,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f58,f83])).

fof(f58,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f32,f49])).

fof(f32,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f81,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f34,f79])).

fof(f34,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f35,f75])).

fof(f35,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f36,f71])).

fof(f36,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f37,f67])).

fof(f37,plain,(
    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:29:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (1497)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (1499)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (1499)Refutation not found, incomplete strategy% (1499)------------------------------
% 0.21/0.52  % (1499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1499)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1499)Memory used [KB]: 10618
% 0.21/0.52  % (1499)Time elapsed: 0.104 s
% 0.21/0.52  % (1499)------------------------------
% 0.21/0.52  % (1499)------------------------------
% 0.21/0.52  % (1489)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (1488)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (1492)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (1513)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (1510)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (1491)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (1494)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (1496)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (1488)Refutation not found, incomplete strategy% (1488)------------------------------
% 0.21/0.53  % (1488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1488)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1488)Memory used [KB]: 1663
% 0.21/0.53  % (1488)Time elapsed: 0.118 s
% 0.21/0.53  % (1488)------------------------------
% 0.21/0.53  % (1488)------------------------------
% 0.21/0.53  % (1508)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (1504)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (1501)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (1502)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (1500)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (1495)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (1490)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (1500)Refutation not found, incomplete strategy% (1500)------------------------------
% 0.21/0.54  % (1500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1500)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1500)Memory used [KB]: 10618
% 0.21/0.54  % (1500)Time elapsed: 0.132 s
% 0.21/0.54  % (1500)------------------------------
% 0.21/0.54  % (1500)------------------------------
% 0.21/0.54  % (1517)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (1518)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (1490)Refutation not found, incomplete strategy% (1490)------------------------------
% 0.21/0.54  % (1490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1490)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1490)Memory used [KB]: 10746
% 0.21/0.54  % (1490)Time elapsed: 0.126 s
% 0.21/0.54  % (1490)------------------------------
% 0.21/0.54  % (1490)------------------------------
% 0.21/0.55  % (1505)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (1498)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (1509)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (1511)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (1498)Refutation not found, incomplete strategy% (1498)------------------------------
% 0.21/0.55  % (1498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1498)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1498)Memory used [KB]: 10618
% 0.21/0.55  % (1498)Time elapsed: 0.135 s
% 0.21/0.55  % (1498)------------------------------
% 0.21/0.55  % (1498)------------------------------
% 0.21/0.55  % (1516)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (1512)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (1507)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (1503)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (1506)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (1515)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (1510)Refutation not found, incomplete strategy% (1510)------------------------------
% 0.21/0.56  % (1510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (1514)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (1506)Refutation not found, incomplete strategy% (1506)------------------------------
% 0.21/0.57  % (1506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (1506)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (1506)Memory used [KB]: 10618
% 0.21/0.57  % (1506)Time elapsed: 0.159 s
% 0.21/0.57  % (1506)------------------------------
% 0.21/0.57  % (1506)------------------------------
% 0.21/0.58  % (1508)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f502,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f69,f73,f77,f81,f85,f98,f123,f132,f149,f158,f173,f182,f274,f280,f293,f320,f413,f501])).
% 0.21/0.58  fof(f501,plain,(
% 0.21/0.58    spl7_3 | spl7_4 | ~spl7_36),
% 0.21/0.58    inference(avatar_split_clause,[],[f483,f397,f79,f75])).
% 0.21/0.58  fof(f75,plain,(
% 0.21/0.58    spl7_3 <=> k1_xboole_0 = sK1),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.58  fof(f79,plain,(
% 0.21/0.58    spl7_4 <=> k1_xboole_0 = sK0),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.58  fof(f397,plain,(
% 0.21/0.58    spl7_36 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.21/0.58  fof(f483,plain,(
% 0.21/0.58    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl7_36),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f482])).
% 0.21/0.58  fof(f482,plain,(
% 0.21/0.58    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl7_36),
% 0.21/0.58    inference(superposition,[],[f45,f398])).
% 0.21/0.58  fof(f398,plain,(
% 0.21/0.58    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl7_36),
% 0.21/0.58    inference(avatar_component_clause,[],[f397])).
% 0.21/0.58  fof(f45,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.58    inference(flattening,[],[f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.58    inference(nnf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.58  fof(f413,plain,(
% 0.21/0.58    spl7_2 | spl7_36 | ~spl7_29),
% 0.21/0.58    inference(avatar_split_clause,[],[f380,f291,f397,f71])).
% 0.21/0.58  fof(f71,plain,(
% 0.21/0.58    spl7_2 <=> k1_xboole_0 = sK2),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.58  fof(f291,plain,(
% 0.21/0.58    spl7_29 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.21/0.58  fof(f380,plain,(
% 0.21/0.58    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl7_29),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f379])).
% 0.21/0.58  fof(f379,plain,(
% 0.21/0.58    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl7_29),
% 0.21/0.58    inference(superposition,[],[f45,f292])).
% 0.21/0.58  fof(f292,plain,(
% 0.21/0.58    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl7_29),
% 0.21/0.58    inference(avatar_component_clause,[],[f291])).
% 0.21/0.58  fof(f320,plain,(
% 0.21/0.58    spl7_28 | ~spl7_5 | ~spl7_13),
% 0.21/0.58    inference(avatar_split_clause,[],[f315,f164,f83,f264])).
% 0.21/0.58  fof(f264,plain,(
% 0.21/0.58    spl7_28 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.58  fof(f83,plain,(
% 0.21/0.58    spl7_5 <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.58  fof(f164,plain,(
% 0.21/0.58    spl7_13 <=> ! [X4] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X4))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.58  fof(f315,plain,(
% 0.21/0.58    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | (~spl7_5 | ~spl7_13)),
% 0.21/0.58    inference(resolution,[],[f308,f84])).
% 0.21/0.58  fof(f84,plain,(
% 0.21/0.58    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_5),
% 0.21/0.58    inference(avatar_component_clause,[],[f83])).
% 0.21/0.58  fof(f308,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))) ) | ~spl7_13),
% 0.21/0.58    inference(resolution,[],[f305,f41])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.58    inference(nnf_transformation,[],[f16])).
% 0.21/0.58  % (1510)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (1510)Memory used [KB]: 1791
% 0.21/0.58  % (1510)Time elapsed: 0.156 s
% 0.21/0.58  % (1510)------------------------------
% 0.21/0.58  % (1510)------------------------------
% 0.21/0.58  fof(f16,plain,(
% 0.21/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.58  fof(f305,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))) ) | ~spl7_13),
% 0.21/0.58    inference(resolution,[],[f165,f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.58    inference(ennf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.58  fof(f165,plain,(
% 0.21/0.58    ( ! [X4] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X4))) ) | ~spl7_13),
% 0.21/0.58    inference(avatar_component_clause,[],[f164])).
% 0.21/0.58  fof(f293,plain,(
% 0.21/0.58    spl7_29 | ~spl7_28),
% 0.21/0.58    inference(avatar_split_clause,[],[f286,f264,f291])).
% 0.21/0.58  fof(f286,plain,(
% 0.21/0.58    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl7_28),
% 0.21/0.58    inference(resolution,[],[f284,f40])).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f15,plain,(
% 0.21/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.58    inference(ennf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.58  fof(f284,plain,(
% 0.21/0.58    ( ! [X2] : (~r2_hidden(X2,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) ) | ~spl7_28),
% 0.21/0.58    inference(resolution,[],[f265,f38])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.58    inference(rectify,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.58    inference(nnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.58  fof(f265,plain,(
% 0.21/0.58    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_28),
% 0.21/0.58    inference(avatar_component_clause,[],[f264])).
% 0.21/0.58  fof(f280,plain,(
% 0.21/0.58    spl7_28 | ~spl7_5 | ~spl7_15),
% 0.21/0.58    inference(avatar_split_clause,[],[f275,f171,f83,f264])).
% 0.21/0.58  fof(f171,plain,(
% 0.21/0.58    spl7_15 <=> ! [X0] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.58  fof(f275,plain,(
% 0.21/0.58    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | (~spl7_5 | ~spl7_15)),
% 0.21/0.58    inference(resolution,[],[f255,f84])).
% 0.21/0.58  fof(f255,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | ~spl7_15),
% 0.21/0.58    inference(resolution,[],[f240,f41])).
% 0.21/0.58  fof(f240,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | ~spl7_15),
% 0.21/0.58    inference(resolution,[],[f172,f50])).
% 0.21/0.58  fof(f172,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))) ) | ~spl7_15),
% 0.21/0.58    inference(avatar_component_clause,[],[f171])).
% 0.21/0.58  fof(f274,plain,(
% 0.21/0.58    spl7_3 | spl7_4 | ~spl7_5 | ~spl7_16),
% 0.21/0.58    inference(avatar_split_clause,[],[f270,f180,f83,f79,f75])).
% 0.21/0.58  fof(f180,plain,(
% 0.21/0.58    spl7_16 <=> ! [X1,X0] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X0),sK2)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.58  fof(f270,plain,(
% 0.21/0.58    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | (~spl7_5 | ~spl7_16)),
% 0.21/0.58    inference(resolution,[],[f181,f84])).
% 0.21/0.58  fof(f181,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X0),sK2)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl7_16),
% 0.21/0.58    inference(avatar_component_clause,[],[f180])).
% 0.21/0.58  fof(f182,plain,(
% 0.21/0.58    spl7_2 | spl7_16 | ~spl7_14),
% 0.21/0.58    inference(avatar_split_clause,[],[f178,f168,f180,f71])).
% 0.21/0.58  fof(f168,plain,(
% 0.21/0.58    spl7_14 <=> ! [X1,X3,X2] : (~m1_subset_1(k7_mcart_1(X1,X2,X3,sK4),sK2) | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) | k1_xboole_0 = X1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.58  fof(f178,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X0),sK2)) | k1_xboole_0 = X1) ) | ~spl7_14),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f174])).
% 0.21/0.58  fof(f174,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X0),sK2)) | k1_xboole_0 = X1 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X0),sK2))) ) | ~spl7_14),
% 0.21/0.58    inference(resolution,[],[f169,f63])).
% 0.21/0.58  fof(f63,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f56,f49])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.58    inference(ennf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).
% 0.21/0.58  fof(f169,plain,(
% 0.21/0.58    ( ! [X2,X3,X1] : (~m1_subset_1(k7_mcart_1(X1,X2,X3,sK4),sK2) | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) | k1_xboole_0 = X1) ) | ~spl7_14),
% 0.21/0.58    inference(avatar_component_clause,[],[f168])).
% 0.21/0.58  fof(f173,plain,(
% 0.21/0.58    spl7_13 | spl7_6 | spl7_14 | spl7_15 | ~spl7_12),
% 0.21/0.58    inference(avatar_split_clause,[],[f162,f147,f171,f168,f96,f164])).
% 0.21/0.58  fof(f96,plain,(
% 0.21/0.58    spl7_6 <=> sK3 = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.58  fof(f147,plain,(
% 0.21/0.58    spl7_12 <=> ! [X1,X3,X0,X2,X4] : (k1_xboole_0 = X0 | ~r2_hidden(k1_mcart_1(k1_mcart_1(X3)),sK0) | ~r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1)) | ~m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2) | sK4 != X3 | k2_mcart_1(k1_mcart_1(X3)) = sK3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.58  fof(f162,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1)) | ~m1_subset_1(k7_mcart_1(X1,X2,X3,sK4),sK2) | k1_xboole_0 = X1 | sK3 = k2_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X4))) ) | ~spl7_12),
% 0.21/0.58    inference(equality_resolution,[],[f160])).
% 0.21/0.58  fof(f160,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (sK4 != X1 | ~r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(X2,sK1)) | ~m1_subset_1(k7_mcart_1(X0,X3,X4,X1),sK2) | k1_xboole_0 = X0 | sK3 = k2_mcart_1(k1_mcart_1(X1)) | ~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X0,X3),X4)) | k1_xboole_0 = X4 | k1_xboole_0 = X3 | ~r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(sK0,X5))) ) | ~spl7_12),
% 0.21/0.58    inference(resolution,[],[f148,f50])).
% 0.21/0.58  fof(f148,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k1_mcart_1(k1_mcart_1(X3)),sK0) | k1_xboole_0 = X0 | ~r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1)) | ~m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2) | sK4 != X3 | k2_mcart_1(k1_mcart_1(X3)) = sK3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1) ) | ~spl7_12),
% 0.21/0.58    inference(avatar_component_clause,[],[f147])).
% 0.21/0.58  fof(f158,plain,(
% 0.21/0.58    spl7_4 | ~spl7_10),
% 0.21/0.58    inference(avatar_split_clause,[],[f154,f139,f79])).
% 0.21/0.58  fof(f139,plain,(
% 0.21/0.58    spl7_10 <=> v1_xboole_0(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.58  fof(f154,plain,(
% 0.21/0.58    k1_xboole_0 = sK0 | ~spl7_10),
% 0.21/0.58    inference(resolution,[],[f152,f40])).
% 0.21/0.58  fof(f152,plain,(
% 0.21/0.58    ( ! [X2] : (~r2_hidden(X2,sK0)) ) | ~spl7_10),
% 0.21/0.58    inference(resolution,[],[f140,f38])).
% 0.21/0.58  fof(f140,plain,(
% 0.21/0.58    v1_xboole_0(sK0) | ~spl7_10),
% 0.21/0.58    inference(avatar_component_clause,[],[f139])).
% 0.21/0.58  fof(f149,plain,(
% 0.21/0.58    spl7_10 | spl7_12 | ~spl7_9),
% 0.21/0.58    inference(avatar_split_clause,[],[f145,f121,f147,f139])).
% 0.21/0.58  fof(f121,plain,(
% 0.21/0.58    spl7_9 <=> ! [X9,X7,X8,X6] : (sK3 = k2_mcart_1(k1_mcart_1(X6)) | ~r2_hidden(k2_mcart_1(k1_mcart_1(X6)),sK1) | k1_xboole_0 = X7 | k1_xboole_0 = X8 | k1_xboole_0 = X9 | ~m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(X7,X8),X9)) | ~m1_subset_1(k5_mcart_1(X7,X8,X9,X6),sK0) | sK4 != X6 | ~m1_subset_1(k7_mcart_1(X7,X8,X9,X6),sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.58  fof(f145,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k2_mcart_1(k1_mcart_1(X3)) = sK3 | sK4 != X3 | ~m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2) | ~r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1)) | ~r2_hidden(k1_mcart_1(k1_mcart_1(X3)),sK0) | v1_xboole_0(sK0)) ) | ~spl7_9),
% 0.21/0.58    inference(resolution,[],[f137,f42])).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f29])).
% 0.21/0.58  fof(f137,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),sK0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k2_mcart_1(k1_mcart_1(X3)) = sK3 | sK4 != X3 | ~m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2) | ~r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1))) ) | ~spl7_9),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f136])).
% 0.21/0.58  fof(f136,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),sK0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k2_mcart_1(k1_mcart_1(X3)) = sK3 | sK4 != X3 | ~m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2) | ~r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl7_9),
% 0.21/0.58    inference(superposition,[],[f133,f62])).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f53,f49])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.58    inference(ennf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.58  fof(f133,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k5_mcart_1(X1,X2,X3,X0),sK0) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) | sK3 = k2_mcart_1(k1_mcart_1(X0)) | sK4 != X0 | ~m1_subset_1(k7_mcart_1(X1,X2,X3,X0),sK2) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,sK1))) ) | ~spl7_9),
% 0.21/0.58    inference(resolution,[],[f122,f51])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f122,plain,(
% 0.21/0.58    ( ! [X6,X8,X7,X9] : (~r2_hidden(k2_mcart_1(k1_mcart_1(X6)),sK1) | sK3 = k2_mcart_1(k1_mcart_1(X6)) | k1_xboole_0 = X7 | k1_xboole_0 = X8 | k1_xboole_0 = X9 | ~m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(X7,X8),X9)) | ~m1_subset_1(k5_mcart_1(X7,X8,X9,X6),sK0) | sK4 != X6 | ~m1_subset_1(k7_mcart_1(X7,X8,X9,X6),sK2)) ) | ~spl7_9),
% 0.21/0.58    inference(avatar_component_clause,[],[f121])).
% 0.21/0.58  fof(f132,plain,(
% 0.21/0.58    spl7_3 | ~spl7_7),
% 0.21/0.58    inference(avatar_split_clause,[],[f128,f111,f75])).
% 0.21/0.58  fof(f111,plain,(
% 0.21/0.58    spl7_7 <=> v1_xboole_0(sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.58  fof(f128,plain,(
% 0.21/0.58    k1_xboole_0 = sK1 | ~spl7_7),
% 0.21/0.58    inference(resolution,[],[f126,f40])).
% 0.21/0.58  fof(f126,plain,(
% 0.21/0.58    ( ! [X2] : (~r2_hidden(X2,sK1)) ) | ~spl7_7),
% 0.21/0.58    inference(resolution,[],[f112,f38])).
% 0.21/0.58  fof(f112,plain,(
% 0.21/0.58    v1_xboole_0(sK1) | ~spl7_7),
% 0.21/0.58    inference(avatar_component_clause,[],[f111])).
% 0.21/0.58  fof(f123,plain,(
% 0.21/0.58    spl7_7 | spl7_9),
% 0.21/0.58    inference(avatar_split_clause,[],[f118,f121,f111])).
% 0.21/0.58  fof(f118,plain,(
% 0.21/0.58    ( ! [X6,X8,X7,X9] : (sK3 = k2_mcart_1(k1_mcart_1(X6)) | ~m1_subset_1(k7_mcart_1(X7,X8,X9,X6),sK2) | sK4 != X6 | ~m1_subset_1(k5_mcart_1(X7,X8,X9,X6),sK0) | ~m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(X7,X8),X9)) | k1_xboole_0 = X9 | k1_xboole_0 = X8 | k1_xboole_0 = X7 | ~r2_hidden(k2_mcart_1(k1_mcart_1(X6)),sK1) | v1_xboole_0(sK1)) )),
% 0.21/0.58    inference(resolution,[],[f109,f42])).
% 0.21/0.58  fof(f109,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),sK1) | k2_mcart_1(k1_mcart_1(X3)) = sK3 | ~m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2) | sK4 != X3 | ~m1_subset_1(k5_mcart_1(X0,X1,X2,X3),sK0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f108])).
% 0.21/0.58  fof(f108,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),sK1) | k2_mcart_1(k1_mcart_1(X3)) = sK3 | ~m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2) | sK4 != X3 | ~m1_subset_1(k5_mcart_1(X0,X1,X2,X3),sK0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(superposition,[],[f102,f61])).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f54,f49])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f102,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k6_mcart_1(X0,X1,X2,X3),sK1) | k6_mcart_1(X0,X1,X2,X3) = sK3 | ~m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2) | sK4 != X3 | ~m1_subset_1(k5_mcart_1(X0,X1,X2,X3),sK0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(superposition,[],[f57,f59])).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f52,f48,f49])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f18])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.58    inference(ennf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X6 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f33,f48])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ( ! [X6,X7,X5] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f14,plain,(
% 0.21/0.58    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.58    inference(flattening,[],[f13])).
% 0.21/0.58  fof(f13,plain,(
% 0.21/0.58    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.58    inference(ennf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.58    inference(negated_conjecture,[],[f11])).
% 0.21/0.58  fof(f11,conjecture,(
% 0.21/0.58    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).
% 0.21/0.58  fof(f98,plain,(
% 0.21/0.58    spl7_4 | spl7_3 | spl7_2 | ~spl7_5 | ~spl7_6 | spl7_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f90,f67,f96,f83,f71,f75,f79])).
% 0.21/0.58  fof(f67,plain,(
% 0.21/0.58    spl7_1 <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.58  fof(f90,plain,(
% 0.21/0.58    sK3 != k2_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl7_1),
% 0.21/0.58    inference(superposition,[],[f68,f61])).
% 0.21/0.58  fof(f68,plain,(
% 0.21/0.58    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) | spl7_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f67])).
% 0.21/0.58  fof(f85,plain,(
% 0.21/0.58    spl7_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f58,f83])).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.58    inference(definition_unfolding,[],[f32,f49])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f81,plain,(
% 0.21/0.58    ~spl7_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f34,f79])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    k1_xboole_0 != sK0),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f77,plain,(
% 0.21/0.58    ~spl7_3),
% 0.21/0.58    inference(avatar_split_clause,[],[f35,f75])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    k1_xboole_0 != sK1),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f73,plain,(
% 0.21/0.58    ~spl7_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f36,f71])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    k1_xboole_0 != sK2),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f69,plain,(
% 0.21/0.58    ~spl7_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f37,f67])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (1508)------------------------------
% 0.21/0.58  % (1508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (1508)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (1508)Memory used [KB]: 11129
% 0.21/0.58  % (1508)Time elapsed: 0.170 s
% 0.21/0.58  % (1508)------------------------------
% 0.21/0.58  % (1508)------------------------------
% 1.52/0.59  % (1487)Success in time 0.216 s
%------------------------------------------------------------------------------
