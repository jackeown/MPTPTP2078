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
% DateTime   : Thu Dec  3 12:59:32 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 286 expanded)
%              Number of leaves         :   30 ( 118 expanded)
%              Depth                    :   10
%              Number of atoms          :  551 (1349 expanded)
%              Number of equality atoms :  225 ( 533 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f428,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f75,f79,f83,f87,f100,f108,f113,f123,f141,f158,f178,f201,f231,f239,f266,f294,f328,f332,f420,f427])).

fof(f427,plain,
    ( spl5_3
    | spl5_4
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f424,f264,f81,f77])).

fof(f77,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f81,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f264,plain,
    ( spl5_27
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f424,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl5_27 ),
    inference(trivial_inequality_removal,[],[f423])).

fof(f423,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl5_27 ),
    inference(superposition,[],[f44,f265])).

fof(f265,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f264])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f420,plain,
    ( spl5_2
    | spl5_27
    | ~ spl5_5
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f416,f176,f85,f264,f73])).

fof(f73,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f85,plain,
    ( spl5_5
  <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f176,plain,
    ( spl5_19
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(sK4,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f416,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl5_5
    | ~ spl5_19 ),
    inference(resolution,[],[f177,f86])).

fof(f86,plain,
    ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1 )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f176])).

fof(f332,plain,
    ( spl5_2
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f331,f153,f73])).

fof(f153,plain,
    ( spl5_13
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f331,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_13 ),
    inference(resolution,[],[f154,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f154,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f153])).

fof(f328,plain,
    ( spl5_2
    | spl5_27
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f325,f237,f264,f73])).

fof(f237,plain,
    ( spl5_26
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f325,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl5_26 ),
    inference(trivial_inequality_removal,[],[f324])).

fof(f324,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl5_26 ),
    inference(superposition,[],[f44,f238])).

fof(f238,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f237])).

fof(f294,plain,
    ( spl5_23
    | ~ spl5_5
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f289,f173,f85,f199])).

fof(f199,plain,
    ( spl5_23
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f173,plain,
    ( spl5_18
  <=> ! [X2] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f289,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_5
    | ~ spl5_18 ),
    inference(resolution,[],[f282,f86])).

fof(f282,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) )
    | ~ spl5_18 ),
    inference(resolution,[],[f267,f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f267,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
    | ~ spl5_18 ),
    inference(resolution,[],[f174,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f174,plain,
    ( ! [X2] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X2))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f173])).

fof(f266,plain,
    ( spl5_27
    | spl5_23
    | spl5_4
    | spl5_3
    | ~ spl5_5
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f257,f167,f85,f77,f81,f199,f264])).

fof(f167,plain,
    ( spl5_16
  <=> ! [X5,X4] :
        ( k1_xboole_0 = X4
        | ~ m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5))
        | k1_xboole_0 = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f257,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_5
    | ~ spl5_16 ),
    inference(resolution,[],[f254,f86])).

fof(f254,plain,
    ( ! [X10,X8,X9] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10))
        | k1_xboole_0 = X9
        | k1_xboole_0 = X8
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10))
        | k1_xboole_0 = k2_zfmisc_1(X8,X9) )
    | ~ spl5_16 ),
    inference(resolution,[],[f248,f38])).

fof(f248,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )
    | ~ spl5_16 ),
    inference(resolution,[],[f243,f39])).

fof(f243,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X0),X2))
        | k1_xboole_0 = X1
        | v1_xboole_0(k2_zfmisc_1(X1,X0))
        | k1_xboole_0 = X0 )
    | ~ spl5_16 ),
    inference(resolution,[],[f240,f50])).

fof(f240,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | v1_xboole_0(k2_zfmisc_1(X0,X1)) )
    | ~ spl5_16 ),
    inference(resolution,[],[f168,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f168,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5))
        | k1_xboole_0 = X4
        | k1_xboole_0 = X5 )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f167])).

fof(f239,plain,
    ( spl5_26
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f235,f199,f237])).

fof(f235,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl5_23 ),
    inference(resolution,[],[f200,f38])).

fof(f200,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f199])).

fof(f231,plain,
    ( spl5_23
    | ~ spl5_5
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f226,f170,f85,f199])).

fof(f170,plain,
    ( spl5_17
  <=> ! [X3] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f226,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_5
    | ~ spl5_17 ),
    inference(resolution,[],[f219,f86])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) )
    | ~ spl5_17 ),
    inference(resolution,[],[f202,f39])).

fof(f202,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
    | ~ spl5_17 ),
    inference(resolution,[],[f171,f50])).

fof(f171,plain,
    ( ! [X3] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X3,sK1))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f170])).

fof(f201,plain,
    ( spl5_23
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f194,f163,f85,f199])).

fof(f163,plain,
    ( spl5_15
  <=> ! [X6] : ~ r2_hidden(sK4,k2_zfmisc_1(X6,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f194,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(resolution,[],[f179,f86])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(X0,sK2))
        | v1_xboole_0(k2_zfmisc_1(X0,sK2)) )
    | ~ spl5_15 ),
    inference(resolution,[],[f164,f39])).

fof(f164,plain,
    ( ! [X6] : ~ r2_hidden(sK4,k2_zfmisc_1(X6,sK2))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f163])).

fof(f178,plain,
    ( spl5_15
    | spl5_10
    | spl5_16
    | spl5_17
    | spl5_18
    | spl5_19
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f161,f156,f176,f173,f170,f167,f121,f163])).

fof(f121,plain,
    ( spl5_10
  <=> sK3 = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f156,plain,
    ( spl5_14
  <=> ! [X1,X3,X5,X0,X2,X4,X6] :
        ( sK4 != X0
        | ~ r2_hidden(k2_mcart_1(X0),sK2)
        | k1_xboole_0 = X5
        | k1_xboole_0 = X6
        | ~ m1_subset_1(X0,k2_zfmisc_1(X5,X6))
        | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X4))
        | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X2
        | ~ m1_subset_1(k1_mcart_1(X0),k2_zfmisc_1(X1,X2))
        | k2_mcart_1(X0) = sK3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f161,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(sK4,k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X2))
        | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X3,sK1))
        | k1_xboole_0 = X4
        | k1_xboole_0 = X5
        | ~ m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5))
        | sK3 = k2_mcart_1(sK4)
        | ~ r2_hidden(sK4,k2_zfmisc_1(X6,sK2)) )
    | ~ spl5_14 ),
    inference(equality_resolution,[],[f159])).

fof(f159,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] :
        ( sK4 != X0
        | k1_xboole_0 = X1
        | k1_xboole_0 = X2
        | ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
        | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X3))
        | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,sK1))
        | k1_xboole_0 = X5
        | k1_xboole_0 = X6
        | ~ m1_subset_1(k1_mcart_1(X0),k2_zfmisc_1(X5,X6))
        | k2_mcart_1(X0) = sK3
        | ~ r2_hidden(X0,k2_zfmisc_1(X7,sK2)) )
    | ~ spl5_14 ),
    inference(resolution,[],[f157,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f157,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( ~ r2_hidden(k2_mcart_1(X0),sK2)
        | sK4 != X0
        | k1_xboole_0 = X5
        | k1_xboole_0 = X6
        | ~ m1_subset_1(X0,k2_zfmisc_1(X5,X6))
        | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X4))
        | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X2
        | ~ m1_subset_1(k1_mcart_1(X0),k2_zfmisc_1(X1,X2))
        | k2_mcart_1(X0) = sK3 )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f156])).

fof(f158,plain,
    ( spl5_13
    | spl5_14
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f151,f106,f156,f153])).

fof(f106,plain,
    ( spl5_9
  <=> ! [X1,X3,X0,X2] :
        ( ~ r2_hidden(k2_mcart_1(X0),sK1)
        | ~ r2_hidden(k1_mcart_1(X0),sK0)
        | ~ m1_subset_1(X3,sK2)
        | sK4 != k4_tarski(X0,X3)
        | sK3 = X3
        | ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f151,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( sK4 != X0
        | k2_mcart_1(X0) = sK3
        | ~ m1_subset_1(k1_mcart_1(X0),k2_zfmisc_1(X1,X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1))
        | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X4))
        | ~ m1_subset_1(X0,k2_zfmisc_1(X5,X6))
        | k1_xboole_0 = X6
        | k1_xboole_0 = X5
        | ~ r2_hidden(k2_mcart_1(X0),sK2)
        | v1_xboole_0(sK2) )
    | ~ spl5_9 ),
    inference(resolution,[],[f148,f40])).

fof(f148,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(k2_mcart_1(X0),sK2)
        | sK4 != X0
        | k2_mcart_1(X0) = sK3
        | ~ m1_subset_1(k1_mcart_1(X0),k2_zfmisc_1(X1,X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1))
        | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X4))
        | ~ m1_subset_1(X0,k2_zfmisc_1(X5,X6))
        | k1_xboole_0 = X6
        | k1_xboole_0 = X5 )
    | ~ spl5_9 ),
    inference(superposition,[],[f145,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f145,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( sK4 != k4_tarski(X1,X0)
        | ~ m1_subset_1(X0,sK2)
        | sK3 = X0
        | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3))
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | ~ r2_hidden(X1,k2_zfmisc_1(X4,sK1))
        | ~ r2_hidden(X1,k2_zfmisc_1(sK0,X5)) )
    | ~ spl5_9 ),
    inference(resolution,[],[f143,f50])).

fof(f143,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r2_hidden(k1_mcart_1(X0),sK0)
        | ~ m1_subset_1(X1,sK2)
        | k4_tarski(X0,X1) != sK4
        | sK3 = X1
        | ~ m1_subset_1(X0,k2_zfmisc_1(X2,X3))
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | ~ r2_hidden(X0,k2_zfmisc_1(X4,sK1)) )
    | ~ spl5_9 ),
    inference(resolution,[],[f107,f51])).

fof(f107,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k2_mcart_1(X0),sK1)
        | ~ r2_hidden(k1_mcart_1(X0),sK0)
        | ~ m1_subset_1(X3,sK2)
        | sK4 != k4_tarski(X0,X3)
        | sK3 = X3
        | ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1 )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f141,plain,
    ( spl5_3
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f140,f95,f77])).

fof(f95,plain,
    ( spl5_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f140,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_6 ),
    inference(resolution,[],[f96,f38])).

fof(f96,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f123,plain,
    ( spl5_4
    | spl5_3
    | spl5_2
    | ~ spl5_5
    | ~ spl5_10
    | spl5_1 ),
    inference(avatar_split_clause,[],[f114,f69,f121,f85,f73,f77,f81])).

fof(f69,plain,
    ( spl5_1
  <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f114,plain,
    ( sK3 != k2_mcart_1(sK4)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl5_1 ),
    inference(superposition,[],[f70,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f54,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f70,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f113,plain,
    ( spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f111,f103,f81])).

fof(f103,plain,
    ( spl5_8
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f111,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_8 ),
    inference(resolution,[],[f104,f38])).

fof(f104,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f108,plain,
    ( spl5_8
    | spl5_9
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f101,f98,f106,f103])).

fof(f98,plain,
    ( spl5_7
  <=> ! [X1,X3,X0,X2] :
        ( sK3 = X0
        | ~ r2_hidden(k2_mcart_1(X1),sK1)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3))
        | ~ m1_subset_1(k1_mcart_1(X1),sK0)
        | sK4 != k4_tarski(X1,X0)
        | ~ m1_subset_1(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f101,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k2_mcart_1(X0),sK1)
        | k1_xboole_0 = X1
        | k1_xboole_0 = X2
        | ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
        | sK3 = X3
        | sK4 != k4_tarski(X0,X3)
        | ~ m1_subset_1(X3,sK2)
        | ~ r2_hidden(k1_mcart_1(X0),sK0)
        | v1_xboole_0(sK0) )
    | ~ spl5_7 ),
    inference(resolution,[],[f99,f40])).

fof(f99,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(k1_mcart_1(X1),sK0)
        | ~ r2_hidden(k2_mcart_1(X1),sK1)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3))
        | sK3 = X0
        | sK4 != k4_tarski(X1,X0)
        | ~ m1_subset_1(X0,sK2) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f100,plain,
    ( spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f93,f98,f95])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( sK3 = X0
      | ~ m1_subset_1(X0,sK2)
      | sK4 != k4_tarski(X1,X0)
      | ~ m1_subset_1(k1_mcart_1(X1),sK0)
      | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | ~ r2_hidden(k2_mcart_1(X1),sK1)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f90,f40])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK1)
      | sK3 = X1
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | ~ m1_subset_1(X0,k2_zfmisc_1(X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f58,f47])).

fof(f58,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f33,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X7
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X7
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f87,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f59,f85])).

fof(f59,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f32,f49])).

fof(f32,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f34,f81])).

fof(f34,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f35,f77])).

fof(f35,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f36,f73])).

fof(f36,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f37,f69])).

fof(f37,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (27794)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (27785)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (27800)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (27800)Refutation not found, incomplete strategy% (27800)------------------------------
% 0.21/0.51  % (27800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27800)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (27800)Memory used [KB]: 10746
% 0.21/0.51  % (27800)Time elapsed: 0.092 s
% 0.21/0.51  % (27800)------------------------------
% 0.21/0.51  % (27800)------------------------------
% 0.21/0.52  % (27802)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (27784)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (27779)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (27779)Refutation not found, incomplete strategy% (27779)------------------------------
% 0.21/0.53  % (27779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27779)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27779)Memory used [KB]: 1791
% 0.21/0.53  % (27779)Time elapsed: 0.125 s
% 0.21/0.53  % (27779)------------------------------
% 0.21/0.53  % (27779)------------------------------
% 0.21/0.53  % (27782)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (27781)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (27781)Refutation not found, incomplete strategy% (27781)------------------------------
% 0.21/0.54  % (27781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27781)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27781)Memory used [KB]: 10746
% 0.21/0.54  % (27781)Time elapsed: 0.124 s
% 0.21/0.54  % (27781)------------------------------
% 0.21/0.54  % (27781)------------------------------
% 0.21/0.54  % (27792)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (27808)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (27810)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.49/0.54  % (27809)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.49/0.55  % (27797)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.49/0.55  % (27807)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.49/0.55  % (27799)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.49/0.55  % (27789)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.49/0.55  % (27786)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.49/0.55  % (27796)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.49/0.56  % (27791)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.49/0.56  % (27780)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.49/0.56  % (27797)Refutation not found, incomplete strategy% (27797)------------------------------
% 1.49/0.56  % (27797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (27797)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (27797)Memory used [KB]: 10618
% 1.49/0.56  % (27797)Time elapsed: 0.146 s
% 1.49/0.56  % (27797)------------------------------
% 1.49/0.56  % (27797)------------------------------
% 1.49/0.56  % (27790)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.49/0.56  % (27783)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.49/0.56  % (27790)Refutation not found, incomplete strategy% (27790)------------------------------
% 1.49/0.56  % (27790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (27790)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (27790)Memory used [KB]: 10618
% 1.49/0.56  % (27790)Time elapsed: 0.140 s
% 1.49/0.56  % (27790)------------------------------
% 1.49/0.56  % (27790)------------------------------
% 1.57/0.56  % (27798)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.57/0.56  % (27804)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.57/0.56  % (27811)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.57/0.57  % (27787)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.57/0.57  % (27795)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.57/0.57  % (27803)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.57/0.57  % (27801)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.57/0.58  % (27793)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.57/0.58  % (27799)Refutation found. Thanks to Tanya!
% 1.57/0.58  % SZS status Theorem for theBenchmark
% 1.57/0.59  % SZS output start Proof for theBenchmark
% 1.57/0.59  fof(f428,plain,(
% 1.57/0.59    $false),
% 1.57/0.59    inference(avatar_sat_refutation,[],[f71,f75,f79,f83,f87,f100,f108,f113,f123,f141,f158,f178,f201,f231,f239,f266,f294,f328,f332,f420,f427])).
% 1.57/0.59  fof(f427,plain,(
% 1.57/0.59    spl5_3 | spl5_4 | ~spl5_27),
% 1.57/0.59    inference(avatar_split_clause,[],[f424,f264,f81,f77])).
% 1.57/0.59  fof(f77,plain,(
% 1.57/0.59    spl5_3 <=> k1_xboole_0 = sK1),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.57/0.59  fof(f81,plain,(
% 1.57/0.59    spl5_4 <=> k1_xboole_0 = sK0),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.57/0.59  fof(f264,plain,(
% 1.57/0.59    spl5_27 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.57/0.59  fof(f424,plain,(
% 1.57/0.59    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl5_27),
% 1.57/0.59    inference(trivial_inequality_removal,[],[f423])).
% 1.57/0.59  fof(f423,plain,(
% 1.57/0.59    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl5_27),
% 1.57/0.59    inference(superposition,[],[f44,f265])).
% 1.57/0.59  fof(f265,plain,(
% 1.57/0.59    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl5_27),
% 1.57/0.59    inference(avatar_component_clause,[],[f264])).
% 1.57/0.59  fof(f44,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 1.57/0.59    inference(cnf_transformation,[],[f31])).
% 1.57/0.59  fof(f31,plain,(
% 1.57/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.57/0.59    inference(flattening,[],[f30])).
% 1.57/0.59  fof(f30,plain,(
% 1.57/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.57/0.59    inference(nnf_transformation,[],[f2])).
% 1.57/0.59  fof(f2,axiom,(
% 1.57/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.57/0.59  fof(f420,plain,(
% 1.57/0.59    spl5_2 | spl5_27 | ~spl5_5 | ~spl5_19),
% 1.57/0.59    inference(avatar_split_clause,[],[f416,f176,f85,f264,f73])).
% 1.57/0.59  fof(f73,plain,(
% 1.57/0.59    spl5_2 <=> k1_xboole_0 = sK2),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.57/0.59  fof(f85,plain,(
% 1.57/0.59    spl5_5 <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.57/0.59  fof(f176,plain,(
% 1.57/0.59    spl5_19 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~m1_subset_1(sK4,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.57/0.59  fof(f416,plain,(
% 1.57/0.59    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | (~spl5_5 | ~spl5_19)),
% 1.57/0.59    inference(resolution,[],[f177,f86])).
% 1.57/0.59  fof(f86,plain,(
% 1.57/0.59    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_5),
% 1.57/0.59    inference(avatar_component_clause,[],[f85])).
% 1.57/0.59  fof(f177,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 | k1_xboole_0 = X1) ) | ~spl5_19),
% 1.57/0.59    inference(avatar_component_clause,[],[f176])).
% 1.57/0.59  fof(f332,plain,(
% 1.57/0.59    spl5_2 | ~spl5_13),
% 1.57/0.59    inference(avatar_split_clause,[],[f331,f153,f73])).
% 1.57/0.59  fof(f153,plain,(
% 1.57/0.59    spl5_13 <=> v1_xboole_0(sK2)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.57/0.59  fof(f331,plain,(
% 1.57/0.59    k1_xboole_0 = sK2 | ~spl5_13),
% 1.57/0.59    inference(resolution,[],[f154,f38])).
% 1.57/0.59  fof(f38,plain,(
% 1.57/0.59    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.57/0.59    inference(cnf_transformation,[],[f17])).
% 1.57/0.59  fof(f17,plain,(
% 1.57/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.57/0.59    inference(ennf_transformation,[],[f1])).
% 1.57/0.59  fof(f1,axiom,(
% 1.57/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.57/0.59  fof(f154,plain,(
% 1.57/0.59    v1_xboole_0(sK2) | ~spl5_13),
% 1.57/0.59    inference(avatar_component_clause,[],[f153])).
% 1.57/0.59  fof(f328,plain,(
% 1.57/0.59    spl5_2 | spl5_27 | ~spl5_26),
% 1.57/0.59    inference(avatar_split_clause,[],[f325,f237,f264,f73])).
% 1.57/0.59  fof(f237,plain,(
% 1.57/0.59    spl5_26 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.57/0.59  fof(f325,plain,(
% 1.57/0.59    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl5_26),
% 1.57/0.59    inference(trivial_inequality_removal,[],[f324])).
% 1.57/0.59  fof(f324,plain,(
% 1.57/0.59    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl5_26),
% 1.57/0.59    inference(superposition,[],[f44,f238])).
% 1.57/0.59  fof(f238,plain,(
% 1.57/0.59    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl5_26),
% 1.57/0.59    inference(avatar_component_clause,[],[f237])).
% 1.57/0.59  fof(f294,plain,(
% 1.57/0.59    spl5_23 | ~spl5_5 | ~spl5_18),
% 1.57/0.59    inference(avatar_split_clause,[],[f289,f173,f85,f199])).
% 1.57/0.59  fof(f199,plain,(
% 1.57/0.59    spl5_23 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.57/0.59  fof(f173,plain,(
% 1.57/0.59    spl5_18 <=> ! [X2] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X2))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.57/0.59  fof(f289,plain,(
% 1.57/0.59    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | (~spl5_5 | ~spl5_18)),
% 1.57/0.59    inference(resolution,[],[f282,f86])).
% 1.57/0.59  fof(f282,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))) ) | ~spl5_18),
% 1.57/0.59    inference(resolution,[],[f267,f39])).
% 1.57/0.59  fof(f39,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f29])).
% 1.57/0.59  fof(f29,plain,(
% 1.57/0.59    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.57/0.59    inference(nnf_transformation,[],[f18])).
% 1.57/0.59  fof(f18,plain,(
% 1.57/0.59    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.57/0.59    inference(ennf_transformation,[],[f3])).
% 1.57/0.59  fof(f3,axiom,(
% 1.57/0.59    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.57/0.59  fof(f267,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))) ) | ~spl5_18),
% 1.57/0.59    inference(resolution,[],[f174,f50])).
% 1.57/0.59  fof(f50,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f22])).
% 1.57/0.59  fof(f22,plain,(
% 1.57/0.59    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.57/0.59    inference(ennf_transformation,[],[f10])).
% 1.57/0.59  fof(f10,axiom,(
% 1.57/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.57/0.59  fof(f174,plain,(
% 1.57/0.59    ( ! [X2] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X2))) ) | ~spl5_18),
% 1.57/0.59    inference(avatar_component_clause,[],[f173])).
% 1.57/0.59  fof(f266,plain,(
% 1.57/0.59    spl5_27 | spl5_23 | spl5_4 | spl5_3 | ~spl5_5 | ~spl5_16),
% 1.57/0.59    inference(avatar_split_clause,[],[f257,f167,f85,f77,f81,f199,f264])).
% 1.57/0.59  fof(f167,plain,(
% 1.57/0.59    spl5_16 <=> ! [X5,X4] : (k1_xboole_0 = X4 | ~m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5)) | k1_xboole_0 = X5)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.57/0.59  fof(f257,plain,(
% 1.57/0.59    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl5_5 | ~spl5_16)),
% 1.57/0.59    inference(resolution,[],[f254,f86])).
% 1.57/0.59  fof(f254,plain,(
% 1.57/0.59    ( ! [X10,X8,X9] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10)) | k1_xboole_0 = X9 | k1_xboole_0 = X8 | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10)) | k1_xboole_0 = k2_zfmisc_1(X8,X9)) ) | ~spl5_16),
% 1.57/0.59    inference(resolution,[],[f248,f38])).
% 1.57/0.59  fof(f248,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) ) | ~spl5_16),
% 1.57/0.59    inference(resolution,[],[f243,f39])).
% 1.57/0.59  fof(f243,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X0),X2)) | k1_xboole_0 = X1 | v1_xboole_0(k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) ) | ~spl5_16),
% 1.57/0.59    inference(resolution,[],[f240,f50])).
% 1.57/0.59  fof(f240,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | v1_xboole_0(k2_zfmisc_1(X0,X1))) ) | ~spl5_16),
% 1.57/0.59    inference(resolution,[],[f168,f40])).
% 1.57/0.59  fof(f40,plain,(
% 1.57/0.59    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f29])).
% 1.57/0.59  fof(f168,plain,(
% 1.57/0.59    ( ! [X4,X5] : (~m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5)) | k1_xboole_0 = X4 | k1_xboole_0 = X5) ) | ~spl5_16),
% 1.57/0.59    inference(avatar_component_clause,[],[f167])).
% 1.57/0.59  fof(f239,plain,(
% 1.57/0.59    spl5_26 | ~spl5_23),
% 1.57/0.59    inference(avatar_split_clause,[],[f235,f199,f237])).
% 1.57/0.59  fof(f235,plain,(
% 1.57/0.59    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl5_23),
% 1.57/0.59    inference(resolution,[],[f200,f38])).
% 1.57/0.59  fof(f200,plain,(
% 1.57/0.59    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_23),
% 1.57/0.59    inference(avatar_component_clause,[],[f199])).
% 1.57/0.59  fof(f231,plain,(
% 1.57/0.59    spl5_23 | ~spl5_5 | ~spl5_17),
% 1.57/0.59    inference(avatar_split_clause,[],[f226,f170,f85,f199])).
% 1.57/0.59  fof(f170,plain,(
% 1.57/0.59    spl5_17 <=> ! [X3] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X3,sK1))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.57/0.59  fof(f226,plain,(
% 1.57/0.59    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | (~spl5_5 | ~spl5_17)),
% 1.57/0.59    inference(resolution,[],[f219,f86])).
% 1.57/0.59  fof(f219,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | ~spl5_17),
% 1.57/0.59    inference(resolution,[],[f202,f39])).
% 1.57/0.59  fof(f202,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | ~spl5_17),
% 1.57/0.59    inference(resolution,[],[f171,f50])).
% 1.57/0.59  fof(f171,plain,(
% 1.57/0.59    ( ! [X3] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X3,sK1))) ) | ~spl5_17),
% 1.57/0.59    inference(avatar_component_clause,[],[f170])).
% 1.57/0.59  fof(f201,plain,(
% 1.57/0.59    spl5_23 | ~spl5_5 | ~spl5_15),
% 1.57/0.59    inference(avatar_split_clause,[],[f194,f163,f85,f199])).
% 1.57/0.59  fof(f163,plain,(
% 1.57/0.59    spl5_15 <=> ! [X6] : ~r2_hidden(sK4,k2_zfmisc_1(X6,sK2))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.57/0.59  fof(f194,plain,(
% 1.57/0.59    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | (~spl5_5 | ~spl5_15)),
% 1.57/0.59    inference(resolution,[],[f179,f86])).
% 1.57/0.59  fof(f179,plain,(
% 1.57/0.59    ( ! [X0] : (~m1_subset_1(sK4,k2_zfmisc_1(X0,sK2)) | v1_xboole_0(k2_zfmisc_1(X0,sK2))) ) | ~spl5_15),
% 1.57/0.59    inference(resolution,[],[f164,f39])).
% 1.57/0.59  fof(f164,plain,(
% 1.57/0.59    ( ! [X6] : (~r2_hidden(sK4,k2_zfmisc_1(X6,sK2))) ) | ~spl5_15),
% 1.57/0.59    inference(avatar_component_clause,[],[f163])).
% 1.57/0.59  fof(f178,plain,(
% 1.57/0.59    spl5_15 | spl5_10 | spl5_16 | spl5_17 | spl5_18 | spl5_19 | ~spl5_14),
% 1.57/0.59    inference(avatar_split_clause,[],[f161,f156,f176,f173,f170,f167,f121,f163])).
% 1.57/0.59  fof(f121,plain,(
% 1.57/0.59    spl5_10 <=> sK3 = k2_mcart_1(sK4)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.57/0.59  fof(f156,plain,(
% 1.57/0.59    spl5_14 <=> ! [X1,X3,X5,X0,X2,X4,X6] : (sK4 != X0 | ~r2_hidden(k2_mcart_1(X0),sK2) | k1_xboole_0 = X5 | k1_xboole_0 = X6 | ~m1_subset_1(X0,k2_zfmisc_1(X5,X6)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X4)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(k1_mcart_1(X0),k2_zfmisc_1(X1,X2)) | k2_mcart_1(X0) = sK3)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.57/0.59  fof(f161,plain,(
% 1.57/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | ~m1_subset_1(sK4,k2_zfmisc_1(X0,X1)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X2)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X3,sK1)) | k1_xboole_0 = X4 | k1_xboole_0 = X5 | ~m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5)) | sK3 = k2_mcart_1(sK4) | ~r2_hidden(sK4,k2_zfmisc_1(X6,sK2))) ) | ~spl5_14),
% 1.57/0.59    inference(equality_resolution,[],[f159])).
% 1.57/0.59  fof(f159,plain,(
% 1.57/0.59    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sK4 != X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X0,k2_zfmisc_1(X1,X2)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X3)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,sK1)) | k1_xboole_0 = X5 | k1_xboole_0 = X6 | ~m1_subset_1(k1_mcart_1(X0),k2_zfmisc_1(X5,X6)) | k2_mcart_1(X0) = sK3 | ~r2_hidden(X0,k2_zfmisc_1(X7,sK2))) ) | ~spl5_14),
% 1.57/0.59    inference(resolution,[],[f157,f51])).
% 1.57/0.59  fof(f51,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f22])).
% 1.57/0.59  fof(f157,plain,(
% 1.57/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~r2_hidden(k2_mcart_1(X0),sK2) | sK4 != X0 | k1_xboole_0 = X5 | k1_xboole_0 = X6 | ~m1_subset_1(X0,k2_zfmisc_1(X5,X6)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X4)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(k1_mcart_1(X0),k2_zfmisc_1(X1,X2)) | k2_mcart_1(X0) = sK3) ) | ~spl5_14),
% 1.57/0.59    inference(avatar_component_clause,[],[f156])).
% 1.57/0.59  fof(f158,plain,(
% 1.57/0.59    spl5_13 | spl5_14 | ~spl5_9),
% 1.57/0.59    inference(avatar_split_clause,[],[f151,f106,f156,f153])).
% 1.57/0.59  fof(f106,plain,(
% 1.57/0.59    spl5_9 <=> ! [X1,X3,X0,X2] : (~r2_hidden(k2_mcart_1(X0),sK1) | ~r2_hidden(k1_mcart_1(X0),sK0) | ~m1_subset_1(X3,sK2) | sK4 != k4_tarski(X0,X3) | sK3 = X3 | ~m1_subset_1(X0,k2_zfmisc_1(X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.57/0.59  fof(f151,plain,(
% 1.57/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sK4 != X0 | k2_mcart_1(X0) = sK3 | ~m1_subset_1(k1_mcart_1(X0),k2_zfmisc_1(X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X4)) | ~m1_subset_1(X0,k2_zfmisc_1(X5,X6)) | k1_xboole_0 = X6 | k1_xboole_0 = X5 | ~r2_hidden(k2_mcart_1(X0),sK2) | v1_xboole_0(sK2)) ) | ~spl5_9),
% 1.57/0.59    inference(resolution,[],[f148,f40])).
% 1.57/0.59  fof(f148,plain,(
% 1.57/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k2_mcart_1(X0),sK2) | sK4 != X0 | k2_mcart_1(X0) = sK3 | ~m1_subset_1(k1_mcart_1(X0),k2_zfmisc_1(X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X4)) | ~m1_subset_1(X0,k2_zfmisc_1(X5,X6)) | k1_xboole_0 = X6 | k1_xboole_0 = X5) ) | ~spl5_9),
% 1.57/0.59    inference(superposition,[],[f145,f47])).
% 1.57/0.59  fof(f47,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.57/0.59    inference(cnf_transformation,[],[f21])).
% 1.57/0.59  fof(f21,plain,(
% 1.57/0.59    ! [X0,X1] : (! [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.57/0.59    inference(ennf_transformation,[],[f11])).
% 1.57/0.59  fof(f11,axiom,(
% 1.57/0.59    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).
% 1.57/0.59  fof(f145,plain,(
% 1.57/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (sK4 != k4_tarski(X1,X0) | ~m1_subset_1(X0,sK2) | sK3 = X0 | ~m1_subset_1(X1,k2_zfmisc_1(X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | ~r2_hidden(X1,k2_zfmisc_1(X4,sK1)) | ~r2_hidden(X1,k2_zfmisc_1(sK0,X5))) ) | ~spl5_9),
% 1.57/0.59    inference(resolution,[],[f143,f50])).
% 1.57/0.59  fof(f143,plain,(
% 1.57/0.59    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k1_mcart_1(X0),sK0) | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | sK3 = X1 | ~m1_subset_1(X0,k2_zfmisc_1(X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | ~r2_hidden(X0,k2_zfmisc_1(X4,sK1))) ) | ~spl5_9),
% 1.57/0.59    inference(resolution,[],[f107,f51])).
% 1.57/0.59  fof(f107,plain,(
% 1.57/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k2_mcart_1(X0),sK1) | ~r2_hidden(k1_mcart_1(X0),sK0) | ~m1_subset_1(X3,sK2) | sK4 != k4_tarski(X0,X3) | sK3 = X3 | ~m1_subset_1(X0,k2_zfmisc_1(X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1) ) | ~spl5_9),
% 1.57/0.59    inference(avatar_component_clause,[],[f106])).
% 1.57/0.59  fof(f141,plain,(
% 1.57/0.59    spl5_3 | ~spl5_6),
% 1.57/0.59    inference(avatar_split_clause,[],[f140,f95,f77])).
% 1.57/0.59  fof(f95,plain,(
% 1.57/0.59    spl5_6 <=> v1_xboole_0(sK1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.57/0.59  fof(f140,plain,(
% 1.57/0.59    k1_xboole_0 = sK1 | ~spl5_6),
% 1.57/0.59    inference(resolution,[],[f96,f38])).
% 1.57/0.59  fof(f96,plain,(
% 1.57/0.59    v1_xboole_0(sK1) | ~spl5_6),
% 1.57/0.59    inference(avatar_component_clause,[],[f95])).
% 1.57/0.59  fof(f123,plain,(
% 1.57/0.59    spl5_4 | spl5_3 | spl5_2 | ~spl5_5 | ~spl5_10 | spl5_1),
% 1.57/0.59    inference(avatar_split_clause,[],[f114,f69,f121,f85,f73,f77,f81])).
% 1.57/0.59  fof(f69,plain,(
% 1.57/0.59    spl5_1 <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK4)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.57/0.59  fof(f114,plain,(
% 1.57/0.59    sK3 != k2_mcart_1(sK4) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl5_1),
% 1.57/0.59    inference(superposition,[],[f70,f60])).
% 1.57/0.59  fof(f60,plain,(
% 1.57/0.59    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.57/0.59    inference(definition_unfolding,[],[f54,f49])).
% 1.57/0.59  fof(f49,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f6])).
% 1.57/0.59  fof(f6,axiom,(
% 1.57/0.59    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.57/0.59  fof(f54,plain,(
% 1.57/0.59    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.57/0.59    inference(cnf_transformation,[],[f23])).
% 1.57/0.59  fof(f23,plain,(
% 1.57/0.59    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.57/0.59    inference(ennf_transformation,[],[f12])).
% 1.57/0.59  fof(f12,axiom,(
% 1.57/0.59    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.57/0.59  fof(f70,plain,(
% 1.57/0.59    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) | spl5_1),
% 1.57/0.59    inference(avatar_component_clause,[],[f69])).
% 1.57/0.59  fof(f113,plain,(
% 1.57/0.59    spl5_4 | ~spl5_8),
% 1.57/0.59    inference(avatar_split_clause,[],[f111,f103,f81])).
% 1.57/0.59  fof(f103,plain,(
% 1.57/0.59    spl5_8 <=> v1_xboole_0(sK0)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.57/0.59  fof(f111,plain,(
% 1.57/0.59    k1_xboole_0 = sK0 | ~spl5_8),
% 1.57/0.59    inference(resolution,[],[f104,f38])).
% 1.57/0.59  fof(f104,plain,(
% 1.57/0.59    v1_xboole_0(sK0) | ~spl5_8),
% 1.57/0.59    inference(avatar_component_clause,[],[f103])).
% 1.57/0.59  fof(f108,plain,(
% 1.57/0.59    spl5_8 | spl5_9 | ~spl5_7),
% 1.57/0.59    inference(avatar_split_clause,[],[f101,f98,f106,f103])).
% 1.57/0.59  fof(f98,plain,(
% 1.57/0.59    spl5_7 <=> ! [X1,X3,X0,X2] : (sK3 = X0 | ~r2_hidden(k2_mcart_1(X1),sK1) | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X1,k2_zfmisc_1(X2,X3)) | ~m1_subset_1(k1_mcart_1(X1),sK0) | sK4 != k4_tarski(X1,X0) | ~m1_subset_1(X0,sK2))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.57/0.59  fof(f101,plain,(
% 1.57/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k2_mcart_1(X0),sK1) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X0,k2_zfmisc_1(X1,X2)) | sK3 = X3 | sK4 != k4_tarski(X0,X3) | ~m1_subset_1(X3,sK2) | ~r2_hidden(k1_mcart_1(X0),sK0) | v1_xboole_0(sK0)) ) | ~spl5_7),
% 1.57/0.59    inference(resolution,[],[f99,f40])).
% 1.57/0.59  fof(f99,plain,(
% 1.57/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k1_mcart_1(X1),sK0) | ~r2_hidden(k2_mcart_1(X1),sK1) | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X1,k2_zfmisc_1(X2,X3)) | sK3 = X0 | sK4 != k4_tarski(X1,X0) | ~m1_subset_1(X0,sK2)) ) | ~spl5_7),
% 1.57/0.59    inference(avatar_component_clause,[],[f98])).
% 1.57/0.59  fof(f100,plain,(
% 1.57/0.59    spl5_6 | spl5_7),
% 1.57/0.59    inference(avatar_split_clause,[],[f93,f98,f95])).
% 1.57/0.59  fof(f93,plain,(
% 1.57/0.59    ( ! [X2,X0,X3,X1] : (sK3 = X0 | ~m1_subset_1(X0,sK2) | sK4 != k4_tarski(X1,X0) | ~m1_subset_1(k1_mcart_1(X1),sK0) | ~m1_subset_1(X1,k2_zfmisc_1(X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | ~r2_hidden(k2_mcart_1(X1),sK1) | v1_xboole_0(sK1)) )),
% 1.57/0.59    inference(resolution,[],[f90,f40])).
% 1.57/0.59  fof(f90,plain,(
% 1.57/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_mcart_1(X0),sK1) | sK3 = X1 | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | ~m1_subset_1(k1_mcart_1(X0),sK0) | ~m1_subset_1(X0,k2_zfmisc_1(X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2) )),
% 1.57/0.59    inference(superposition,[],[f58,f47])).
% 1.57/0.59  fof(f58,plain,(
% 1.57/0.59    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X7 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.57/0.59    inference(definition_unfolding,[],[f33,f48])).
% 1.57/0.59  fof(f48,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f5])).
% 1.57/0.59  fof(f5,axiom,(
% 1.57/0.59    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.57/0.59  fof(f33,plain,(
% 1.57/0.59    ( ! [X6,X7,X5] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f28])).
% 1.57/0.59  fof(f28,plain,(
% 1.57/0.59    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.57/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f27])).
% 1.57/0.59  fof(f27,plain,(
% 1.57/0.59    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 1.57/0.59    introduced(choice_axiom,[])).
% 1.57/0.59  fof(f16,plain,(
% 1.57/0.59    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.57/0.59    inference(flattening,[],[f15])).
% 1.57/0.59  fof(f15,plain,(
% 1.57/0.59    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.57/0.59    inference(ennf_transformation,[],[f14])).
% 1.57/0.59  fof(f14,negated_conjecture,(
% 1.57/0.59    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.57/0.59    inference(negated_conjecture,[],[f13])).
% 1.57/0.59  fof(f13,conjecture,(
% 1.57/0.59    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 1.57/0.59  fof(f87,plain,(
% 1.57/0.59    spl5_5),
% 1.57/0.59    inference(avatar_split_clause,[],[f59,f85])).
% 1.57/0.59  fof(f59,plain,(
% 1.57/0.59    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.57/0.59    inference(definition_unfolding,[],[f32,f49])).
% 1.57/0.59  fof(f32,plain,(
% 1.57/0.59    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.57/0.59    inference(cnf_transformation,[],[f28])).
% 1.57/0.59  fof(f83,plain,(
% 1.57/0.59    ~spl5_4),
% 1.57/0.59    inference(avatar_split_clause,[],[f34,f81])).
% 1.57/0.59  fof(f34,plain,(
% 1.57/0.59    k1_xboole_0 != sK0),
% 1.57/0.59    inference(cnf_transformation,[],[f28])).
% 1.57/0.59  fof(f79,plain,(
% 1.57/0.59    ~spl5_3),
% 1.57/0.59    inference(avatar_split_clause,[],[f35,f77])).
% 1.57/0.59  fof(f35,plain,(
% 1.57/0.59    k1_xboole_0 != sK1),
% 1.57/0.59    inference(cnf_transformation,[],[f28])).
% 1.57/0.59  fof(f75,plain,(
% 1.57/0.59    ~spl5_2),
% 1.57/0.59    inference(avatar_split_clause,[],[f36,f73])).
% 1.57/0.59  fof(f36,plain,(
% 1.57/0.59    k1_xboole_0 != sK2),
% 1.57/0.59    inference(cnf_transformation,[],[f28])).
% 1.57/0.59  fof(f71,plain,(
% 1.57/0.59    ~spl5_1),
% 1.57/0.59    inference(avatar_split_clause,[],[f37,f69])).
% 1.57/0.59  fof(f37,plain,(
% 1.57/0.59    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 1.57/0.59    inference(cnf_transformation,[],[f28])).
% 1.57/0.59  % SZS output end Proof for theBenchmark
% 1.57/0.59  % (27799)------------------------------
% 1.57/0.59  % (27799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (27799)Termination reason: Refutation
% 1.57/0.59  
% 1.57/0.59  % (27799)Memory used [KB]: 11001
% 1.57/0.59  % (27799)Time elapsed: 0.177 s
% 1.57/0.59  % (27799)------------------------------
% 1.57/0.59  % (27799)------------------------------
% 1.57/0.59  % (27778)Success in time 0.227 s
%------------------------------------------------------------------------------
