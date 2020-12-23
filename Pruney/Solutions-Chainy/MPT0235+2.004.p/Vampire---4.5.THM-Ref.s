%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:28 EST 2020

% Result     : Theorem 1.99s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 186 expanded)
%              Number of leaves         :   27 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  408 ( 802 expanded)
%              Number of equality atoms :  177 ( 392 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f466,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f70,f74,f78,f86,f90,f110,f141,f150,f156,f167,f183,f188,f232,f239,f261,f281,f350,f362,f452])).

fof(f452,plain,
    ( spl3_1
    | spl3_33
    | spl3_42
    | ~ spl3_45 ),
    inference(avatar_contradiction_clause,[],[f451])).

fof(f451,plain,
    ( $false
    | spl3_1
    | spl3_33
    | spl3_42
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f260,f432])).

fof(f432,plain,
    ( k1_xboole_0 = sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | spl3_1
    | spl3_33
    | spl3_42
    | ~ spl3_45 ),
    inference(unit_resulting_resolution,[],[f57,f260,f349,f349,f361])).

fof(f361,plain,
    ( ! [X6,X4,X5] :
        ( k1_tarski(X6) = sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6)))
        | k2_tarski(X4,X5) = k1_zfmisc_1(k1_tarski(X6))
        | sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) = X5
        | sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) = X4
        | k1_xboole_0 = sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) )
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl3_45
  <=> ! [X5,X4,X6] :
        ( sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) = X4
        | k2_tarski(X4,X5) = k1_zfmisc_1(k1_tarski(X6))
        | sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) = X5
        | k1_tarski(X6) = sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6)))
        | k1_xboole_0 = sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f349,plain,
    ( k1_tarski(sK0) != sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | spl3_42 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl3_42
  <=> k1_tarski(sK0) = sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f57,plain,
    ( k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_1
  <=> k1_zfmisc_1(k1_tarski(sK0)) = k2_tarski(k1_xboole_0,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f260,plain,
    ( k1_xboole_0 != sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | spl3_33 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl3_33
  <=> k1_xboole_0 = sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f362,plain,
    ( spl3_45
    | ~ spl3_30
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f241,f237,f230,f360])).

fof(f230,plain,
    ( spl3_30
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X1,k1_tarski(X0))
        | k1_tarski(X0) = X1
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f237,plain,
    ( spl3_31
  <=> ! [X1,X0,X2] :
        ( sK2(X0,X1,k1_zfmisc_1(X2)) = X1
        | sK2(X0,X1,k1_zfmisc_1(X2)) = X0
        | k2_tarski(X0,X1) = k1_zfmisc_1(X2)
        | r1_tarski(sK2(X0,X1,k1_zfmisc_1(X2)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f241,plain,
    ( ! [X6,X4,X5] :
        ( sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) = X4
        | k2_tarski(X4,X5) = k1_zfmisc_1(k1_tarski(X6))
        | sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) = X5
        | k1_tarski(X6) = sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6)))
        | k1_xboole_0 = sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) )
    | ~ spl3_30
    | ~ spl3_31 ),
    inference(resolution,[],[f238,f231])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_tarski(X0))
        | k1_tarski(X0) = X1
        | k1_xboole_0 = X1 )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f230])).

fof(f238,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(sK2(X0,X1,k1_zfmisc_1(X2)),X2)
        | sK2(X0,X1,k1_zfmisc_1(X2)) = X0
        | k2_tarski(X0,X1) = k1_zfmisc_1(X2)
        | sK2(X0,X1,k1_zfmisc_1(X2)) = X1 )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f237])).

fof(f350,plain,
    ( ~ spl3_42
    | spl3_1
    | ~ spl3_16
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f283,f279,f139,f55,f347])).

fof(f139,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] :
        ( k2_tarski(X0,X1) = X2
        | sK2(X0,X1,X2) != X1
        | ~ r2_hidden(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f279,plain,
    ( spl3_35
  <=> ! [X0] : r2_hidden(k1_tarski(X0),k1_zfmisc_1(k1_tarski(X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f283,plain,
    ( k1_tarski(sK0) != sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | spl3_1
    | ~ spl3_16
    | ~ spl3_35 ),
    inference(unit_resulting_resolution,[],[f57,f280,f140])).

fof(f140,plain,
    ( ! [X2,X0,X1] :
        ( sK2(X0,X1,X2) != X1
        | k2_tarski(X0,X1) = X2
        | ~ r2_hidden(X1,X2) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f139])).

fof(f280,plain,
    ( ! [X0] : r2_hidden(k1_tarski(X0),k1_zfmisc_1(k1_tarski(X0)))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f279])).

fof(f281,plain,
    ( spl3_35
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f184,f181,f84,f279])).

fof(f84,plain,
    ( spl3_8
  <=> ! [X3,X0] :
        ( r2_hidden(X3,k1_zfmisc_1(X0))
        | ~ r1_tarski(X3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f181,plain,
    ( spl3_23
  <=> ! [X0] : r1_tarski(k1_tarski(X0),k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f184,plain,
    ( ! [X0] : r2_hidden(k1_tarski(X0),k1_zfmisc_1(k1_tarski(X0)))
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f182,f85])).

fof(f85,plain,
    ( ! [X0,X3] :
        ( r2_hidden(X3,k1_zfmisc_1(X0))
        | ~ r1_tarski(X3,X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f182,plain,
    ( ! [X0] : r1_tarski(k1_tarski(X0),k1_tarski(X0))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f181])).

fof(f261,plain,
    ( ~ spl3_33
    | spl3_1
    | ~ spl3_18
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f220,f186,f148,f55,f258])).

fof(f148,plain,
    ( spl3_18
  <=> ! [X1,X0,X2] :
        ( k2_tarski(X0,X1) = X2
        | sK2(X0,X1,X2) != X0
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f186,plain,
    ( spl3_24
  <=> ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_tarski(X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f220,plain,
    ( k1_xboole_0 != sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | spl3_1
    | ~ spl3_18
    | ~ spl3_24 ),
    inference(unit_resulting_resolution,[],[f57,f187,f149])).

fof(f149,plain,
    ( ! [X2,X0,X1] :
        ( sK2(X0,X1,X2) != X0
        | k2_tarski(X0,X1) = X2
        | ~ r2_hidden(X0,X2) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f148])).

fof(f187,plain,
    ( ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_tarski(X0)))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f186])).

fof(f239,plain,
    ( spl3_31
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f168,f165,f88,f237])).

fof(f88,plain,
    ( spl3_9
  <=> ! [X3,X0] :
        ( r1_tarski(X3,X0)
        | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f165,plain,
    ( spl3_20
  <=> ! [X1,X0,X2] :
        ( k2_tarski(X0,X1) = X2
        | sK2(X0,X1,X2) = X1
        | sK2(X0,X1,X2) = X0
        | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f168,plain,
    ( ! [X2,X0,X1] :
        ( sK2(X0,X1,k1_zfmisc_1(X2)) = X1
        | sK2(X0,X1,k1_zfmisc_1(X2)) = X0
        | k2_tarski(X0,X1) = k1_zfmisc_1(X2)
        | r1_tarski(sK2(X0,X1,k1_zfmisc_1(X2)),X2) )
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(resolution,[],[f166,f89])).

fof(f89,plain,
    ( ! [X0,X3] :
        ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
        | r1_tarski(X3,X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f166,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK2(X0,X1,X2),X2)
        | sK2(X0,X1,X2) = X1
        | sK2(X0,X1,X2) = X0
        | k2_tarski(X0,X1) = X2 )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f165])).

fof(f232,plain,
    ( spl3_30
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f163,f154,f72,f230])).

fof(f72,plain,
    ( spl3_5
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f154,plain,
    ( spl3_19
  <=> ! [X1,X0,X2] :
        ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_tarski(X0))
        | k1_tarski(X0) = X1
        | k1_xboole_0 = X1 )
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_tarski(X0))
        | k1_tarski(X0) = X1
        | k1_tarski(X0) = X1
        | k1_xboole_0 = X1
        | k1_tarski(X0) = X1 )
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(superposition,[],[f155,f73])).

fof(f73,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f155,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k2_tarski(X1,X2))
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k2_tarski(X1,X2) = X0 )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f154])).

fof(f188,plain,
    ( spl3_24
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f175,f108,f84,f186])).

fof(f108,plain,
    ( spl3_12
  <=> ! [X0] : r1_tarski(k1_xboole_0,k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f175,plain,
    ( ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_tarski(X0)))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f109,f85])).

fof(f109,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,k1_tarski(X0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f183,plain,
    ( spl3_23
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f98,f76,f72,f181])).

fof(f76,plain,
    ( spl3_6
  <=> ! [X1,X2] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f98,plain,
    ( ! [X0] : r1_tarski(k1_tarski(X0),k1_tarski(X0))
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(superposition,[],[f77,f73])).

fof(f77,plain,
    ( ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f167,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f33,f165])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK2(X0,X1,X2) = X1
      | sK2(X0,X1,X2) = X0
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f16])).

% (31482)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% (31485)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% (31485)Refutation not found, incomplete strategy% (31485)------------------------------
% (31485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31485)Termination reason: Refutation not found, incomplete strategy

% (31485)Memory used [KB]: 10618
% (31485)Time elapsed: 0.088 s
% (31485)------------------------------
% (31485)------------------------------
fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f156,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f36,f154])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f150,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f53,f148])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK2(X0,X1,X2) != X0
      | ~ r2_hidden(X0,X2) ) ),
    inference(inner_rewriting,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK2(X0,X1,X2) != X0
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f141,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f52,f139])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK2(X0,X1,X2) != X1
      | ~ r2_hidden(X1,X2) ) ),
    inference(inner_rewriting,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK2(X0,X1,X2) != X1
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f110,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f95,f72,f68,f108])).

fof(f68,plain,
    ( spl3_4
  <=> ! [X1,X2] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f95,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,k1_tarski(X0))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f69,f73])).

fof(f69,plain,
    ( ! [X2,X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f90,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f42,f88])).

fof(f42,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f86,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f41,f84])).

fof(f41,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f49,f76])).

fof(f49,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f24,f72])).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

% (31483)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
fof(f70,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f51,f68])).

fof(f51,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f10])).

fof(f10,plain,
    ( ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0))
   => k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:23:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (31440)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (31433)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (31440)Refutation not found, incomplete strategy% (31440)------------------------------
% 0.20/0.51  % (31440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31440)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (31440)Memory used [KB]: 10618
% 0.20/0.51  % (31440)Time elapsed: 0.094 s
% 0.20/0.51  % (31440)------------------------------
% 0.20/0.51  % (31440)------------------------------
% 0.20/0.52  % (31457)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (31441)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (31442)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (31448)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (31448)Refutation not found, incomplete strategy% (31448)------------------------------
% 0.20/0.52  % (31448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31430)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (31448)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (31448)Memory used [KB]: 1663
% 0.20/0.52  % (31448)Time elapsed: 0.117 s
% 0.20/0.52  % (31448)------------------------------
% 0.20/0.52  % (31448)------------------------------
% 0.20/0.53  % (31451)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (31435)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (31450)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (31459)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (31434)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (31445)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (31459)Refutation not found, incomplete strategy% (31459)------------------------------
% 0.20/0.54  % (31459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31459)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31459)Memory used [KB]: 1663
% 0.20/0.54  % (31459)Time elapsed: 0.139 s
% 0.20/0.54  % (31459)------------------------------
% 0.20/0.54  % (31459)------------------------------
% 0.20/0.54  % (31441)Refutation not found, incomplete strategy% (31441)------------------------------
% 0.20/0.54  % (31441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31441)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31441)Memory used [KB]: 6140
% 0.20/0.54  % (31441)Time elapsed: 0.137 s
% 0.20/0.54  % (31441)------------------------------
% 0.20/0.54  % (31441)------------------------------
% 0.20/0.54  % (31457)Refutation not found, incomplete strategy% (31457)------------------------------
% 0.20/0.54  % (31457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31457)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31457)Memory used [KB]: 6140
% 0.20/0.54  % (31457)Time elapsed: 0.143 s
% 0.20/0.54  % (31457)------------------------------
% 0.20/0.54  % (31457)------------------------------
% 1.36/0.54  % (31432)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.36/0.54  % (31431)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.36/0.54  % (31446)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.36/0.54  % (31458)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.36/0.54  % (31431)Refutation not found, incomplete strategy% (31431)------------------------------
% 1.36/0.54  % (31431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (31431)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (31431)Memory used [KB]: 1663
% 1.36/0.54  % (31431)Time elapsed: 0.136 s
% 1.36/0.54  % (31431)------------------------------
% 1.36/0.54  % (31431)------------------------------
% 1.36/0.54  % (31446)Refutation not found, incomplete strategy% (31446)------------------------------
% 1.36/0.54  % (31446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (31446)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (31446)Memory used [KB]: 10618
% 1.36/0.54  % (31446)Time elapsed: 0.141 s
% 1.36/0.54  % (31446)------------------------------
% 1.36/0.54  % (31446)------------------------------
% 1.36/0.54  % (31458)Refutation not found, incomplete strategy% (31458)------------------------------
% 1.36/0.54  % (31458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (31458)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (31458)Memory used [KB]: 10618
% 1.36/0.54  % (31458)Time elapsed: 0.140 s
% 1.36/0.54  % (31458)------------------------------
% 1.36/0.54  % (31458)------------------------------
% 1.36/0.55  % (31447)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.36/0.55  % (31447)Refutation not found, incomplete strategy% (31447)------------------------------
% 1.36/0.55  % (31447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (31447)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (31447)Memory used [KB]: 1663
% 1.36/0.55  % (31447)Time elapsed: 0.140 s
% 1.36/0.55  % (31447)------------------------------
% 1.36/0.55  % (31447)------------------------------
% 1.36/0.55  % (31443)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.36/0.55  % (31438)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.36/0.55  % (31456)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.36/0.55  % (31453)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.36/0.55  % (31456)Refutation not found, incomplete strategy% (31456)------------------------------
% 1.36/0.55  % (31456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (31456)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (31456)Memory used [KB]: 6140
% 1.36/0.55  % (31456)Time elapsed: 0.148 s
% 1.36/0.55  % (31456)------------------------------
% 1.36/0.55  % (31456)------------------------------
% 1.36/0.55  % (31452)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.36/0.55  % (31437)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.36/0.56  % (31444)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.36/0.56  % (31449)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.36/0.56  % (31439)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.36/0.56  % (31454)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.36/0.56  % (31455)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.59/0.56  % (31444)Refutation not found, incomplete strategy% (31444)------------------------------
% 1.59/0.56  % (31444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.56  % (31444)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.56  
% 1.59/0.56  % (31444)Memory used [KB]: 1663
% 1.59/0.56  % (31444)Time elapsed: 0.069 s
% 1.59/0.56  % (31444)------------------------------
% 1.59/0.56  % (31444)------------------------------
% 1.59/0.56  % (31455)Refutation not found, incomplete strategy% (31455)------------------------------
% 1.59/0.56  % (31455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.56  % (31455)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.56  
% 1.59/0.56  % (31455)Memory used [KB]: 6140
% 1.59/0.56  % (31455)Time elapsed: 0.158 s
% 1.59/0.56  % (31455)------------------------------
% 1.59/0.56  % (31455)------------------------------
% 1.59/0.56  % (31454)Refutation not found, incomplete strategy% (31454)------------------------------
% 1.59/0.56  % (31454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.56  % (31454)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.56  
% 1.59/0.56  % (31454)Memory used [KB]: 10618
% 1.59/0.56  % (31454)Time elapsed: 0.157 s
% 1.59/0.56  % (31454)------------------------------
% 1.59/0.56  % (31454)------------------------------
% 1.59/0.56  % (31436)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.63  % (31481)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.99/0.64  % (31433)Refutation not found, incomplete strategy% (31433)------------------------------
% 1.99/0.64  % (31433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.64  % (31433)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.64  
% 1.99/0.64  % (31433)Memory used [KB]: 6140
% 1.99/0.64  % (31433)Time elapsed: 0.234 s
% 1.99/0.64  % (31433)------------------------------
% 1.99/0.64  % (31433)------------------------------
% 1.99/0.65  % (31481)Refutation found. Thanks to Tanya!
% 1.99/0.65  % SZS status Theorem for theBenchmark
% 1.99/0.65  % SZS output start Proof for theBenchmark
% 1.99/0.65  fof(f466,plain,(
% 1.99/0.65    $false),
% 1.99/0.65    inference(avatar_sat_refutation,[],[f58,f70,f74,f78,f86,f90,f110,f141,f150,f156,f167,f183,f188,f232,f239,f261,f281,f350,f362,f452])).
% 1.99/0.65  fof(f452,plain,(
% 1.99/0.65    spl3_1 | spl3_33 | spl3_42 | ~spl3_45),
% 1.99/0.65    inference(avatar_contradiction_clause,[],[f451])).
% 1.99/0.65  fof(f451,plain,(
% 1.99/0.65    $false | (spl3_1 | spl3_33 | spl3_42 | ~spl3_45)),
% 1.99/0.65    inference(subsumption_resolution,[],[f260,f432])).
% 1.99/0.65  fof(f432,plain,(
% 1.99/0.65    k1_xboole_0 = sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) | (spl3_1 | spl3_33 | spl3_42 | ~spl3_45)),
% 1.99/0.65    inference(unit_resulting_resolution,[],[f57,f260,f349,f349,f361])).
% 1.99/0.65  fof(f361,plain,(
% 1.99/0.65    ( ! [X6,X4,X5] : (k1_tarski(X6) = sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) | k2_tarski(X4,X5) = k1_zfmisc_1(k1_tarski(X6)) | sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) = X5 | sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) = X4 | k1_xboole_0 = sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6)))) ) | ~spl3_45),
% 1.99/0.65    inference(avatar_component_clause,[],[f360])).
% 1.99/0.66  fof(f360,plain,(
% 1.99/0.66    spl3_45 <=> ! [X5,X4,X6] : (sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) = X4 | k2_tarski(X4,X5) = k1_zfmisc_1(k1_tarski(X6)) | sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) = X5 | k1_tarski(X6) = sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) | k1_xboole_0 = sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 1.99/0.66  fof(f349,plain,(
% 1.99/0.66    k1_tarski(sK0) != sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) | spl3_42),
% 1.99/0.66    inference(avatar_component_clause,[],[f347])).
% 1.99/0.66  fof(f347,plain,(
% 1.99/0.66    spl3_42 <=> k1_tarski(sK0) = sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 1.99/0.66  fof(f57,plain,(
% 1.99/0.66    k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0)) | spl3_1),
% 1.99/0.66    inference(avatar_component_clause,[],[f55])).
% 1.99/0.66  fof(f55,plain,(
% 1.99/0.66    spl3_1 <=> k1_zfmisc_1(k1_tarski(sK0)) = k2_tarski(k1_xboole_0,k1_tarski(sK0))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.99/0.66  fof(f260,plain,(
% 1.99/0.66    k1_xboole_0 != sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) | spl3_33),
% 1.99/0.66    inference(avatar_component_clause,[],[f258])).
% 1.99/0.66  fof(f258,plain,(
% 1.99/0.66    spl3_33 <=> k1_xboole_0 = sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 1.99/0.66  fof(f362,plain,(
% 1.99/0.66    spl3_45 | ~spl3_30 | ~spl3_31),
% 1.99/0.66    inference(avatar_split_clause,[],[f241,f237,f230,f360])).
% 1.99/0.66  fof(f230,plain,(
% 1.99/0.66    spl3_30 <=> ! [X1,X0] : (~r1_tarski(X1,k1_tarski(X0)) | k1_tarski(X0) = X1 | k1_xboole_0 = X1)),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.99/0.66  fof(f237,plain,(
% 1.99/0.66    spl3_31 <=> ! [X1,X0,X2] : (sK2(X0,X1,k1_zfmisc_1(X2)) = X1 | sK2(X0,X1,k1_zfmisc_1(X2)) = X0 | k2_tarski(X0,X1) = k1_zfmisc_1(X2) | r1_tarski(sK2(X0,X1,k1_zfmisc_1(X2)),X2))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.99/0.66  fof(f241,plain,(
% 1.99/0.66    ( ! [X6,X4,X5] : (sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) = X4 | k2_tarski(X4,X5) = k1_zfmisc_1(k1_tarski(X6)) | sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) = X5 | k1_tarski(X6) = sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6))) | k1_xboole_0 = sK2(X4,X5,k1_zfmisc_1(k1_tarski(X6)))) ) | (~spl3_30 | ~spl3_31)),
% 1.99/0.66    inference(resolution,[],[f238,f231])).
% 1.99/0.66  fof(f231,plain,(
% 1.99/0.66    ( ! [X0,X1] : (~r1_tarski(X1,k1_tarski(X0)) | k1_tarski(X0) = X1 | k1_xboole_0 = X1) ) | ~spl3_30),
% 1.99/0.66    inference(avatar_component_clause,[],[f230])).
% 1.99/0.66  fof(f238,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (r1_tarski(sK2(X0,X1,k1_zfmisc_1(X2)),X2) | sK2(X0,X1,k1_zfmisc_1(X2)) = X0 | k2_tarski(X0,X1) = k1_zfmisc_1(X2) | sK2(X0,X1,k1_zfmisc_1(X2)) = X1) ) | ~spl3_31),
% 1.99/0.66    inference(avatar_component_clause,[],[f237])).
% 1.99/0.66  fof(f350,plain,(
% 1.99/0.66    ~spl3_42 | spl3_1 | ~spl3_16 | ~spl3_35),
% 1.99/0.66    inference(avatar_split_clause,[],[f283,f279,f139,f55,f347])).
% 1.99/0.66  fof(f139,plain,(
% 1.99/0.66    spl3_16 <=> ! [X1,X0,X2] : (k2_tarski(X0,X1) = X2 | sK2(X0,X1,X2) != X1 | ~r2_hidden(X1,X2))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.99/0.66  fof(f279,plain,(
% 1.99/0.66    spl3_35 <=> ! [X0] : r2_hidden(k1_tarski(X0),k1_zfmisc_1(k1_tarski(X0)))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 1.99/0.66  fof(f283,plain,(
% 1.99/0.66    k1_tarski(sK0) != sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) | (spl3_1 | ~spl3_16 | ~spl3_35)),
% 1.99/0.66    inference(unit_resulting_resolution,[],[f57,f280,f140])).
% 1.99/0.66  fof(f140,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) != X1 | k2_tarski(X0,X1) = X2 | ~r2_hidden(X1,X2)) ) | ~spl3_16),
% 1.99/0.66    inference(avatar_component_clause,[],[f139])).
% 1.99/0.66  fof(f280,plain,(
% 1.99/0.66    ( ! [X0] : (r2_hidden(k1_tarski(X0),k1_zfmisc_1(k1_tarski(X0)))) ) | ~spl3_35),
% 1.99/0.66    inference(avatar_component_clause,[],[f279])).
% 1.99/0.66  fof(f281,plain,(
% 1.99/0.66    spl3_35 | ~spl3_8 | ~spl3_23),
% 1.99/0.66    inference(avatar_split_clause,[],[f184,f181,f84,f279])).
% 1.99/0.66  fof(f84,plain,(
% 1.99/0.66    spl3_8 <=> ! [X3,X0] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.99/0.66  fof(f181,plain,(
% 1.99/0.66    spl3_23 <=> ! [X0] : r1_tarski(k1_tarski(X0),k1_tarski(X0))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.99/0.66  fof(f184,plain,(
% 1.99/0.66    ( ! [X0] : (r2_hidden(k1_tarski(X0),k1_zfmisc_1(k1_tarski(X0)))) ) | (~spl3_8 | ~spl3_23)),
% 1.99/0.66    inference(unit_resulting_resolution,[],[f182,f85])).
% 1.99/0.66  fof(f85,plain,(
% 1.99/0.66    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) ) | ~spl3_8),
% 1.99/0.66    inference(avatar_component_clause,[],[f84])).
% 1.99/0.66  fof(f182,plain,(
% 1.99/0.66    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_tarski(X0))) ) | ~spl3_23),
% 1.99/0.66    inference(avatar_component_clause,[],[f181])).
% 1.99/0.66  fof(f261,plain,(
% 1.99/0.66    ~spl3_33 | spl3_1 | ~spl3_18 | ~spl3_24),
% 1.99/0.66    inference(avatar_split_clause,[],[f220,f186,f148,f55,f258])).
% 1.99/0.66  fof(f148,plain,(
% 1.99/0.66    spl3_18 <=> ! [X1,X0,X2] : (k2_tarski(X0,X1) = X2 | sK2(X0,X1,X2) != X0 | ~r2_hidden(X0,X2))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.99/0.66  fof(f186,plain,(
% 1.99/0.66    spl3_24 <=> ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_tarski(X0)))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.99/0.66  fof(f220,plain,(
% 1.99/0.66    k1_xboole_0 != sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) | (spl3_1 | ~spl3_18 | ~spl3_24)),
% 1.99/0.66    inference(unit_resulting_resolution,[],[f57,f187,f149])).
% 1.99/0.66  fof(f149,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) != X0 | k2_tarski(X0,X1) = X2 | ~r2_hidden(X0,X2)) ) | ~spl3_18),
% 1.99/0.66    inference(avatar_component_clause,[],[f148])).
% 1.99/0.66  fof(f187,plain,(
% 1.99/0.66    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_tarski(X0)))) ) | ~spl3_24),
% 1.99/0.66    inference(avatar_component_clause,[],[f186])).
% 1.99/0.66  fof(f239,plain,(
% 1.99/0.66    spl3_31 | ~spl3_9 | ~spl3_20),
% 1.99/0.66    inference(avatar_split_clause,[],[f168,f165,f88,f237])).
% 1.99/0.66  fof(f88,plain,(
% 1.99/0.66    spl3_9 <=> ! [X3,X0] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0)))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.99/0.66  fof(f165,plain,(
% 1.99/0.66    spl3_20 <=> ! [X1,X0,X2] : (k2_tarski(X0,X1) = X2 | sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.99/0.66  fof(f168,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (sK2(X0,X1,k1_zfmisc_1(X2)) = X1 | sK2(X0,X1,k1_zfmisc_1(X2)) = X0 | k2_tarski(X0,X1) = k1_zfmisc_1(X2) | r1_tarski(sK2(X0,X1,k1_zfmisc_1(X2)),X2)) ) | (~spl3_9 | ~spl3_20)),
% 1.99/0.66    inference(resolution,[],[f166,f89])).
% 1.99/0.66  fof(f89,plain,(
% 1.99/0.66    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) ) | ~spl3_9),
% 1.99/0.66    inference(avatar_component_clause,[],[f88])).
% 1.99/0.66  fof(f166,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | k2_tarski(X0,X1) = X2) ) | ~spl3_20),
% 1.99/0.66    inference(avatar_component_clause,[],[f165])).
% 1.99/0.66  fof(f232,plain,(
% 1.99/0.66    spl3_30 | ~spl3_5 | ~spl3_19),
% 1.99/0.66    inference(avatar_split_clause,[],[f163,f154,f72,f230])).
% 1.99/0.66  fof(f72,plain,(
% 1.99/0.66    spl3_5 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.99/0.66  fof(f154,plain,(
% 1.99/0.66    spl3_19 <=> ! [X1,X0,X2] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2)))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.99/0.66  fof(f163,plain,(
% 1.99/0.66    ( ! [X0,X1] : (~r1_tarski(X1,k1_tarski(X0)) | k1_tarski(X0) = X1 | k1_xboole_0 = X1) ) | (~spl3_5 | ~spl3_19)),
% 1.99/0.66    inference(duplicate_literal_removal,[],[f162])).
% 1.99/0.66  fof(f162,plain,(
% 1.99/0.66    ( ! [X0,X1] : (~r1_tarski(X1,k1_tarski(X0)) | k1_tarski(X0) = X1 | k1_tarski(X0) = X1 | k1_xboole_0 = X1 | k1_tarski(X0) = X1) ) | (~spl3_5 | ~spl3_19)),
% 1.99/0.66    inference(superposition,[],[f155,f73])).
% 1.99/0.66  fof(f73,plain,(
% 1.99/0.66    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl3_5),
% 1.99/0.66    inference(avatar_component_clause,[],[f72])).
% 1.99/0.66  fof(f155,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k2_tarski(X1,X2) = X0) ) | ~spl3_19),
% 1.99/0.66    inference(avatar_component_clause,[],[f154])).
% 1.99/0.66  fof(f188,plain,(
% 1.99/0.66    spl3_24 | ~spl3_8 | ~spl3_12),
% 1.99/0.66    inference(avatar_split_clause,[],[f175,f108,f84,f186])).
% 1.99/0.66  fof(f108,plain,(
% 1.99/0.66    spl3_12 <=> ! [X0] : r1_tarski(k1_xboole_0,k1_tarski(X0))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.99/0.66  fof(f175,plain,(
% 1.99/0.66    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_tarski(X0)))) ) | (~spl3_8 | ~spl3_12)),
% 1.99/0.66    inference(unit_resulting_resolution,[],[f109,f85])).
% 1.99/0.66  fof(f109,plain,(
% 1.99/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,k1_tarski(X0))) ) | ~spl3_12),
% 1.99/0.66    inference(avatar_component_clause,[],[f108])).
% 1.99/0.66  fof(f183,plain,(
% 1.99/0.66    spl3_23 | ~spl3_5 | ~spl3_6),
% 1.99/0.66    inference(avatar_split_clause,[],[f98,f76,f72,f181])).
% 1.99/0.66  fof(f76,plain,(
% 1.99/0.66    spl3_6 <=> ! [X1,X2] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.99/0.66  fof(f98,plain,(
% 1.99/0.66    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_tarski(X0))) ) | (~spl3_5 | ~spl3_6)),
% 1.99/0.66    inference(superposition,[],[f77,f73])).
% 1.99/0.66  fof(f77,plain,(
% 1.99/0.66    ( ! [X2,X1] : (r1_tarski(k1_tarski(X2),k2_tarski(X1,X2))) ) | ~spl3_6),
% 1.99/0.66    inference(avatar_component_clause,[],[f76])).
% 1.99/0.66  fof(f167,plain,(
% 1.99/0.66    spl3_20),
% 1.99/0.66    inference(avatar_split_clause,[],[f33,f165])).
% 1.99/0.66  fof(f33,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f20])).
% 1.99/0.66  fof(f20,plain,(
% 1.99/0.66    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.99/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 1.99/0.66  fof(f19,plain,(
% 1.99/0.66    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.99/0.66    introduced(choice_axiom,[])).
% 1.99/0.66  fof(f18,plain,(
% 1.99/0.66    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.99/0.66    inference(rectify,[],[f17])).
% 1.99/0.66  fof(f17,plain,(
% 1.99/0.66    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.99/0.66    inference(flattening,[],[f16])).
% 1.99/0.66  % (31482)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.99/0.66  % (31485)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 1.99/0.66  % (31485)Refutation not found, incomplete strategy% (31485)------------------------------
% 1.99/0.66  % (31485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.66  % (31485)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.66  
% 1.99/0.66  % (31485)Memory used [KB]: 10618
% 1.99/0.66  % (31485)Time elapsed: 0.088 s
% 1.99/0.66  % (31485)------------------------------
% 1.99/0.66  % (31485)------------------------------
% 1.99/0.66  fof(f16,plain,(
% 1.99/0.66    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.99/0.66    inference(nnf_transformation,[],[f1])).
% 1.99/0.66  fof(f1,axiom,(
% 1.99/0.66    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.99/0.66  fof(f156,plain,(
% 1.99/0.66    spl3_19),
% 1.99/0.66    inference(avatar_split_clause,[],[f36,f154])).
% 1.99/0.66  fof(f36,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f22])).
% 1.99/0.66  fof(f22,plain,(
% 1.99/0.66    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.99/0.66    inference(flattening,[],[f21])).
% 1.99/0.66  fof(f21,plain,(
% 1.99/0.66    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.99/0.66    inference(nnf_transformation,[],[f9])).
% 1.99/0.66  fof(f9,plain,(
% 1.99/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.99/0.66    inference(ennf_transformation,[],[f5])).
% 1.99/0.66  fof(f5,axiom,(
% 1.99/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.99/0.66  fof(f150,plain,(
% 1.99/0.66    spl3_18),
% 1.99/0.66    inference(avatar_split_clause,[],[f53,f148])).
% 1.99/0.66  fof(f53,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK2(X0,X1,X2) != X0 | ~r2_hidden(X0,X2)) )),
% 1.99/0.66    inference(inner_rewriting,[],[f34])).
% 1.99/0.66  fof(f34,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK2(X0,X1,X2) != X0 | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f20])).
% 1.99/0.66  fof(f141,plain,(
% 1.99/0.66    spl3_16),
% 1.99/0.66    inference(avatar_split_clause,[],[f52,f139])).
% 1.99/0.66  fof(f52,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK2(X0,X1,X2) != X1 | ~r2_hidden(X1,X2)) )),
% 1.99/0.66    inference(inner_rewriting,[],[f35])).
% 1.99/0.66  fof(f35,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK2(X0,X1,X2) != X1 | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f20])).
% 1.99/0.66  fof(f110,plain,(
% 1.99/0.66    spl3_12 | ~spl3_4 | ~spl3_5),
% 1.99/0.66    inference(avatar_split_clause,[],[f95,f72,f68,f108])).
% 1.99/0.66  fof(f68,plain,(
% 1.99/0.66    spl3_4 <=> ! [X1,X2] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.99/0.66  fof(f95,plain,(
% 1.99/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,k1_tarski(X0))) ) | (~spl3_4 | ~spl3_5)),
% 1.99/0.66    inference(superposition,[],[f69,f73])).
% 1.99/0.66  fof(f69,plain,(
% 1.99/0.66    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X2))) ) | ~spl3_4),
% 1.99/0.66    inference(avatar_component_clause,[],[f68])).
% 1.99/0.66  fof(f90,plain,(
% 1.99/0.66    spl3_9),
% 1.99/0.66    inference(avatar_split_clause,[],[f42,f88])).
% 1.99/0.66  fof(f42,plain,(
% 1.99/0.66    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.99/0.66    inference(equality_resolution,[],[f26])).
% 1.99/0.66  fof(f26,plain,(
% 1.99/0.66    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.99/0.66    inference(cnf_transformation,[],[f15])).
% 1.99/0.66  fof(f15,plain,(
% 1.99/0.66    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.99/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).
% 1.99/0.66  fof(f14,plain,(
% 1.99/0.66    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 1.99/0.66    introduced(choice_axiom,[])).
% 1.99/0.66  fof(f13,plain,(
% 1.99/0.66    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.99/0.66    inference(rectify,[],[f12])).
% 1.99/0.66  fof(f12,plain,(
% 1.99/0.66    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.99/0.66    inference(nnf_transformation,[],[f4])).
% 1.99/0.66  fof(f4,axiom,(
% 1.99/0.66    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.99/0.66  fof(f86,plain,(
% 1.99/0.66    spl3_8),
% 1.99/0.66    inference(avatar_split_clause,[],[f41,f84])).
% 1.99/0.66  fof(f41,plain,(
% 1.99/0.66    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.99/0.66    inference(equality_resolution,[],[f27])).
% 1.99/0.66  fof(f27,plain,(
% 1.99/0.66    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.99/0.66    inference(cnf_transformation,[],[f15])).
% 1.99/0.66  fof(f78,plain,(
% 1.99/0.66    spl3_6),
% 1.99/0.66    inference(avatar_split_clause,[],[f49,f76])).
% 1.99/0.66  fof(f49,plain,(
% 1.99/0.66    ( ! [X2,X1] : (r1_tarski(k1_tarski(X2),k2_tarski(X1,X2))) )),
% 1.99/0.66    inference(equality_resolution,[],[f39])).
% 1.99/0.66  fof(f39,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 1.99/0.66    inference(cnf_transformation,[],[f22])).
% 1.99/0.66  fof(f74,plain,(
% 1.99/0.66    spl3_5),
% 1.99/0.66    inference(avatar_split_clause,[],[f24,f72])).
% 1.99/0.66  fof(f24,plain,(
% 1.99/0.66    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f2])).
% 1.99/0.66  fof(f2,axiom,(
% 1.99/0.66    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.99/0.67  % (31483)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.99/0.67  fof(f70,plain,(
% 1.99/0.67    spl3_4),
% 1.99/0.67    inference(avatar_split_clause,[],[f51,f68])).
% 1.99/0.67  fof(f51,plain,(
% 1.99/0.67    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X2))) )),
% 1.99/0.67    inference(equality_resolution,[],[f37])).
% 1.99/0.67  fof(f37,plain,(
% 1.99/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 1.99/0.67    inference(cnf_transformation,[],[f22])).
% 1.99/0.67  fof(f58,plain,(
% 1.99/0.67    ~spl3_1),
% 1.99/0.67    inference(avatar_split_clause,[],[f23,f55])).
% 1.99/0.67  fof(f23,plain,(
% 1.99/0.67    k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0))),
% 1.99/0.67    inference(cnf_transformation,[],[f11])).
% 1.99/0.67  fof(f11,plain,(
% 1.99/0.67    k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0))),
% 1.99/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f10])).
% 1.99/0.67  fof(f10,plain,(
% 1.99/0.67    ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0)) => k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0))),
% 1.99/0.67    introduced(choice_axiom,[])).
% 1.99/0.67  fof(f8,plain,(
% 1.99/0.67    ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0))),
% 1.99/0.67    inference(ennf_transformation,[],[f7])).
% 1.99/0.67  fof(f7,negated_conjecture,(
% 1.99/0.67    ~! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0))),
% 1.99/0.67    inference(negated_conjecture,[],[f6])).
% 1.99/0.67  fof(f6,conjecture,(
% 1.99/0.67    ! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0))),
% 1.99/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_zfmisc_1)).
% 1.99/0.67  % SZS output end Proof for theBenchmark
% 1.99/0.67  % (31481)------------------------------
% 1.99/0.67  % (31481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.67  % (31481)Termination reason: Refutation
% 1.99/0.67  
% 1.99/0.67  % (31481)Memory used [KB]: 6524
% 1.99/0.67  % (31481)Time elapsed: 0.109 s
% 1.99/0.67  % (31481)------------------------------
% 1.99/0.67  % (31481)------------------------------
% 1.99/0.67  % (31486)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 1.99/0.67  % (31429)Success in time 0.302 s
%------------------------------------------------------------------------------
