%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0647+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:22 EST 2020

% Result     : Theorem 1.99s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 619 expanded)
%              Number of leaves         :   47 ( 285 expanded)
%              Depth                    :   11
%              Number of atoms          : 1014 (5439 expanded)
%              Number of equality atoms :  268 (2143 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2785,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f117,f120,f122,f124,f129,f137,f141,f143,f147,f151,f155,f159,f163,f177,f182,f210,f214,f291,f320,f378,f382,f449,f494,f509,f517,f522,f530,f550,f1775,f2159,f2166,f2168,f2173,f2182,f2183,f2192,f2213,f2228,f2593,f2646,f2784])).

fof(f2784,plain,
    ( ~ spl12_15
    | spl12_2
    | ~ spl12_17 ),
    inference(avatar_split_clause,[],[f2781,f180,f100,f161])).

fof(f161,plain,
    ( spl12_15
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f100,plain,
    ( spl12_2
  <=> k2_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f180,plain,
    ( spl12_17
  <=> sK1 = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).

fof(f2781,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl12_17 ),
    inference(superposition,[],[f63,f292])).

fof(f292,plain,
    ( sK1 = k4_relat_1(sK0)
    | ~ spl12_17 ),
    inference(avatar_component_clause,[],[f180])).

fof(f63,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f2646,plain,
    ( ~ spl12_270
    | spl12_268
    | ~ spl12_2
    | ~ spl12_10
    | ~ spl12_271 ),
    inference(avatar_split_clause,[],[f2587,f2180,f139,f100,f2161,f2171])).

fof(f2171,plain,
    ( spl12_270
  <=> r2_hidden(sK4(sK0,sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_270])])).

fof(f2161,plain,
    ( spl12_268
  <=> r2_hidden(sK5(sK0,sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_268])])).

fof(f139,plain,
    ( spl12_10
  <=> ! [X4] :
        ( r2_hidden(k1_funct_1(sK1,X4),k1_relat_1(sK0))
        | ~ r2_hidden(X4,k2_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f2180,plain,
    ( spl12_271
  <=> sK5(sK0,sK1) = k1_funct_1(sK1,sK4(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_271])])).

fof(f2587,plain,
    ( r2_hidden(sK5(sK0,sK1),k1_relat_1(sK0))
    | ~ r2_hidden(sK4(sK0,sK1),k1_relat_1(sK1))
    | ~ spl12_2
    | ~ spl12_10
    | ~ spl12_271 ),
    inference(superposition,[],[f571,f2181])).

fof(f2181,plain,
    ( sK5(sK0,sK1) = k1_funct_1(sK1,sK4(sK0,sK1))
    | ~ spl12_271 ),
    inference(avatar_component_clause,[],[f2180])).

fof(f571,plain,
    ( ! [X4] :
        ( r2_hidden(k1_funct_1(sK1,X4),k1_relat_1(sK0))
        | ~ r2_hidden(X4,k1_relat_1(sK1)) )
    | ~ spl12_2
    | ~ spl12_10 ),
    inference(forward_demodulation,[],[f140,f142])).

fof(f142,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f140,plain,
    ( ! [X4] :
        ( r2_hidden(k1_funct_1(sK1,X4),k1_relat_1(sK0))
        | ~ r2_hidden(X4,k2_relat_1(sK0)) )
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f139])).

fof(f2593,plain,
    ( ~ spl12_270
    | spl12_269
    | ~ spl12_2
    | ~ spl12_9
    | ~ spl12_271 ),
    inference(avatar_split_clause,[],[f2586,f2180,f135,f100,f2164,f2171])).

fof(f2164,plain,
    ( spl12_269
  <=> sK4(sK0,sK1) = k1_funct_1(sK0,sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_269])])).

fof(f135,plain,
    ( spl12_9
  <=> ! [X4] :
        ( k1_funct_1(sK0,k1_funct_1(sK1,X4)) = X4
        | ~ r2_hidden(X4,k2_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f2586,plain,
    ( sK4(sK0,sK1) = k1_funct_1(sK0,sK5(sK0,sK1))
    | ~ r2_hidden(sK4(sK0,sK1),k1_relat_1(sK1))
    | ~ spl12_2
    | ~ spl12_9
    | ~ spl12_271 ),
    inference(superposition,[],[f572,f2181])).

fof(f572,plain,
    ( ! [X4] :
        ( k1_funct_1(sK0,k1_funct_1(sK1,X4)) = X4
        | ~ r2_hidden(X4,k1_relat_1(sK1)) )
    | ~ spl12_2
    | ~ spl12_9 ),
    inference(forward_demodulation,[],[f136,f142])).

fof(f136,plain,
    ( ! [X4] :
        ( k1_funct_1(sK0,k1_funct_1(sK1,X4)) = X4
        | ~ r2_hidden(X4,k2_relat_1(sK0)) )
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f135])).

fof(f2228,plain,
    ( spl12_205
    | ~ spl12_21
    | ~ spl12_268
    | ~ spl12_269 ),
    inference(avatar_split_clause,[],[f2197,f2164,f2161,f212,f1770])).

fof(f1770,plain,
    ( spl12_205
  <=> r2_hidden(k4_tarski(sK5(sK0,sK1),sK4(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_205])])).

fof(f212,plain,
    ( spl12_21
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK0))
        | r2_hidden(k4_tarski(X1,k1_funct_1(sK0,X1)),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).

fof(f2197,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK1),sK4(sK0,sK1)),sK0)
    | ~ spl12_21
    | ~ spl12_268
    | ~ spl12_269 ),
    inference(forward_demodulation,[],[f2189,f2165])).

fof(f2165,plain,
    ( sK4(sK0,sK1) = k1_funct_1(sK0,sK5(sK0,sK1))
    | ~ spl12_269 ),
    inference(avatar_component_clause,[],[f2164])).

fof(f2189,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK1),k1_funct_1(sK0,sK5(sK0,sK1))),sK0)
    | ~ spl12_21
    | ~ spl12_268 ),
    inference(resolution,[],[f2167,f213])).

fof(f213,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK0))
        | r2_hidden(k4_tarski(X1,k1_funct_1(sK0,X1)),sK0) )
    | ~ spl12_21 ),
    inference(avatar_component_clause,[],[f212])).

fof(f2167,plain,
    ( r2_hidden(sK5(sK0,sK1),k1_relat_1(sK0))
    | ~ spl12_268 ),
    inference(avatar_component_clause,[],[f2161])).

fof(f2213,plain,
    ( spl12_206
    | ~ spl12_20
    | ~ spl12_270
    | ~ spl12_271 ),
    inference(avatar_split_clause,[],[f2212,f2180,f2171,f208,f1773])).

fof(f1773,plain,
    ( spl12_206
  <=> r2_hidden(k4_tarski(sK4(sK0,sK1),sK5(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_206])])).

fof(f208,plain,
    ( spl12_20
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f2212,plain,
    ( r2_hidden(k4_tarski(sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ spl12_20
    | ~ spl12_270
    | ~ spl12_271 ),
    inference(forward_demodulation,[],[f2203,f2181])).

fof(f2203,plain,
    ( r2_hidden(k4_tarski(sK4(sK0,sK1),k1_funct_1(sK1,sK4(sK0,sK1))),sK1)
    | ~ spl12_20
    | ~ spl12_270 ),
    inference(resolution,[],[f2172,f209])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) )
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f208])).

fof(f2172,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_relat_1(sK1))
    | ~ spl12_270 ),
    inference(avatar_component_clause,[],[f2171])).

fof(f2192,plain,
    ( spl12_271
    | ~ spl12_7
    | ~ spl12_268
    | ~ spl12_269 ),
    inference(avatar_split_clause,[],[f2191,f2164,f2161,f127,f2180])).

fof(f127,plain,
    ( spl12_7
  <=> ! [X5] :
        ( k1_funct_1(sK1,k1_funct_1(sK0,X5)) = X5
        | ~ r2_hidden(X5,k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f2191,plain,
    ( sK5(sK0,sK1) = k1_funct_1(sK1,sK4(sK0,sK1))
    | ~ spl12_7
    | ~ spl12_268
    | ~ spl12_269 ),
    inference(forward_demodulation,[],[f2187,f2165])).

fof(f2187,plain,
    ( sK5(sK0,sK1) = k1_funct_1(sK1,k1_funct_1(sK0,sK5(sK0,sK1)))
    | ~ spl12_7
    | ~ spl12_268 ),
    inference(resolution,[],[f2167,f128])).

fof(f128,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relat_1(sK0))
        | k1_funct_1(sK1,k1_funct_1(sK0,X5)) = X5 )
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f2183,plain,
    ( spl12_270
    | ~ spl12_206 ),
    inference(avatar_split_clause,[],[f2176,f1773,f2171])).

fof(f2176,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_relat_1(sK1))
    | ~ spl12_206 ),
    inference(resolution,[],[f1774,f93])).

fof(f93,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK9(X0,X1),X3),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f38,f41,f40,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK9(X0,X1),X3),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK9(X0,X1),X4),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK9(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f1774,plain,
    ( r2_hidden(k4_tarski(sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ spl12_206 ),
    inference(avatar_component_clause,[],[f1773])).

fof(f2182,plain,
    ( ~ spl12_12
    | ~ spl12_11
    | ~ spl12_270
    | spl12_271
    | ~ spl12_206 ),
    inference(avatar_split_clause,[],[f2174,f1773,f2180,f2171,f145,f149])).

fof(f149,plain,
    ( spl12_12
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f145,plain,
    ( spl12_11
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f2174,plain,
    ( sK5(sK0,sK1) = k1_funct_1(sK1,sK4(sK0,sK1))
    | ~ r2_hidden(sK4(sK0,sK1),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl12_206 ),
    inference(resolution,[],[f1774,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f2173,plain,
    ( spl12_270
    | ~ spl12_2
    | ~ spl12_205 ),
    inference(avatar_split_clause,[],[f2169,f1770,f100,f2171])).

fof(f2169,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_relat_1(sK1))
    | ~ spl12_2
    | ~ spl12_205 ),
    inference(forward_demodulation,[],[f2157,f142])).

fof(f2157,plain,
    ( r2_hidden(sK4(sK0,sK1),k2_relat_1(sK0))
    | ~ spl12_205 ),
    inference(resolution,[],[f1771,f91])).

fof(f91,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f32,f35,f34,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f1771,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK1),sK4(sK0,sK1)),sK0)
    | ~ spl12_205 ),
    inference(avatar_component_clause,[],[f1770])).

fof(f2168,plain,
    ( spl12_268
    | ~ spl12_205 ),
    inference(avatar_split_clause,[],[f2156,f1770,f2161])).

fof(f2156,plain,
    ( r2_hidden(sK5(sK0,sK1),k1_relat_1(sK0))
    | ~ spl12_205 ),
    inference(resolution,[],[f1771,f93])).

fof(f2166,plain,
    ( ~ spl12_15
    | ~ spl12_14
    | ~ spl12_268
    | spl12_269
    | ~ spl12_205 ),
    inference(avatar_split_clause,[],[f2154,f1770,f2164,f2161,f157,f161])).

fof(f157,plain,
    ( spl12_14
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f2154,plain,
    ( sK4(sK0,sK1) = k1_funct_1(sK0,sK5(sK0,sK1))
    | ~ r2_hidden(sK5(sK0,sK1),k1_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl12_205 ),
    inference(resolution,[],[f1771,f71])).

fof(f2159,plain,
    ( ~ spl12_15
    | ~ spl12_12
    | ~ spl12_206
    | spl12_17
    | ~ spl12_205 ),
    inference(avatar_split_clause,[],[f2153,f1770,f180,f1773,f149,f161])).

fof(f2153,plain,
    ( sK1 = k4_relat_1(sK0)
    | ~ r2_hidden(k4_tarski(sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl12_205 ),
    inference(resolution,[],[f1771,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
      | k4_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

fof(f1775,plain,
    ( spl12_205
    | spl12_17
    | spl12_206
    | ~ spl12_12
    | ~ spl12_15 ),
    inference(avatar_split_clause,[],[f1758,f161,f149,f1773,f180,f1770])).

fof(f1758,plain,
    ( r2_hidden(k4_tarski(sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | sK1 = k4_relat_1(sK0)
    | r2_hidden(k4_tarski(sK5(sK0,sK1),sK4(sK0,sK1)),sK0)
    | ~ spl12_12
    | ~ spl12_15 ),
    inference(resolution,[],[f1198,f162])).

fof(f162,plain,
    ( v1_relat_1(sK0)
    | ~ spl12_15 ),
    inference(avatar_component_clause,[],[f161])).

fof(f1198,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK4(X0,sK1),sK5(X0,sK1)),sK1)
        | k4_relat_1(X0) = sK1
        | r2_hidden(k4_tarski(sK5(X0,sK1),sK4(X0,sK1)),X0) )
    | ~ spl12_12 ),
    inference(resolution,[],[f67,f150])).

fof(f150,plain,
    ( v1_relat_1(sK1)
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f149])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | k4_relat_1(X0) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f550,plain,
    ( ~ spl12_15
    | ~ spl12_14
    | ~ spl12_3
    | spl12_4
    | ~ spl12_36 ),
    inference(avatar_split_clause,[],[f546,f350,f106,f103,f157,f161])).

fof(f103,plain,
    ( spl12_3
  <=> r2_hidden(sK3,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f106,plain,
    ( spl12_4
  <=> sK2 = k1_funct_1(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f350,plain,
    ( spl12_36
  <=> r2_hidden(k4_tarski(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_36])])).

fof(f546,plain,
    ( sK2 = k1_funct_1(sK0,sK3)
    | ~ r2_hidden(sK3,k1_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl12_36 ),
    inference(resolution,[],[f351,f71])).

fof(f351,plain,
    ( r2_hidden(k4_tarski(sK3,sK2),sK0)
    | ~ spl12_36 ),
    inference(avatar_component_clause,[],[f350])).

fof(f530,plain,
    ( ~ spl12_12
    | spl12_36
    | ~ spl12_15
    | ~ spl12_31
    | ~ spl12_39 ),
    inference(avatar_split_clause,[],[f529,f380,f318,f161,f350,f149])).

fof(f318,plain,
    ( spl12_31
  <=> r2_hidden(k4_tarski(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).

fof(f380,plain,
    ( spl12_39
  <=> sK0 = k4_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_39])])).

fof(f529,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(k4_tarski(sK3,sK2),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl12_31
    | ~ spl12_39 ),
    inference(forward_demodulation,[],[f518,f381])).

fof(f381,plain,
    ( sK0 = k4_relat_1(sK1)
    | ~ spl12_39 ),
    inference(avatar_component_clause,[],[f380])).

fof(f518,plain,
    ( r2_hidden(k4_tarski(sK3,sK2),sK0)
    | ~ v1_relat_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl12_31
    | ~ spl12_39 ),
    inference(forward_demodulation,[],[f513,f381])).

fof(f513,plain,
    ( r2_hidden(k4_tarski(sK3,sK2),k4_relat_1(sK1))
    | ~ v1_relat_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl12_31 ),
    inference(resolution,[],[f319,f86])).

fof(f86,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X4),X0)
      | r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f319,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),sK1)
    | ~ spl12_31 ),
    inference(avatar_component_clause,[],[f318])).

fof(f522,plain,
    ( spl12_5
    | ~ spl12_2
    | ~ spl12_36 ),
    inference(avatar_split_clause,[],[f510,f350,f100,f109])).

fof(f109,plain,
    ( spl12_5
  <=> r2_hidden(sK2,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f510,plain,
    ( r2_hidden(sK2,k1_relat_1(sK1))
    | ~ spl12_2
    | ~ spl12_36 ),
    inference(forward_demodulation,[],[f506,f142])).

fof(f506,plain,
    ( r2_hidden(sK2,k2_relat_1(sK0))
    | ~ spl12_36 ),
    inference(resolution,[],[f351,f91])).

fof(f517,plain,
    ( ~ spl12_12
    | ~ spl12_11
    | ~ spl12_5
    | spl12_6
    | ~ spl12_31 ),
    inference(avatar_split_clause,[],[f512,f318,f112,f109,f145,f149])).

fof(f112,plain,
    ( spl12_6
  <=> sK3 = k1_funct_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f512,plain,
    ( sK3 = k1_funct_1(sK1,sK2)
    | ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl12_31 ),
    inference(resolution,[],[f319,f71])).

fof(f509,plain,
    ( ~ spl12_15
    | spl12_31
    | ~ spl12_12
    | ~ spl12_17
    | ~ spl12_36 ),
    inference(avatar_split_clause,[],[f508,f350,f180,f149,f318,f161])).

fof(f508,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK2,sK3),sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl12_17
    | ~ spl12_36 ),
    inference(forward_demodulation,[],[f507,f292])).

fof(f507,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),sK1)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl12_17
    | ~ spl12_36 ),
    inference(forward_demodulation,[],[f504,f292])).

fof(f504,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl12_36 ),
    inference(resolution,[],[f351,f86])).

fof(f494,plain,
    ( spl12_36
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_21 ),
    inference(avatar_split_clause,[],[f348,f212,f106,f103,f350])).

fof(f348,plain,
    ( r2_hidden(k4_tarski(sK3,sK2),sK0)
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_21 ),
    inference(forward_demodulation,[],[f343,f116])).

fof(f116,plain,
    ( sK2 = k1_funct_1(sK0,sK3)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f343,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK0,sK3)),sK0)
    | ~ spl12_3
    | ~ spl12_21 ),
    inference(resolution,[],[f121,f213])).

fof(f121,plain,
    ( r2_hidden(sK3,k1_relat_1(sK0))
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f449,plain,
    ( spl12_3
    | ~ spl12_31
    | ~ spl12_38 ),
    inference(avatar_split_clause,[],[f448,f376,f318,f103])).

fof(f376,plain,
    ( spl12_38
  <=> k1_relat_1(sK0) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_38])])).

fof(f448,plain,
    ( r2_hidden(sK3,k1_relat_1(sK0))
    | ~ spl12_31
    | ~ spl12_38 ),
    inference(forward_demodulation,[],[f439,f377])).

fof(f377,plain,
    ( k1_relat_1(sK0) = k2_relat_1(sK1)
    | ~ spl12_38 ),
    inference(avatar_component_clause,[],[f376])).

fof(f439,plain,
    ( r2_hidden(sK3,k2_relat_1(sK1))
    | ~ spl12_31 ),
    inference(resolution,[],[f319,f91])).

fof(f382,plain,
    ( ~ spl12_15
    | spl12_39
    | ~ spl12_17 ),
    inference(avatar_split_clause,[],[f370,f180,f380,f161])).

fof(f370,plain,
    ( sK0 = k4_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl12_17 ),
    inference(superposition,[],[f62,f292])).

fof(f62,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f378,plain,
    ( ~ spl12_15
    | spl12_38
    | ~ spl12_17 ),
    inference(avatar_split_clause,[],[f368,f180,f376,f161])).

fof(f368,plain,
    ( k1_relat_1(sK0) = k2_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl12_17 ),
    inference(superposition,[],[f64,f292])).

fof(f64,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f320,plain,
    ( spl12_31
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_20 ),
    inference(avatar_split_clause,[],[f316,f208,f112,f109,f318])).

fof(f316,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),sK1)
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_20 ),
    inference(forward_demodulation,[],[f296,f115])).

fof(f115,plain,
    ( sK3 = k1_funct_1(sK1,sK2)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f296,plain,
    ( r2_hidden(k4_tarski(sK2,k1_funct_1(sK1,sK2)),sK1)
    | ~ spl12_5
    | ~ spl12_20 ),
    inference(resolution,[],[f119,f209])).

fof(f119,plain,
    ( r2_hidden(sK2,k1_relat_1(sK1))
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f291,plain,
    ( k2_funct_1(sK0) != k4_relat_1(sK0)
    | k2_funct_1(sK0) != sK1
    | sK1 = k4_relat_1(sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f214,plain,
    ( ~ spl12_15
    | spl12_21
    | ~ spl12_14 ),
    inference(avatar_split_clause,[],[f206,f157,f212,f161])).

fof(f206,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK0))
        | r2_hidden(k4_tarski(X1,k1_funct_1(sK0,X1)),sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl12_14 ),
    inference(resolution,[],[f90,f158])).

fof(f158,plain,
    ( v1_funct_1(sK0)
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f157])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f210,plain,
    ( ~ spl12_12
    | spl12_20
    | ~ spl12_11 ),
    inference(avatar_split_clause,[],[f205,f145,f208,f149])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl12_11 ),
    inference(resolution,[],[f90,f146])).

fof(f146,plain,
    ( v1_funct_1(sK1)
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f145])).

fof(f182,plain,
    ( ~ spl12_17
    | spl12_1
    | ~ spl12_16 ),
    inference(avatar_split_clause,[],[f178,f175,f97,f180])).

fof(f97,plain,
    ( spl12_1
  <=> k2_funct_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f175,plain,
    ( spl12_16
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f178,plain,
    ( sK1 != k4_relat_1(sK0)
    | spl12_1
    | ~ spl12_16 ),
    inference(superposition,[],[f98,f176])).

fof(f176,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f175])).

fof(f98,plain,
    ( k2_funct_1(sK0) != sK1
    | spl12_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f177,plain,
    ( ~ spl12_15
    | ~ spl12_14
    | spl12_16
    | ~ spl12_13 ),
    inference(avatar_split_clause,[],[f171,f153,f175,f157,f161])).

fof(f153,plain,
    ( spl12_13
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f171,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl12_13 ),
    inference(resolution,[],[f69,f154])).

fof(f154,plain,
    ( v2_funct_1(sK0)
    | ~ spl12_13 ),
    inference(avatar_component_clause,[],[f153])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f163,plain,(
    spl12_15 ),
    inference(avatar_split_clause,[],[f43,f161])).

fof(f43,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ( ( sK3 != k1_funct_1(sK1,sK2)
          | ~ r2_hidden(sK2,k2_relat_1(sK0)) )
        & sK2 = k1_funct_1(sK0,sK3)
        & r2_hidden(sK3,k1_relat_1(sK0)) )
      | ( ( sK2 != k1_funct_1(sK0,sK3)
          | ~ r2_hidden(sK3,k1_relat_1(sK0)) )
        & sK3 = k1_funct_1(sK1,sK2)
        & r2_hidden(sK2,k2_relat_1(sK0)) )
      | k2_relat_1(sK0) != k1_relat_1(sK1)
      | k2_funct_1(sK0) != sK1 )
    & ( ( ! [X4,X5] :
            ( ( ( k1_funct_1(sK1,X4) = X5
                & r2_hidden(X4,k2_relat_1(sK0)) )
              | k1_funct_1(sK0,X5) != X4
              | ~ r2_hidden(X5,k1_relat_1(sK0)) )
            & ( ( k1_funct_1(sK0,X5) = X4
                & r2_hidden(X5,k1_relat_1(sK0)) )
              | k1_funct_1(sK1,X4) != X5
              | ~ r2_hidden(X4,k2_relat_1(sK0)) ) )
        & k2_relat_1(sK0) = k1_relat_1(sK1) )
      | k2_funct_1(sK0) = sK1 )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k2_relat_1(X0) != k1_relat_1(X1)
              | k2_funct_1(X0) != X1 )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) )
              | k2_funct_1(X0) = X1 )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ( ? [X3,X2] :
                ( ( ( k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(sK0)) )
                  & k1_funct_1(sK0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(sK0)) )
                | ( ( k1_funct_1(sK0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(sK0)) )
                  & k1_funct_1(X1,X2) = X3
                  & r2_hidden(X2,k2_relat_1(sK0)) ) )
            | k1_relat_1(X1) != k2_relat_1(sK0)
            | k2_funct_1(sK0) != X1 )
          & ( ( ! [X5,X4] :
                  ( ( ( k1_funct_1(X1,X4) = X5
                      & r2_hidden(X4,k2_relat_1(sK0)) )
                    | k1_funct_1(sK0,X5) != X4
                    | ~ r2_hidden(X5,k1_relat_1(sK0)) )
                  & ( ( k1_funct_1(sK0,X5) = X4
                      & r2_hidden(X5,k1_relat_1(sK0)) )
                    | k1_funct_1(X1,X4) != X5
                    | ~ r2_hidden(X4,k2_relat_1(sK0)) ) )
              & k1_relat_1(X1) = k2_relat_1(sK0) )
            | k2_funct_1(sK0) = X1 )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ( ? [X3,X2] :
              ( ( ( k1_funct_1(X1,X2) != X3
                  | ~ r2_hidden(X2,k2_relat_1(sK0)) )
                & k1_funct_1(sK0,X3) = X2
                & r2_hidden(X3,k1_relat_1(sK0)) )
              | ( ( k1_funct_1(sK0,X3) != X2
                  | ~ r2_hidden(X3,k1_relat_1(sK0)) )
                & k1_funct_1(X1,X2) = X3
                & r2_hidden(X2,k2_relat_1(sK0)) ) )
          | k1_relat_1(X1) != k2_relat_1(sK0)
          | k2_funct_1(sK0) != X1 )
        & ( ( ! [X5,X4] :
                ( ( ( k1_funct_1(X1,X4) = X5
                    & r2_hidden(X4,k2_relat_1(sK0)) )
                  | k1_funct_1(sK0,X5) != X4
                  | ~ r2_hidden(X5,k1_relat_1(sK0)) )
                & ( ( k1_funct_1(sK0,X5) = X4
                    & r2_hidden(X5,k1_relat_1(sK0)) )
                  | k1_funct_1(X1,X4) != X5
                  | ~ r2_hidden(X4,k2_relat_1(sK0)) ) )
            & k1_relat_1(X1) = k2_relat_1(sK0) )
          | k2_funct_1(sK0) = X1 )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ? [X3,X2] :
            ( ( ( k1_funct_1(sK1,X2) != X3
                | ~ r2_hidden(X2,k2_relat_1(sK0)) )
              & k1_funct_1(sK0,X3) = X2
              & r2_hidden(X3,k1_relat_1(sK0)) )
            | ( ( k1_funct_1(sK0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(sK0)) )
              & k1_funct_1(sK1,X2) = X3
              & r2_hidden(X2,k2_relat_1(sK0)) ) )
        | k2_relat_1(sK0) != k1_relat_1(sK1)
        | k2_funct_1(sK0) != sK1 )
      & ( ( ! [X5,X4] :
              ( ( ( k1_funct_1(sK1,X4) = X5
                  & r2_hidden(X4,k2_relat_1(sK0)) )
                | k1_funct_1(sK0,X5) != X4
                | ~ r2_hidden(X5,k1_relat_1(sK0)) )
              & ( ( k1_funct_1(sK0,X5) = X4
                  & r2_hidden(X5,k1_relat_1(sK0)) )
                | k1_funct_1(sK1,X4) != X5
                | ~ r2_hidden(X4,k2_relat_1(sK0)) ) )
          & k2_relat_1(sK0) = k1_relat_1(sK1) )
        | k2_funct_1(sK0) = sK1 )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3,X2] :
        ( ( ( k1_funct_1(sK1,X2) != X3
            | ~ r2_hidden(X2,k2_relat_1(sK0)) )
          & k1_funct_1(sK0,X3) = X2
          & r2_hidden(X3,k1_relat_1(sK0)) )
        | ( ( k1_funct_1(sK0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(sK0)) )
          & k1_funct_1(sK1,X2) = X3
          & r2_hidden(X2,k2_relat_1(sK0)) ) )
   => ( ( ( sK3 != k1_funct_1(sK1,sK2)
          | ~ r2_hidden(sK2,k2_relat_1(sK0)) )
        & sK2 = k1_funct_1(sK0,sK3)
        & r2_hidden(sK3,k1_relat_1(sK0)) )
      | ( ( sK2 != k1_funct_1(sK0,sK3)
          | ~ r2_hidden(sK3,k1_relat_1(sK0)) )
        & sK3 = k1_funct_1(sK1,sK2)
        & r2_hidden(sK2,k2_relat_1(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2,X3] :
                ( ( ( k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) )
                  & k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) )
                | ( ( k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & k1_funct_1(X1,X2) = X3
                  & r2_hidden(X2,k2_relat_1(X0)) ) )
            | k2_relat_1(X0) != k1_relat_1(X1)
            | k2_funct_1(X0) != X1 )
          & ( ( ! [X4,X5] :
                  ( ( ( k1_funct_1(X1,X4) = X5
                      & r2_hidden(X4,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X5) != X4
                    | ~ r2_hidden(X5,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X5) = X4
                      & r2_hidden(X5,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X4) != X5
                    | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
              & k2_relat_1(X0) = k1_relat_1(X1) )
            | k2_funct_1(X0) = X1 )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2,X3] :
                ( ( ( k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) )
                  & k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) )
                | ( ( k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & k1_funct_1(X1,X2) = X3
                  & r2_hidden(X2,k2_relat_1(X0)) ) )
            | k2_relat_1(X0) != k1_relat_1(X1)
            | k2_funct_1(X0) != X1 )
          & ( ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k2_relat_1(X0) = k1_relat_1(X1) )
            | k2_funct_1(X0) = X1 )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2,X3] :
                ( ( ( k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) )
                  & k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) )
                | ( ( k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & k1_funct_1(X1,X2) = X3
                  & r2_hidden(X2,k2_relat_1(X0)) ) )
            | k2_relat_1(X0) != k1_relat_1(X1)
            | k2_funct_1(X0) != X1 )
          & ( ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k2_relat_1(X0) = k1_relat_1(X1) )
            | k2_funct_1(X0) = X1 )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_funct_1(X0) = X1
          <~> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_funct_1(X0) = X1
          <~> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ! [X1] :
              ( ( v1_funct_1(X1)
                & v1_relat_1(X1) )
             => ( k2_funct_1(X0) = X1
              <=> ( ! [X2,X3] :
                      ( ( ( k1_funct_1(X0,X3) = X2
                          & r2_hidden(X3,k1_relat_1(X0)) )
                       => ( k1_funct_1(X1,X2) = X3
                          & r2_hidden(X2,k2_relat_1(X0)) ) )
                      & ( ( k1_funct_1(X1,X2) = X3
                          & r2_hidden(X2,k2_relat_1(X0)) )
                       => ( k1_funct_1(X0,X3) = X2
                          & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                  & k2_relat_1(X0) = k1_relat_1(X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

fof(f159,plain,(
    spl12_14 ),
    inference(avatar_split_clause,[],[f44,f157])).

fof(f44,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f155,plain,(
    spl12_13 ),
    inference(avatar_split_clause,[],[f45,f153])).

fof(f45,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f151,plain,(
    spl12_12 ),
    inference(avatar_split_clause,[],[f46,f149])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f147,plain,(
    spl12_11 ),
    inference(avatar_split_clause,[],[f47,f145])).

fof(f47,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f143,plain,
    ( spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f48,f100,f97])).

fof(f48,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | k2_funct_1(sK0) = sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f141,plain,
    ( spl12_1
    | spl12_10 ),
    inference(avatar_split_clause,[],[f85,f139,f97])).

fof(f85,plain,(
    ! [X4] :
      ( r2_hidden(k1_funct_1(sK1,X4),k1_relat_1(sK0))
      | ~ r2_hidden(X4,k2_relat_1(sK0))
      | k2_funct_1(sK0) = sK1 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,k1_relat_1(sK0))
      | k1_funct_1(sK1,X4) != X5
      | ~ r2_hidden(X4,k2_relat_1(sK0))
      | k2_funct_1(sK0) = sK1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f137,plain,
    ( spl12_1
    | spl12_9 ),
    inference(avatar_split_clause,[],[f84,f135,f97])).

fof(f84,plain,(
    ! [X4] :
      ( k1_funct_1(sK0,k1_funct_1(sK1,X4)) = X4
      | ~ r2_hidden(X4,k2_relat_1(sK0))
      | k2_funct_1(sK0) = sK1 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X5] :
      ( k1_funct_1(sK0,X5) = X4
      | k1_funct_1(sK1,X4) != X5
      | ~ r2_hidden(X4,k2_relat_1(sK0))
      | k2_funct_1(sK0) = sK1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f129,plain,
    ( spl12_1
    | spl12_7 ),
    inference(avatar_split_clause,[],[f82,f127,f97])).

fof(f82,plain,(
    ! [X5] :
      ( k1_funct_1(sK1,k1_funct_1(sK0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(sK0))
      | k2_funct_1(sK0) = sK1 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X5] :
      ( k1_funct_1(sK1,X4) = X5
      | k1_funct_1(sK0,X5) != X4
      | ~ r2_hidden(X5,k1_relat_1(sK0))
      | k2_funct_1(sK0) = sK1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f124,plain,
    ( ~ spl12_1
    | ~ spl12_2
    | spl12_5
    | spl12_3 ),
    inference(avatar_split_clause,[],[f123,f103,f109,f100,f97])).

fof(f123,plain,
    ( r2_hidden(sK3,k1_relat_1(sK0))
    | r2_hidden(sK2,k1_relat_1(sK1))
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | k2_funct_1(sK0) != sK1 ),
    inference(inner_rewriting,[],[f53])).

fof(f53,plain,
    ( r2_hidden(sK3,k1_relat_1(sK0))
    | r2_hidden(sK2,k2_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f122,plain,
    ( ~ spl12_1
    | ~ spl12_2
    | spl12_6
    | spl12_3 ),
    inference(avatar_split_clause,[],[f54,f103,f112,f100,f97])).

fof(f54,plain,
    ( r2_hidden(sK3,k1_relat_1(sK0))
    | sK3 = k1_funct_1(sK1,sK2)
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f120,plain,
    ( ~ spl12_1
    | ~ spl12_2
    | spl12_5
    | spl12_4 ),
    inference(avatar_split_clause,[],[f118,f106,f109,f100,f97])).

fof(f118,plain,
    ( sK2 = k1_funct_1(sK0,sK3)
    | r2_hidden(sK2,k1_relat_1(sK1))
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | k2_funct_1(sK0) != sK1 ),
    inference(inner_rewriting,[],[f56])).

fof(f56,plain,
    ( sK2 = k1_funct_1(sK0,sK3)
    | r2_hidden(sK2,k2_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f117,plain,
    ( ~ spl12_1
    | ~ spl12_2
    | spl12_6
    | spl12_4 ),
    inference(avatar_split_clause,[],[f57,f106,f112,f100,f97])).

fof(f57,plain,
    ( sK2 = k1_funct_1(sK0,sK3)
    | sK3 = k1_funct_1(sK1,sK2)
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f114,plain,
    ( ~ spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f95,f112,f109,f106,f103,f100,f97])).

fof(f95,plain,
    ( sK3 != k1_funct_1(sK1,sK2)
    | ~ r2_hidden(sK2,k1_relat_1(sK1))
    | sK2 != k1_funct_1(sK0,sK3)
    | ~ r2_hidden(sK3,k1_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | k2_funct_1(sK0) != sK1 ),
    inference(inner_rewriting,[],[f61])).

fof(f61,plain,
    ( sK3 != k1_funct_1(sK1,sK2)
    | ~ r2_hidden(sK2,k2_relat_1(sK0))
    | sK2 != k1_funct_1(sK0,sK3)
    | ~ r2_hidden(sK3,k1_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f25])).

%------------------------------------------------------------------------------
