%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:26 EST 2020

% Result     : Theorem 5.39s
% Output     : Refutation 5.39s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 433 expanded)
%              Number of leaves         :   36 ( 147 expanded)
%              Depth                    :   19
%              Number of atoms          :  667 (2000 expanded)
%              Number of equality atoms :  102 ( 309 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2592,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f93,f98,f103,f108,f113,f118,f123,f128,f139,f144,f447,f668,f1692,f1718,f2156,f2591])).

fof(f2591,plain,(
    spl4_35 ),
    inference(avatar_contradiction_clause,[],[f2590])).

fof(f2590,plain,
    ( $false
    | spl4_35 ),
    inference(subsumption_resolution,[],[f2588,f283])).

fof(f283,plain,(
    ! [X0] : v1_xboole_0(k4_xboole_0(X0,X0)) ),
    inference(duplicate_literal_removal,[],[f272])).

fof(f272,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_xboole_0(X0,X0))
      | v1_xboole_0(k4_xboole_0(X0,X0)) ) ),
    inference(resolution,[],[f154,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(k4_xboole_0(X0,X1)),X1)
      | v1_xboole_0(k4_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f82,f74])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
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

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f154,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k4_xboole_0(X0,X1)),X0)
      | v1_xboole_0(k4_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f83,f74])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2588,plain,
    ( ~ v1_xboole_0(k4_xboole_0(sK1,sK1))
    | spl4_35 ),
    inference(trivial_inequality_removal,[],[f2586])).

fof(f2586,plain,
    ( sK1 != sK1
    | ~ v1_xboole_0(k4_xboole_0(sK1,sK1))
    | spl4_35 ),
    inference(superposition,[],[f2249,f206])).

fof(f206,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f198,f64])).

fof(f64,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f198,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f79,f157])).

fof(f157,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f77,f64])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f2249,plain,
    ( ! [X0] :
        ( sK1 != k5_xboole_0(sK1,X0)
        | ~ v1_xboole_0(X0) )
    | spl4_35 ),
    inference(superposition,[],[f2154,f367])).

fof(f367,plain,(
    ! [X16] :
      ( k1_xboole_0 = X16
      | ~ v1_xboole_0(X16) ) ),
    inference(forward_demodulation,[],[f359,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f359,plain,(
    ! [X15,X16] :
      ( k4_xboole_0(k1_xboole_0,X15) = X16
      | ~ v1_xboole_0(X16) ) ),
    inference(resolution,[],[f184,f131])).

fof(f131,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f80,f65])).

fof(f80,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f60,f73])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2154,plain,
    ( sK1 != k5_xboole_0(sK1,k1_xboole_0)
    | spl4_35 ),
    inference(avatar_component_clause,[],[f2152])).

fof(f2152,plain,
    ( spl4_35
  <=> sK1 = k5_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f2156,plain,
    ( spl4_20
    | ~ spl4_35
    | ~ spl4_9
    | ~ spl4_14
    | spl4_18 ),
    inference(avatar_split_clause,[],[f2149,f444,f219,f125,f2152,f647])).

fof(f647,plain,
    ( spl4_20
  <=> ! [X58] : ~ v1_xboole_0(X58) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f125,plain,
    ( spl4_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f219,plain,
    ( spl4_14
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f444,plain,
    ( spl4_18
  <=> sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f2149,plain,
    ( ! [X0] :
        ( sK1 != k5_xboole_0(sK1,k1_xboole_0)
        | ~ v1_xboole_0(X0) )
    | ~ spl4_9
    | ~ spl4_14
    | spl4_18 ),
    inference(duplicate_literal_removal,[],[f2118])).

fof(f2118,plain,
    ( ! [X0] :
        ( sK1 != k5_xboole_0(sK1,k1_xboole_0)
        | ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl4_9
    | ~ spl4_14
    | spl4_18 ),
    inference(superposition,[],[f448,f1625])).

fof(f1625,plain,
    ( ! [X9] :
        ( k5_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k1_tarski(X9))
        | ~ v1_xboole_0(X9) )
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(superposition,[],[f79,f1565])).

fof(f1565,plain,
    ( ! [X92] :
        ( k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X92))
        | ~ v1_xboole_0(X92) )
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(duplicate_literal_removal,[],[f1564])).

fof(f1564,plain,
    ( ! [X92] :
        ( k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X92))
        | ~ v1_xboole_0(X92)
        | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X92)) )
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f1563,f77])).

fof(f1563,plain,
    ( ! [X92] :
        ( ~ v1_xboole_0(X92)
        | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(X92)))
        | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X92)) )
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f1510,f127])).

fof(f127,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f1510,plain,
    ( ! [X92] :
        ( ~ v1_xboole_0(X92)
        | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(X92)))
        | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X92))
        | ~ v1_xboole_0(k1_xboole_0) )
    | ~ spl4_14 ),
    inference(superposition,[],[f897,f467])).

fof(f467,plain,(
    ! [X12,X13,X11] :
      ( sK2(X11,k4_xboole_0(X11,k1_tarski(X12)),X13) = X12
      | k3_xboole_0(X11,k1_tarski(X12)) = X13
      | ~ v1_xboole_0(X13) ) ),
    inference(forward_demodulation,[],[f466,f77])).

fof(f466,plain,(
    ! [X12,X13,X11] :
      ( sK2(X11,k4_xboole_0(X11,k1_tarski(X12)),X13) = X12
      | k4_xboole_0(X11,k4_xboole_0(X11,k1_tarski(X12))) = X13
      | ~ v1_xboole_0(X13) ) ),
    inference(subsumption_resolution,[],[f459,f73])).

fof(f459,plain,(
    ! [X12,X13,X11] :
      ( r2_hidden(sK2(X11,k4_xboole_0(X11,k1_tarski(X12)),X13),X13)
      | sK2(X11,k4_xboole_0(X11,k1_tarski(X12)),X13) = X12
      | k4_xboole_0(X11,k4_xboole_0(X11,k1_tarski(X12))) = X13
      | ~ v1_xboole_0(X13) ) ),
    inference(duplicate_literal_removal,[],[f453])).

fof(f453,plain,(
    ! [X12,X13,X11] :
      ( r2_hidden(sK2(X11,k4_xboole_0(X11,k1_tarski(X12)),X13),X13)
      | sK2(X11,k4_xboole_0(X11,k1_tarski(X12)),X13) = X12
      | k4_xboole_0(X11,k4_xboole_0(X11,k1_tarski(X12))) = X13
      | k4_xboole_0(X11,k4_xboole_0(X11,k1_tarski(X12))) = X13
      | ~ v1_xboole_0(X13) ) ),
    inference(resolution,[],[f191,f184])).

fof(f191,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(sK2(X6,k4_xboole_0(X7,k1_tarski(X8)),X9),X7)
      | r2_hidden(sK2(X6,k4_xboole_0(X7,k1_tarski(X8)),X9),X9)
      | sK2(X6,k4_xboole_0(X7,k1_tarski(X8)),X9) = X8
      | k4_xboole_0(X6,k4_xboole_0(X7,k1_tarski(X8))) = X9 ) ),
    inference(resolution,[],[f61,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f897,plain,
    ( ! [X28] :
        ( ~ v1_xboole_0(sK2(sK1,X28,k1_xboole_0))
        | k1_xboole_0 = k4_xboole_0(sK1,X28) )
    | ~ spl4_14 ),
    inference(resolution,[],[f187,f220])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f219])).

fof(f187,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK2(X11,X12,k1_xboole_0),X11)
      | k1_xboole_0 = k4_xboole_0(X11,X12) ) ),
    inference(resolution,[],[f60,f131])).

fof(f448,plain,
    ( ! [X0] :
        ( sK1 != k4_xboole_0(sK1,k1_tarski(X0))
        | ~ v1_xboole_0(X0) )
    | spl4_18 ),
    inference(superposition,[],[f446,f367])).

fof(f446,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f444])).

fof(f1718,plain,
    ( spl4_14
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_11
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1717,f215,f141,f136,f100,f95,f219])).

fof(f95,plain,
    ( spl4_3
  <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f100,plain,
    ( spl4_4
  <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f136,plain,
    ( spl4_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f141,plain,
    ( spl4_11
  <=> v1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f215,plain,
    ( spl4_13
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f1717,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_11
    | spl4_13 ),
    inference(subsumption_resolution,[],[f1716,f216])).

fof(f216,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f215])).

fof(f1716,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ r2_hidden(X0,sK1)
        | v1_xboole_0(k2_struct_0(sK0)) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f1715,f102])).

fof(f102,plain,
    ( v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f1715,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ r2_hidden(X0,sK1)
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_struct_0(sK0)) )
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f1714,f97])).

fof(f97,plain,
    ( v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f1714,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ r2_hidden(X0,sK1)
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_struct_0(sK0)) )
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f1713,f143])).

fof(f143,plain,
    ( v1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f1713,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v1_xboole_0(X0)
        | ~ r2_hidden(X0,sK1)
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_struct_0(sK0)) )
    | ~ spl4_10 ),
    inference(resolution,[],[f209,f138])).

fof(f138,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ v1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f208,f129])).

fof(f129,plain,(
    ! [X0] : k1_zfmisc_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(forward_demodulation,[],[f71,f69])).

fof(f69,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f71,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_7)).

fof(f208,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f207,f129])).

fof(f207,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f68,f73])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

fof(f1692,plain,(
    ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f1680])).

fof(f1680,plain,
    ( $false
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f131,f648,f237])).

fof(f237,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k3_xboole_0(X0,X1)),X0)
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f161,f74])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f83,f77])).

fof(f648,plain,
    ( ! [X58] : ~ v1_xboole_0(X58)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f647])).

fof(f668,plain,
    ( ~ spl4_7
    | spl4_8
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f667])).

fof(f667,plain,
    ( $false
    | ~ spl4_7
    | spl4_8
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f666,f122])).

fof(f122,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f666,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f664,f117])).

fof(f117,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f664,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_13 ),
    inference(resolution,[],[f217,f149])).

fof(f149,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(k2_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(k2_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X1) ) ),
    inference(superposition,[],[f70,f63])).

fof(f63,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f217,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f215])).

fof(f447,plain,
    ( ~ spl4_18
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6
    | ~ spl4_7
    | spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f442,f136,f120,f115,f110,f100,f95,f85,f444])).

fof(f85,plain,
    ( spl4_1
  <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f110,plain,
    ( spl4_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f442,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6
    | ~ spl4_7
    | spl4_8
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f441,f122])).

fof(f441,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | v2_struct_0(sK0)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f440,f117])).

fof(f440,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f439,f112])).

fof(f112,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f439,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f438,f102])).

fof(f438,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f437,f97])).

fof(f437,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl4_1
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f432,f138])).

fof(f432,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl4_1 ),
    inference(superposition,[],[f87,f234])).

fof(f234,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k4_xboole_0(X1,k1_tarski(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k4_xboole_0(X1,k1_tarski(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f67,f223])).

fof(f223,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(k1_zfmisc_1(k2_struct_0(X0)),X1,k1_tarski(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f222,f129])).

fof(f222,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(k1_zfmisc_1(k2_struct_0(X0)),X1,k1_tarski(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f66,f129])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f87,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f144,plain,
    ( spl4_11
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f134,f105,f141])).

fof(f105,plain,
    ( spl4_5
  <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f134,plain,
    ( v1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f107,f129])).

fof(f107,plain,
    ( v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f139,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f133,f90,f136])).

fof(f90,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f133,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f92,f129])).

fof(f92,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f128,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f75,f125])).

fof(f75,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f123,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f46,f120])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X1) )
   => ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

fof(f118,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f47,f115])).

fof(f47,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f113,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f48,f110])).

fof(f48,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f108,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f49,f105])).

fof(f49,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f103,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f50,f100])).

fof(f50,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f98,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f51,f95])).

fof(f51,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f93,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f52,f90])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f53,f85])).

fof(f53,plain,(
    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:39:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (17583)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.50  % (17600)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (17592)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (17600)Refutation not found, incomplete strategy% (17600)------------------------------
% 0.22/0.51  % (17600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17586)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (17582)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (17600)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (17600)Memory used [KB]: 10746
% 0.22/0.51  % (17600)Time elapsed: 0.065 s
% 0.22/0.51  % (17600)------------------------------
% 0.22/0.51  % (17600)------------------------------
% 0.22/0.52  % (17599)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (17591)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (17585)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (17578)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (17579)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (17581)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (17605)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (17606)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (17597)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (17587)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (17598)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (17595)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (17589)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (17590)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (17601)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (17596)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (17593)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (17580)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.57  % (17603)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.58  % (17604)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.58  % (17607)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.58  % (17588)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.58  % (17584)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.58  % (17588)Refutation not found, incomplete strategy% (17588)------------------------------
% 0.22/0.58  % (17588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (17588)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (17588)Memory used [KB]: 10746
% 0.22/0.58  % (17588)Time elapsed: 0.181 s
% 0.22/0.58  % (17588)------------------------------
% 0.22/0.58  % (17588)------------------------------
% 0.22/0.59  % (17602)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.60  % (17594)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.02/0.64  % (17608)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.67/0.72  % (17609)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.13/0.81  % (17583)Time limit reached!
% 3.13/0.81  % (17583)------------------------------
% 3.13/0.81  % (17583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.13/0.81  % (17583)Termination reason: Time limit
% 3.13/0.81  % (17583)Termination phase: Saturation
% 3.13/0.81  
% 3.13/0.81  % (17583)Memory used [KB]: 8827
% 3.13/0.81  % (17583)Time elapsed: 0.400 s
% 3.13/0.81  % (17583)------------------------------
% 3.13/0.81  % (17583)------------------------------
% 4.10/0.92  % (17595)Time limit reached!
% 4.10/0.92  % (17595)------------------------------
% 4.10/0.92  % (17595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.10/0.92  % (17595)Termination reason: Time limit
% 4.10/0.92  
% 4.10/0.92  % (17595)Memory used [KB]: 13432
% 4.10/0.92  % (17595)Time elapsed: 0.517 s
% 4.10/0.92  % (17595)------------------------------
% 4.10/0.92  % (17595)------------------------------
% 4.10/0.92  % (17590)Time limit reached!
% 4.10/0.92  % (17590)------------------------------
% 4.10/0.92  % (17590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.10/0.92  % (17590)Termination reason: Time limit
% 4.10/0.92  
% 4.10/0.92  % (17590)Memory used [KB]: 8571
% 4.10/0.92  % (17590)Time elapsed: 0.522 s
% 4.10/0.92  % (17590)------------------------------
% 4.10/0.92  % (17590)------------------------------
% 4.10/0.92  % (17578)Time limit reached!
% 4.10/0.92  % (17578)------------------------------
% 4.10/0.92  % (17578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.10/0.92  % (17578)Termination reason: Time limit
% 4.10/0.92  
% 4.10/0.92  % (17578)Memory used [KB]: 5245
% 4.10/0.92  % (17578)Time elapsed: 0.517 s
% 4.10/0.92  % (17578)------------------------------
% 4.10/0.92  % (17578)------------------------------
% 4.43/0.93  % (17579)Time limit reached!
% 4.43/0.93  % (17579)------------------------------
% 4.43/0.93  % (17579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/0.93  % (17579)Termination reason: Time limit
% 4.43/0.93  % (17579)Termination phase: Saturation
% 4.43/0.93  
% 4.43/0.93  % (17579)Memory used [KB]: 8315
% 4.43/0.93  % (17579)Time elapsed: 0.500 s
% 4.43/0.93  % (17579)------------------------------
% 4.43/0.93  % (17579)------------------------------
% 4.43/0.93  % (17610)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.93/1.01  % (17606)Time limit reached!
% 4.93/1.01  % (17606)------------------------------
% 4.93/1.01  % (17606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.93/1.01  % (17606)Termination reason: Time limit
% 4.93/1.01  
% 4.93/1.01  % (17606)Memory used [KB]: 8315
% 4.93/1.01  % (17606)Time elapsed: 0.611 s
% 4.93/1.01  % (17606)------------------------------
% 4.93/1.01  % (17606)------------------------------
% 4.93/1.03  % (17594)Time limit reached!
% 4.93/1.03  % (17594)------------------------------
% 4.93/1.03  % (17594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.93/1.03  % (17594)Termination reason: Time limit
% 4.93/1.03  
% 4.93/1.03  % (17594)Memory used [KB]: 14711
% 4.93/1.03  % (17594)Time elapsed: 0.601 s
% 4.93/1.03  % (17594)------------------------------
% 4.93/1.03  % (17594)------------------------------
% 4.93/1.04  % (17585)Time limit reached!
% 4.93/1.04  % (17585)------------------------------
% 4.93/1.04  % (17585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.93/1.04  % (17585)Termination reason: Time limit
% 4.93/1.04  
% 4.93/1.04  % (17585)Memory used [KB]: 11001
% 4.93/1.04  % (17585)Time elapsed: 0.625 s
% 4.93/1.04  % (17585)------------------------------
% 4.93/1.04  % (17585)------------------------------
% 4.93/1.05  % (17611)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.93/1.05  % (17614)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.93/1.05  % (17613)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.93/1.06  % (17612)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.39/1.10  % (17610)Refutation found. Thanks to Tanya!
% 5.39/1.10  % SZS status Theorem for theBenchmark
% 5.39/1.10  % SZS output start Proof for theBenchmark
% 5.39/1.10  fof(f2592,plain,(
% 5.39/1.10    $false),
% 5.39/1.10    inference(avatar_sat_refutation,[],[f88,f93,f98,f103,f108,f113,f118,f123,f128,f139,f144,f447,f668,f1692,f1718,f2156,f2591])).
% 5.39/1.10  fof(f2591,plain,(
% 5.39/1.10    spl4_35),
% 5.39/1.10    inference(avatar_contradiction_clause,[],[f2590])).
% 5.39/1.10  fof(f2590,plain,(
% 5.39/1.10    $false | spl4_35),
% 5.39/1.10    inference(subsumption_resolution,[],[f2588,f283])).
% 5.39/1.10  fof(f283,plain,(
% 5.39/1.10    ( ! [X0] : (v1_xboole_0(k4_xboole_0(X0,X0))) )),
% 5.39/1.10    inference(duplicate_literal_removal,[],[f272])).
% 5.39/1.10  fof(f272,plain,(
% 5.39/1.10    ( ! [X0] : (v1_xboole_0(k4_xboole_0(X0,X0)) | v1_xboole_0(k4_xboole_0(X0,X0))) )),
% 5.39/1.10    inference(resolution,[],[f154,f151])).
% 5.39/1.10  fof(f151,plain,(
% 5.39/1.10    ( ! [X0,X1] : (~r2_hidden(sK3(k4_xboole_0(X0,X1)),X1) | v1_xboole_0(k4_xboole_0(X0,X1))) )),
% 5.39/1.10    inference(resolution,[],[f82,f74])).
% 5.39/1.10  fof(f74,plain,(
% 5.39/1.10    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 5.39/1.10    inference(cnf_transformation,[],[f45])).
% 5.39/1.10  fof(f45,plain,(
% 5.39/1.10    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 5.39/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 5.39/1.10  fof(f44,plain,(
% 5.39/1.10    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 5.39/1.10    introduced(choice_axiom,[])).
% 5.39/1.10  fof(f43,plain,(
% 5.39/1.10    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 5.39/1.10    inference(rectify,[],[f42])).
% 5.39/1.10  fof(f42,plain,(
% 5.39/1.10    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 5.39/1.10    inference(nnf_transformation,[],[f1])).
% 5.39/1.10  fof(f1,axiom,(
% 5.39/1.10    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 5.39/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 5.39/1.10  fof(f82,plain,(
% 5.39/1.10    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 5.39/1.10    inference(equality_resolution,[],[f58])).
% 5.39/1.10  fof(f58,plain,(
% 5.39/1.10    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 5.39/1.10    inference(cnf_transformation,[],[f41])).
% 5.39/1.10  fof(f41,plain,(
% 5.39/1.10    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.39/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 5.39/1.10  fof(f40,plain,(
% 5.39/1.10    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 5.39/1.10    introduced(choice_axiom,[])).
% 5.39/1.10  fof(f39,plain,(
% 5.39/1.10    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.39/1.10    inference(rectify,[],[f38])).
% 5.39/1.10  fof(f38,plain,(
% 5.39/1.10    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.39/1.10    inference(flattening,[],[f37])).
% 5.39/1.10  fof(f37,plain,(
% 5.39/1.10    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.39/1.10    inference(nnf_transformation,[],[f2])).
% 5.39/1.10  fof(f2,axiom,(
% 5.39/1.10    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 5.39/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 5.39/1.10  fof(f154,plain,(
% 5.39/1.10    ( ! [X0,X1] : (r2_hidden(sK3(k4_xboole_0(X0,X1)),X0) | v1_xboole_0(k4_xboole_0(X0,X1))) )),
% 5.39/1.10    inference(resolution,[],[f83,f74])).
% 5.39/1.10  fof(f83,plain,(
% 5.39/1.10    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 5.39/1.10    inference(equality_resolution,[],[f57])).
% 5.39/1.10  fof(f57,plain,(
% 5.39/1.10    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 5.39/1.10    inference(cnf_transformation,[],[f41])).
% 5.39/1.10  fof(f2588,plain,(
% 5.39/1.10    ~v1_xboole_0(k4_xboole_0(sK1,sK1)) | spl4_35),
% 5.39/1.10    inference(trivial_inequality_removal,[],[f2586])).
% 5.39/1.10  fof(f2586,plain,(
% 5.39/1.10    sK1 != sK1 | ~v1_xboole_0(k4_xboole_0(sK1,sK1)) | spl4_35),
% 5.39/1.10    inference(superposition,[],[f2249,f206])).
% 5.39/1.10  fof(f206,plain,(
% 5.39/1.10    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 5.39/1.10    inference(forward_demodulation,[],[f198,f64])).
% 5.39/1.10  fof(f64,plain,(
% 5.39/1.10    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.39/1.10    inference(cnf_transformation,[],[f5])).
% 5.39/1.10  fof(f5,axiom,(
% 5.39/1.10    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 5.39/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 5.39/1.10  fof(f198,plain,(
% 5.39/1.10    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(X0,X0))) )),
% 5.39/1.10    inference(superposition,[],[f79,f157])).
% 5.39/1.10  fof(f157,plain,(
% 5.39/1.10    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 5.39/1.10    inference(superposition,[],[f77,f64])).
% 5.39/1.10  fof(f77,plain,(
% 5.39/1.10    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.39/1.10    inference(cnf_transformation,[],[f6])).
% 5.39/1.10  fof(f6,axiom,(
% 5.39/1.10    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.39/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.39/1.10  fof(f79,plain,(
% 5.39/1.10    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.39/1.10    inference(cnf_transformation,[],[f4])).
% 5.39/1.10  fof(f4,axiom,(
% 5.39/1.10    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.39/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.39/1.10  fof(f2249,plain,(
% 5.39/1.10    ( ! [X0] : (sK1 != k5_xboole_0(sK1,X0) | ~v1_xboole_0(X0)) ) | spl4_35),
% 5.39/1.10    inference(superposition,[],[f2154,f367])).
% 5.39/1.10  fof(f367,plain,(
% 5.39/1.10    ( ! [X16] : (k1_xboole_0 = X16 | ~v1_xboole_0(X16)) )),
% 5.39/1.10    inference(forward_demodulation,[],[f359,f65])).
% 5.39/1.10  fof(f65,plain,(
% 5.39/1.10    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 5.39/1.10    inference(cnf_transformation,[],[f7])).
% 5.39/1.10  fof(f7,axiom,(
% 5.39/1.10    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 5.39/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 5.39/1.10  fof(f359,plain,(
% 5.39/1.10    ( ! [X15,X16] : (k4_xboole_0(k1_xboole_0,X15) = X16 | ~v1_xboole_0(X16)) )),
% 5.39/1.10    inference(resolution,[],[f184,f131])).
% 5.39/1.10  fof(f131,plain,(
% 5.39/1.10    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 5.39/1.10    inference(superposition,[],[f80,f65])).
% 5.39/1.10  fof(f80,plain,(
% 5.39/1.10    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 5.39/1.10    inference(equality_resolution,[],[f55])).
% 5.39/1.10  fof(f55,plain,(
% 5.39/1.10    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 5.39/1.10    inference(cnf_transformation,[],[f36])).
% 5.39/1.10  fof(f36,plain,(
% 5.39/1.10    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 5.39/1.10    inference(flattening,[],[f35])).
% 5.39/1.10  fof(f35,plain,(
% 5.39/1.10    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 5.39/1.10    inference(nnf_transformation,[],[f10])).
% 5.39/1.10  fof(f10,axiom,(
% 5.39/1.10    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 5.39/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 5.39/1.10  fof(f184,plain,(
% 5.39/1.10    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2 | ~v1_xboole_0(X2)) )),
% 5.39/1.10    inference(resolution,[],[f60,f73])).
% 5.39/1.10  fof(f73,plain,(
% 5.39/1.10    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 5.39/1.10    inference(cnf_transformation,[],[f45])).
% 5.39/1.10  fof(f60,plain,(
% 5.39/1.10    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 5.39/1.10    inference(cnf_transformation,[],[f41])).
% 5.39/1.10  fof(f2154,plain,(
% 5.39/1.10    sK1 != k5_xboole_0(sK1,k1_xboole_0) | spl4_35),
% 5.39/1.10    inference(avatar_component_clause,[],[f2152])).
% 5.39/1.10  fof(f2152,plain,(
% 5.39/1.10    spl4_35 <=> sK1 = k5_xboole_0(sK1,k1_xboole_0)),
% 5.39/1.10    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 5.39/1.10  fof(f2156,plain,(
% 5.39/1.10    spl4_20 | ~spl4_35 | ~spl4_9 | ~spl4_14 | spl4_18),
% 5.39/1.10    inference(avatar_split_clause,[],[f2149,f444,f219,f125,f2152,f647])).
% 5.39/1.10  fof(f647,plain,(
% 5.39/1.10    spl4_20 <=> ! [X58] : ~v1_xboole_0(X58)),
% 5.39/1.10    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 5.39/1.10  fof(f125,plain,(
% 5.39/1.10    spl4_9 <=> v1_xboole_0(k1_xboole_0)),
% 5.39/1.10    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 5.39/1.10  fof(f219,plain,(
% 5.39/1.10    spl4_14 <=> ! [X0] : (~v1_xboole_0(X0) | ~r2_hidden(X0,sK1))),
% 5.39/1.10    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 5.39/1.10  fof(f444,plain,(
% 5.39/1.10    spl4_18 <=> sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 5.39/1.10    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 5.39/1.10  fof(f2149,plain,(
% 5.39/1.10    ( ! [X0] : (sK1 != k5_xboole_0(sK1,k1_xboole_0) | ~v1_xboole_0(X0)) ) | (~spl4_9 | ~spl4_14 | spl4_18)),
% 5.39/1.10    inference(duplicate_literal_removal,[],[f2118])).
% 5.39/1.10  fof(f2118,plain,(
% 5.39/1.10    ( ! [X0] : (sK1 != k5_xboole_0(sK1,k1_xboole_0) | ~v1_xboole_0(X0) | ~v1_xboole_0(X0)) ) | (~spl4_9 | ~spl4_14 | spl4_18)),
% 5.39/1.10    inference(superposition,[],[f448,f1625])).
% 5.39/1.10  fof(f1625,plain,(
% 5.39/1.10    ( ! [X9] : (k5_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k1_tarski(X9)) | ~v1_xboole_0(X9)) ) | (~spl4_9 | ~spl4_14)),
% 5.39/1.10    inference(superposition,[],[f79,f1565])).
% 5.39/1.10  fof(f1565,plain,(
% 5.39/1.10    ( ! [X92] : (k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X92)) | ~v1_xboole_0(X92)) ) | (~spl4_9 | ~spl4_14)),
% 5.39/1.10    inference(duplicate_literal_removal,[],[f1564])).
% 5.39/1.10  fof(f1564,plain,(
% 5.39/1.10    ( ! [X92] : (k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X92)) | ~v1_xboole_0(X92) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X92))) ) | (~spl4_9 | ~spl4_14)),
% 5.39/1.10    inference(forward_demodulation,[],[f1563,f77])).
% 5.39/1.10  fof(f1563,plain,(
% 5.39/1.10    ( ! [X92] : (~v1_xboole_0(X92) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(X92))) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X92))) ) | (~spl4_9 | ~spl4_14)),
% 5.39/1.10    inference(subsumption_resolution,[],[f1510,f127])).
% 5.39/1.10  fof(f127,plain,(
% 5.39/1.10    v1_xboole_0(k1_xboole_0) | ~spl4_9),
% 5.39/1.10    inference(avatar_component_clause,[],[f125])).
% 5.39/1.10  fof(f1510,plain,(
% 5.39/1.10    ( ! [X92] : (~v1_xboole_0(X92) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(X92))) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X92)) | ~v1_xboole_0(k1_xboole_0)) ) | ~spl4_14),
% 5.39/1.10    inference(superposition,[],[f897,f467])).
% 5.39/1.10  fof(f467,plain,(
% 5.39/1.10    ( ! [X12,X13,X11] : (sK2(X11,k4_xboole_0(X11,k1_tarski(X12)),X13) = X12 | k3_xboole_0(X11,k1_tarski(X12)) = X13 | ~v1_xboole_0(X13)) )),
% 5.39/1.10    inference(forward_demodulation,[],[f466,f77])).
% 5.39/1.10  fof(f466,plain,(
% 5.39/1.10    ( ! [X12,X13,X11] : (sK2(X11,k4_xboole_0(X11,k1_tarski(X12)),X13) = X12 | k4_xboole_0(X11,k4_xboole_0(X11,k1_tarski(X12))) = X13 | ~v1_xboole_0(X13)) )),
% 5.39/1.10    inference(subsumption_resolution,[],[f459,f73])).
% 5.39/1.10  fof(f459,plain,(
% 5.39/1.10    ( ! [X12,X13,X11] : (r2_hidden(sK2(X11,k4_xboole_0(X11,k1_tarski(X12)),X13),X13) | sK2(X11,k4_xboole_0(X11,k1_tarski(X12)),X13) = X12 | k4_xboole_0(X11,k4_xboole_0(X11,k1_tarski(X12))) = X13 | ~v1_xboole_0(X13)) )),
% 5.39/1.10    inference(duplicate_literal_removal,[],[f453])).
% 5.39/1.10  fof(f453,plain,(
% 5.39/1.10    ( ! [X12,X13,X11] : (r2_hidden(sK2(X11,k4_xboole_0(X11,k1_tarski(X12)),X13),X13) | sK2(X11,k4_xboole_0(X11,k1_tarski(X12)),X13) = X12 | k4_xboole_0(X11,k4_xboole_0(X11,k1_tarski(X12))) = X13 | k4_xboole_0(X11,k4_xboole_0(X11,k1_tarski(X12))) = X13 | ~v1_xboole_0(X13)) )),
% 5.39/1.10    inference(resolution,[],[f191,f184])).
% 5.39/1.10  fof(f191,plain,(
% 5.39/1.10    ( ! [X6,X8,X7,X9] : (~r2_hidden(sK2(X6,k4_xboole_0(X7,k1_tarski(X8)),X9),X7) | r2_hidden(sK2(X6,k4_xboole_0(X7,k1_tarski(X8)),X9),X9) | sK2(X6,k4_xboole_0(X7,k1_tarski(X8)),X9) = X8 | k4_xboole_0(X6,k4_xboole_0(X7,k1_tarski(X8))) = X9) )),
% 5.39/1.10    inference(resolution,[],[f61,f56])).
% 5.39/1.10  fof(f56,plain,(
% 5.39/1.10    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 5.39/1.10    inference(cnf_transformation,[],[f36])).
% 5.39/1.10  fof(f61,plain,(
% 5.39/1.10    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 5.39/1.10    inference(cnf_transformation,[],[f41])).
% 5.39/1.10  fof(f897,plain,(
% 5.39/1.10    ( ! [X28] : (~v1_xboole_0(sK2(sK1,X28,k1_xboole_0)) | k1_xboole_0 = k4_xboole_0(sK1,X28)) ) | ~spl4_14),
% 5.39/1.10    inference(resolution,[],[f187,f220])).
% 5.39/1.10  fof(f220,plain,(
% 5.39/1.10    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0)) ) | ~spl4_14),
% 5.39/1.10    inference(avatar_component_clause,[],[f219])).
% 5.39/1.10  fof(f187,plain,(
% 5.39/1.10    ( ! [X12,X11] : (r2_hidden(sK2(X11,X12,k1_xboole_0),X11) | k1_xboole_0 = k4_xboole_0(X11,X12)) )),
% 5.39/1.10    inference(resolution,[],[f60,f131])).
% 5.39/1.10  fof(f448,plain,(
% 5.39/1.10    ( ! [X0] : (sK1 != k4_xboole_0(sK1,k1_tarski(X0)) | ~v1_xboole_0(X0)) ) | spl4_18),
% 5.39/1.10    inference(superposition,[],[f446,f367])).
% 5.39/1.10  fof(f446,plain,(
% 5.39/1.10    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | spl4_18),
% 5.39/1.10    inference(avatar_component_clause,[],[f444])).
% 5.39/1.10  fof(f1718,plain,(
% 5.39/1.10    spl4_14 | ~spl4_3 | ~spl4_4 | ~spl4_10 | ~spl4_11 | spl4_13),
% 5.39/1.10    inference(avatar_split_clause,[],[f1717,f215,f141,f136,f100,f95,f219])).
% 5.39/1.10  fof(f95,plain,(
% 5.39/1.10    spl4_3 <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 5.39/1.10    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 5.39/1.10  fof(f100,plain,(
% 5.39/1.10    spl4_4 <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 5.39/1.10    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 5.39/1.10  fof(f136,plain,(
% 5.39/1.10    spl4_10 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))),
% 5.39/1.10    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 5.39/1.10  fof(f141,plain,(
% 5.39/1.10    spl4_11 <=> v1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 5.39/1.10    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 5.39/1.10  fof(f215,plain,(
% 5.39/1.10    spl4_13 <=> v1_xboole_0(k2_struct_0(sK0))),
% 5.39/1.10    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 5.39/1.10  fof(f1717,plain,(
% 5.39/1.10    ( ! [X0] : (~v1_xboole_0(X0) | ~r2_hidden(X0,sK1)) ) | (~spl4_3 | ~spl4_4 | ~spl4_10 | ~spl4_11 | spl4_13)),
% 5.39/1.10    inference(subsumption_resolution,[],[f1716,f216])).
% 5.39/1.10  fof(f216,plain,(
% 5.39/1.10    ~v1_xboole_0(k2_struct_0(sK0)) | spl4_13),
% 5.39/1.10    inference(avatar_component_clause,[],[f215])).
% 5.39/1.10  fof(f1716,plain,(
% 5.39/1.10    ( ! [X0] : (~v1_xboole_0(X0) | ~r2_hidden(X0,sK1) | v1_xboole_0(k2_struct_0(sK0))) ) | (~spl4_3 | ~spl4_4 | ~spl4_10 | ~spl4_11)),
% 5.39/1.10    inference(subsumption_resolution,[],[f1715,f102])).
% 5.39/1.10  fof(f102,plain,(
% 5.39/1.10    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~spl4_4),
% 5.39/1.10    inference(avatar_component_clause,[],[f100])).
% 5.39/1.10  fof(f1715,plain,(
% 5.39/1.10    ( ! [X0] : (~v1_xboole_0(X0) | ~r2_hidden(X0,sK1) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0))) ) | (~spl4_3 | ~spl4_10 | ~spl4_11)),
% 5.39/1.10    inference(subsumption_resolution,[],[f1714,f97])).
% 5.39/1.10  fof(f97,plain,(
% 5.39/1.10    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~spl4_3),
% 5.39/1.10    inference(avatar_component_clause,[],[f95])).
% 5.39/1.10  fof(f1714,plain,(
% 5.39/1.10    ( ! [X0] : (~v1_xboole_0(X0) | ~r2_hidden(X0,sK1) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0))) ) | (~spl4_10 | ~spl4_11)),
% 5.39/1.10    inference(subsumption_resolution,[],[f1713,f143])).
% 5.39/1.10  fof(f143,plain,(
% 5.39/1.10    v1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl4_11),
% 5.39/1.10    inference(avatar_component_clause,[],[f141])).
% 5.39/1.10  fof(f1713,plain,(
% 5.39/1.10    ( ! [X0] : (~v1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_xboole_0(X0) | ~r2_hidden(X0,sK1) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0))) ) | ~spl4_10),
% 5.39/1.10    inference(resolution,[],[f209,f138])).
% 5.39/1.10  fof(f138,plain,(
% 5.39/1.10    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~spl4_10),
% 5.39/1.10    inference(avatar_component_clause,[],[f136])).
% 5.39/1.10  fof(f209,plain,(
% 5.39/1.10    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~v1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 5.39/1.10    inference(forward_demodulation,[],[f208,f129])).
% 5.39/1.10  fof(f129,plain,(
% 5.39/1.10    ( ! [X0] : (k1_zfmisc_1(X0) = u1_struct_0(k3_yellow_1(X0))) )),
% 5.39/1.10    inference(forward_demodulation,[],[f71,f69])).
% 5.39/1.10  fof(f69,plain,(
% 5.39/1.10    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 5.39/1.10    inference(cnf_transformation,[],[f12])).
% 5.39/1.10  fof(f12,axiom,(
% 5.39/1.10    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 5.39/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 5.39/1.10  fof(f71,plain,(
% 5.39/1.10    ( ! [X0] : (k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))) )),
% 5.39/1.10    inference(cnf_transformation,[],[f16])).
% 5.39/1.10  fof(f16,axiom,(
% 5.39/1.10    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))),
% 5.39/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_7)).
% 5.39/1.10  fof(f208,plain,(
% 5.39/1.10    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 5.39/1.10    inference(forward_demodulation,[],[f207,f129])).
% 5.39/1.10  fof(f207,plain,(
% 5.39/1.10    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 5.39/1.10    inference(subsumption_resolution,[],[f68,f73])).
% 5.39/1.10  fof(f68,plain,(
% 5.39/1.10    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 5.39/1.10    inference(cnf_transformation,[],[f28])).
% 5.39/1.10  fof(f28,plain,(
% 5.39/1.10    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 5.39/1.10    inference(flattening,[],[f27])).
% 5.39/1.10  fof(f27,plain,(
% 5.39/1.10    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 5.39/1.10    inference(ennf_transformation,[],[f18])).
% 5.39/1.10  fof(f18,axiom,(
% 5.39/1.10    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 5.39/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).
% 5.39/1.10  fof(f1692,plain,(
% 5.39/1.10    ~spl4_20),
% 5.39/1.10    inference(avatar_contradiction_clause,[],[f1680])).
% 5.39/1.10  fof(f1680,plain,(
% 5.39/1.10    $false | ~spl4_20),
% 5.39/1.10    inference(unit_resulting_resolution,[],[f131,f648,f237])).
% 5.39/1.10  fof(f237,plain,(
% 5.39/1.10    ( ! [X0,X1] : (r2_hidden(sK3(k3_xboole_0(X0,X1)),X0) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 5.39/1.10    inference(resolution,[],[f161,f74])).
% 5.39/1.10  fof(f161,plain,(
% 5.39/1.10    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | r2_hidden(X2,X0)) )),
% 5.39/1.10    inference(superposition,[],[f83,f77])).
% 5.39/1.10  fof(f648,plain,(
% 5.39/1.10    ( ! [X58] : (~v1_xboole_0(X58)) ) | ~spl4_20),
% 5.39/1.10    inference(avatar_component_clause,[],[f647])).
% 5.39/1.10  fof(f668,plain,(
% 5.39/1.10    ~spl4_7 | spl4_8 | ~spl4_13),
% 5.39/1.10    inference(avatar_contradiction_clause,[],[f667])).
% 5.39/1.10  fof(f667,plain,(
% 5.39/1.10    $false | (~spl4_7 | spl4_8 | ~spl4_13)),
% 5.39/1.10    inference(subsumption_resolution,[],[f666,f122])).
% 5.39/1.10  fof(f122,plain,(
% 5.39/1.10    ~v2_struct_0(sK0) | spl4_8),
% 5.39/1.10    inference(avatar_component_clause,[],[f120])).
% 5.39/1.10  fof(f120,plain,(
% 5.39/1.10    spl4_8 <=> v2_struct_0(sK0)),
% 5.39/1.10    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 5.39/1.10  fof(f666,plain,(
% 5.39/1.10    v2_struct_0(sK0) | (~spl4_7 | ~spl4_13)),
% 5.39/1.10    inference(subsumption_resolution,[],[f664,f117])).
% 5.39/1.10  fof(f117,plain,(
% 5.39/1.10    l1_struct_0(sK0) | ~spl4_7),
% 5.39/1.10    inference(avatar_component_clause,[],[f115])).
% 5.39/1.10  fof(f115,plain,(
% 5.39/1.10    spl4_7 <=> l1_struct_0(sK0)),
% 5.39/1.10    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 5.39/1.10  fof(f664,plain,(
% 5.39/1.10    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl4_13),
% 5.39/1.10    inference(resolution,[],[f217,f149])).
% 5.39/1.10  fof(f149,plain,(
% 5.39/1.10    ( ! [X1] : (~v1_xboole_0(k2_struct_0(X1)) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 5.39/1.10    inference(duplicate_literal_removal,[],[f148])).
% 5.39/1.10  fof(f148,plain,(
% 5.39/1.10    ( ! [X1] : (~v1_xboole_0(k2_struct_0(X1)) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X1)) )),
% 5.39/1.10    inference(superposition,[],[f70,f63])).
% 5.39/1.10  fof(f63,plain,(
% 5.39/1.10    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 5.39/1.10    inference(cnf_transformation,[],[f23])).
% 5.39/1.10  fof(f23,plain,(
% 5.39/1.10    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 5.39/1.10    inference(ennf_transformation,[],[f13])).
% 5.39/1.10  fof(f13,axiom,(
% 5.39/1.10    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 5.39/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 5.39/1.10  fof(f70,plain,(
% 5.39/1.10    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 5.39/1.10    inference(cnf_transformation,[],[f30])).
% 5.39/1.10  fof(f30,plain,(
% 5.39/1.10    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 5.39/1.10    inference(flattening,[],[f29])).
% 5.39/1.10  fof(f29,plain,(
% 5.39/1.10    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 5.39/1.10    inference(ennf_transformation,[],[f14])).
% 5.39/1.10  fof(f14,axiom,(
% 5.39/1.10    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 5.39/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 5.39/1.10  fof(f217,plain,(
% 5.39/1.10    v1_xboole_0(k2_struct_0(sK0)) | ~spl4_13),
% 5.39/1.10    inference(avatar_component_clause,[],[f215])).
% 5.39/1.10  fof(f447,plain,(
% 5.39/1.10    ~spl4_18 | spl4_1 | ~spl4_3 | ~spl4_4 | spl4_6 | ~spl4_7 | spl4_8 | ~spl4_10),
% 5.39/1.10    inference(avatar_split_clause,[],[f442,f136,f120,f115,f110,f100,f95,f85,f444])).
% 5.39/1.10  fof(f85,plain,(
% 5.39/1.10    spl4_1 <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 5.39/1.10    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 5.39/1.10  fof(f110,plain,(
% 5.39/1.10    spl4_6 <=> v1_xboole_0(sK1)),
% 5.39/1.10    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 5.39/1.10  fof(f442,plain,(
% 5.39/1.10    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | (spl4_1 | ~spl4_3 | ~spl4_4 | spl4_6 | ~spl4_7 | spl4_8 | ~spl4_10)),
% 5.39/1.10    inference(subsumption_resolution,[],[f441,f122])).
% 5.39/1.10  fof(f441,plain,(
% 5.39/1.10    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | v2_struct_0(sK0) | (spl4_1 | ~spl4_3 | ~spl4_4 | spl4_6 | ~spl4_7 | ~spl4_10)),
% 5.39/1.10    inference(subsumption_resolution,[],[f440,f117])).
% 5.39/1.10  fof(f440,plain,(
% 5.39/1.10    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (spl4_1 | ~spl4_3 | ~spl4_4 | spl4_6 | ~spl4_10)),
% 5.39/1.10    inference(subsumption_resolution,[],[f439,f112])).
% 5.39/1.10  fof(f112,plain,(
% 5.39/1.10    ~v1_xboole_0(sK1) | spl4_6),
% 5.39/1.10    inference(avatar_component_clause,[],[f110])).
% 5.39/1.10  fof(f439,plain,(
% 5.39/1.10    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_10)),
% 5.39/1.10    inference(subsumption_resolution,[],[f438,f102])).
% 5.39/1.10  fof(f438,plain,(
% 5.39/1.10    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (spl4_1 | ~spl4_3 | ~spl4_10)),
% 5.39/1.10    inference(subsumption_resolution,[],[f437,f97])).
% 5.39/1.10  fof(f437,plain,(
% 5.39/1.10    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (spl4_1 | ~spl4_10)),
% 5.39/1.10    inference(subsumption_resolution,[],[f432,f138])).
% 5.39/1.10  fof(f432,plain,(
% 5.39/1.10    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | spl4_1),
% 5.39/1.10    inference(superposition,[],[f87,f234])).
% 5.39/1.10  fof(f234,plain,(
% 5.39/1.10    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k4_xboole_0(X1,k1_tarski(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 5.39/1.10    inference(duplicate_literal_removal,[],[f233])).
% 5.39/1.10  fof(f233,plain,(
% 5.39/1.10    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k4_xboole_0(X1,k1_tarski(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 5.39/1.10    inference(superposition,[],[f67,f223])).
% 5.39/1.10  fof(f223,plain,(
% 5.39/1.10    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(k1_zfmisc_1(k2_struct_0(X0)),X1,k1_tarski(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 5.39/1.10    inference(forward_demodulation,[],[f222,f129])).
% 5.39/1.10  fof(f222,plain,(
% 5.39/1.10    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(k1_zfmisc_1(k2_struct_0(X0)),X1,k1_tarski(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 5.39/1.10    inference(forward_demodulation,[],[f66,f129])).
% 5.39/1.10  fof(f66,plain,(
% 5.39/1.10    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 5.39/1.10    inference(cnf_transformation,[],[f25])).
% 5.39/1.10  fof(f25,plain,(
% 5.39/1.10    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 5.39/1.10    inference(flattening,[],[f24])).
% 5.39/1.10  fof(f24,plain,(
% 5.39/1.10    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 5.39/1.10    inference(ennf_transformation,[],[f17])).
% 5.39/1.10  fof(f17,axiom,(
% 5.39/1.10    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 5.39/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).
% 5.39/1.10  fof(f67,plain,(
% 5.39/1.10    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.39/1.10    inference(cnf_transformation,[],[f26])).
% 5.39/1.10  fof(f26,plain,(
% 5.39/1.10    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.39/1.10    inference(ennf_transformation,[],[f11])).
% 5.39/1.10  fof(f11,axiom,(
% 5.39/1.10    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 5.39/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 5.39/1.10  fof(f87,plain,(
% 5.39/1.10    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl4_1),
% 5.39/1.10    inference(avatar_component_clause,[],[f85])).
% 5.39/1.10  fof(f144,plain,(
% 5.39/1.10    spl4_11 | ~spl4_5),
% 5.39/1.10    inference(avatar_split_clause,[],[f134,f105,f141])).
% 5.39/1.10  fof(f105,plain,(
% 5.39/1.10    spl4_5 <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 5.39/1.10    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 5.39/1.10  fof(f134,plain,(
% 5.39/1.10    v1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl4_5),
% 5.39/1.10    inference(backward_demodulation,[],[f107,f129])).
% 5.39/1.10  fof(f107,plain,(
% 5.39/1.10    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~spl4_5),
% 5.39/1.10    inference(avatar_component_clause,[],[f105])).
% 5.39/1.10  fof(f139,plain,(
% 5.39/1.10    spl4_10 | ~spl4_2),
% 5.39/1.10    inference(avatar_split_clause,[],[f133,f90,f136])).
% 5.39/1.10  fof(f90,plain,(
% 5.39/1.10    spl4_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 5.39/1.10    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 5.39/1.10  fof(f133,plain,(
% 5.39/1.10    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~spl4_2),
% 5.39/1.10    inference(backward_demodulation,[],[f92,f129])).
% 5.39/1.10  fof(f92,plain,(
% 5.39/1.10    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~spl4_2),
% 5.39/1.10    inference(avatar_component_clause,[],[f90])).
% 5.39/1.10  fof(f128,plain,(
% 5.39/1.10    spl4_9),
% 5.39/1.10    inference(avatar_split_clause,[],[f75,f125])).
% 5.39/1.10  fof(f75,plain,(
% 5.39/1.10    v1_xboole_0(k1_xboole_0)),
% 5.39/1.10    inference(cnf_transformation,[],[f3])).
% 5.39/1.10  fof(f3,axiom,(
% 5.39/1.10    v1_xboole_0(k1_xboole_0)),
% 5.39/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 5.39/1.10  fof(f123,plain,(
% 5.39/1.10    ~spl4_8),
% 5.39/1.10    inference(avatar_split_clause,[],[f46,f120])).
% 5.39/1.10  fof(f46,plain,(
% 5.39/1.10    ~v2_struct_0(sK0)),
% 5.39/1.10    inference(cnf_transformation,[],[f34])).
% 5.39/1.10  fof(f34,plain,(
% 5.39/1.10    (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 5.39/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f33,f32])).
% 5.39/1.10  fof(f32,plain,(
% 5.39/1.10    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 5.39/1.10    introduced(choice_axiom,[])).
% 5.39/1.10  fof(f33,plain,(
% 5.39/1.10    ? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 5.39/1.10    introduced(choice_axiom,[])).
% 5.39/1.10  fof(f22,plain,(
% 5.39/1.10    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 5.39/1.10    inference(flattening,[],[f21])).
% 5.39/1.10  fof(f21,plain,(
% 5.39/1.10    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 5.39/1.10    inference(ennf_transformation,[],[f20])).
% 5.39/1.10  fof(f20,negated_conjecture,(
% 5.39/1.10    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 5.39/1.10    inference(negated_conjecture,[],[f19])).
% 5.39/1.10  fof(f19,conjecture,(
% 5.39/1.10    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 5.39/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).
% 5.39/1.10  fof(f118,plain,(
% 5.39/1.10    spl4_7),
% 5.39/1.10    inference(avatar_split_clause,[],[f47,f115])).
% 5.39/1.10  fof(f47,plain,(
% 5.39/1.10    l1_struct_0(sK0)),
% 5.39/1.10    inference(cnf_transformation,[],[f34])).
% 5.39/1.10  fof(f113,plain,(
% 5.39/1.10    ~spl4_6),
% 5.39/1.10    inference(avatar_split_clause,[],[f48,f110])).
% 5.39/1.10  fof(f48,plain,(
% 5.39/1.10    ~v1_xboole_0(sK1)),
% 5.39/1.10    inference(cnf_transformation,[],[f34])).
% 5.39/1.10  fof(f108,plain,(
% 5.39/1.10    spl4_5),
% 5.39/1.10    inference(avatar_split_clause,[],[f49,f105])).
% 5.39/1.10  fof(f49,plain,(
% 5.39/1.10    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 5.39/1.10    inference(cnf_transformation,[],[f34])).
% 5.39/1.10  fof(f103,plain,(
% 5.39/1.10    spl4_4),
% 5.39/1.10    inference(avatar_split_clause,[],[f50,f100])).
% 5.39/1.10  fof(f50,plain,(
% 5.39/1.10    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 5.39/1.10    inference(cnf_transformation,[],[f34])).
% 5.39/1.10  fof(f98,plain,(
% 5.39/1.10    spl4_3),
% 5.39/1.10    inference(avatar_split_clause,[],[f51,f95])).
% 5.39/1.10  fof(f51,plain,(
% 5.39/1.10    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 5.39/1.10    inference(cnf_transformation,[],[f34])).
% 5.39/1.10  fof(f93,plain,(
% 5.39/1.10    spl4_2),
% 5.39/1.10    inference(avatar_split_clause,[],[f52,f90])).
% 5.39/1.10  fof(f52,plain,(
% 5.39/1.10    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 5.39/1.10    inference(cnf_transformation,[],[f34])).
% 5.39/1.10  fof(f88,plain,(
% 5.39/1.10    ~spl4_1),
% 5.39/1.10    inference(avatar_split_clause,[],[f53,f85])).
% 5.39/1.10  fof(f53,plain,(
% 5.39/1.10    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 5.39/1.10    inference(cnf_transformation,[],[f34])).
% 5.39/1.10  % SZS output end Proof for theBenchmark
% 5.39/1.10  % (17610)------------------------------
% 5.39/1.10  % (17610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.39/1.10  % (17610)Termination reason: Refutation
% 5.39/1.10  
% 5.39/1.10  % (17610)Memory used [KB]: 7931
% 5.39/1.10  % (17610)Time elapsed: 0.245 s
% 5.39/1.10  % (17610)------------------------------
% 5.39/1.10  % (17610)------------------------------
% 5.39/1.10  % (17576)Success in time 0.731 s
%------------------------------------------------------------------------------
