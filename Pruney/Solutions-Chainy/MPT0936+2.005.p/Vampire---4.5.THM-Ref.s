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
% DateTime   : Thu Dec  3 12:59:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 364 expanded)
%              Number of leaves         :   22 ( 123 expanded)
%              Depth                    :   17
%              Number of atoms          :  298 ( 968 expanded)
%              Number of equality atoms :  185 ( 733 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f253,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f121,f129,f134,f153,f171,f225,f252])).

fof(f252,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f239,f27])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

% (21331)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f239,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f80,f105])).

fof(f105,plain,
    ( k1_xboole_0 = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_2
  <=> k1_xboole_0 = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),X0) ),
    inference(resolution,[],[f75,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f75,plain,(
    ! [X6,X2,X3,X1] : r2_hidden(X6,k5_enumset1(X6,X6,X6,X6,X1,X2,X3)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X6,X4,X2,X3,X1] :
      ( r2_hidden(X6,X4)
      | k5_enumset1(X6,X6,X6,X6,X1,X2,X3) != X4 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X0 != X6
      | k5_enumset1(X0,X0,X0,X0,X1,X2,X3) != X4 ) ),
    inference(definition_unfolding,[],[f40,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f37,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f38,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X0 != X6
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ( ( ( sK3(X0,X1,X2,X3,X4) != X3
              & sK3(X0,X1,X2,X3,X4) != X2
              & sK3(X0,X1,X2,X3,X4) != X1
              & sK3(X0,X1,X2,X3,X4) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4),X4) )
          & ( sK3(X0,X1,X2,X3,X4) = X3
            | sK3(X0,X1,X2,X3,X4) = X2
            | sK3(X0,X1,X2,X3,X4) = X1
            | sK3(X0,X1,X2,X3,X4) = X0
            | r2_hidden(sK3(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4) != X3
            & sK3(X0,X1,X2,X3,X4) != X2
            & sK3(X0,X1,X2,X3,X4) != X1
            & sK3(X0,X1,X2,X3,X4) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4),X4) )
        & ( sK3(X0,X1,X2,X3,X4) = X3
          | sK3(X0,X1,X2,X3,X4) = X2
          | sK3(X0,X1,X2,X3,X4) = X1
          | sK3(X0,X1,X2,X3,X4) = X0
          | r2_hidden(sK3(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(f225,plain,
    ( ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f223,f27])).

fof(f223,plain,
    ( ~ r1_tarski(k1_xboole_0,k4_tarski(sK0,sK1))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(resolution,[],[f222,f32])).

fof(f222,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f220,f202])).

fof(f202,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f201,f133])).

fof(f133,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k1_xboole_0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl4_7
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f201,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(k1_xboole_0))
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f101,f128])).

fof(f128,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k2_relat_1(k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl4_6
  <=> k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f101,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_1
  <=> k1_xboole_0 = k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f220,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)))
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(superposition,[],[f208,f128])).

fof(f208,plain,
    ( ! [X5] : r2_hidden(k4_tarski(sK0,X5),k2_zfmisc_1(k1_relat_1(k1_xboole_0),k5_enumset1(X5,X5,X5,X5,X5,X5,X5)))
    | ~ spl4_7 ),
    inference(superposition,[],[f86,f133])).

fof(f86,plain,(
    ! [X2,X0,X1] : r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) ),
    inference(superposition,[],[f69,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) = k5_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f36,f53,f54,f53])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f53])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f51])).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f69,plain,(
    ! [X6,X2,X0,X1] : r2_hidden(X6,k5_enumset1(X0,X0,X0,X0,X1,X2,X6)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X1] :
      ( r2_hidden(X6,X4)
      | k5_enumset1(X0,X0,X0,X0,X1,X2,X6) != X4 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X3 != X6
      | k5_enumset1(X0,X0,X0,X0,X1,X2,X3) != X4 ) ),
    inference(definition_unfolding,[],[f43,f51])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X3 != X6
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f171,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f162,f27])).

fof(f162,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | ~ spl4_5 ),
    inference(superposition,[],[f80,f120])).

fof(f120,plain,
    ( k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_5
  <=> k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f153,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f144,f27])).

fof(f144,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl4_4 ),
    inference(superposition,[],[f80,f116])).

fof(f116,plain,
    ( k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_4
  <=> k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f134,plain,
    ( spl4_4
    | spl4_5
    | spl4_7
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f124,f99,f131,f118,f114])).

fof(f124,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl4_1 ),
    inference(superposition,[],[f30,f101])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f129,plain,
    ( spl4_4
    | spl4_5
    | spl4_6
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f123,f99,f126,f118,f114])).

fof(f123,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl4_1 ),
    inference(superposition,[],[f31,f101])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f121,plain,
    ( spl4_4
    | spl4_5
    | spl4_3 ),
    inference(avatar_split_clause,[],[f112,f107,f118,f114])).

fof(f107,plain,
    ( spl4_3
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f112,plain,
    ( k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl4_3 ),
    inference(trivial_inequality_removal,[],[f111])).

fof(f111,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl4_3 ),
    inference(superposition,[],[f109,f30])).

fof(f109,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f110,plain,
    ( spl4_1
    | spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f97,f107,f103,f99])).

fof(f97,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | k1_xboole_0 = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f96,f30])).

fof(f96,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(forward_demodulation,[],[f85,f56])).

fof(f85,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k5_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(backward_demodulation,[],[f55,f56])).

fof(f55,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k5_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)))) ),
    inference(definition_unfolding,[],[f26,f54,f54,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f26,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))
   => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:44:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (21316)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (21318)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (21333)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (21341)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (21320)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (21317)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (21313)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (21315)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (21333)Refutation not found, incomplete strategy% (21333)------------------------------
% 0.20/0.52  % (21333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (21333)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (21333)Memory used [KB]: 1791
% 0.20/0.52  % (21333)Time elapsed: 0.113 s
% 0.20/0.52  % (21333)------------------------------
% 0.20/0.52  % (21333)------------------------------
% 0.20/0.53  % (21330)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (21335)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (21335)Refutation not found, incomplete strategy% (21335)------------------------------
% 0.20/0.53  % (21335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (21335)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (21335)Memory used [KB]: 1663
% 0.20/0.53  % (21335)Time elapsed: 0.083 s
% 0.20/0.53  % (21335)------------------------------
% 0.20/0.53  % (21335)------------------------------
% 0.20/0.54  % (21323)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (21319)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (21324)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (21312)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (21312)Refutation not found, incomplete strategy% (21312)------------------------------
% 0.20/0.54  % (21312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (21312)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (21312)Memory used [KB]: 1663
% 0.20/0.54  % (21312)Time elapsed: 0.128 s
% 0.20/0.54  % (21312)------------------------------
% 0.20/0.54  % (21312)------------------------------
% 0.20/0.54  % (21314)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (21327)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (21325)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (21327)Refutation not found, incomplete strategy% (21327)------------------------------
% 0.20/0.54  % (21327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (21327)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (21327)Memory used [KB]: 6268
% 0.20/0.54  % (21327)Time elapsed: 0.096 s
% 0.20/0.54  % (21327)------------------------------
% 0.20/0.54  % (21327)------------------------------
% 0.20/0.55  % (21338)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (21321)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (21322)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (21321)Refutation not found, incomplete strategy% (21321)------------------------------
% 0.20/0.55  % (21321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (21321)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (21321)Memory used [KB]: 10618
% 0.20/0.55  % (21321)Time elapsed: 0.125 s
% 0.20/0.55  % (21321)------------------------------
% 0.20/0.55  % (21321)------------------------------
% 0.20/0.55  % (21339)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (21322)Refutation not found, incomplete strategy% (21322)------------------------------
% 0.20/0.55  % (21322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (21322)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (21322)Memory used [KB]: 10618
% 0.20/0.55  % (21322)Time elapsed: 0.093 s
% 0.20/0.55  % (21322)------------------------------
% 0.20/0.55  % (21322)------------------------------
% 0.20/0.55  % (21336)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (21337)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (21315)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f253,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f110,f121,f129,f134,f153,f171,f225,f252])).
% 0.20/0.55  fof(f252,plain,(
% 0.20/0.55    ~spl4_2),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f251])).
% 0.20/0.55  fof(f251,plain,(
% 0.20/0.55    $false | ~spl4_2),
% 0.20/0.55    inference(subsumption_resolution,[],[f239,f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f1])).
% 0.20/0.55  % (21331)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.55  fof(f239,plain,(
% 0.20/0.55    ~r1_tarski(k1_xboole_0,sK2) | ~spl4_2),
% 0.20/0.55    inference(superposition,[],[f80,f105])).
% 0.20/0.55  fof(f105,plain,(
% 0.20/0.55    k1_xboole_0 = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl4_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f103])).
% 0.20/0.55  fof(f103,plain,(
% 0.20/0.55    spl4_2 <=> k1_xboole_0 = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~r1_tarski(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),X0)) )),
% 0.20/0.55    inference(resolution,[],[f75,f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    ( ! [X6,X2,X3,X1] : (r2_hidden(X6,k5_enumset1(X6,X6,X6,X6,X1,X2,X3))) )),
% 0.20/0.55    inference(equality_resolution,[],[f74])).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ( ! [X6,X4,X2,X3,X1] : (r2_hidden(X6,X4) | k5_enumset1(X6,X6,X6,X6,X1,X2,X3) != X4) )),
% 0.20/0.55    inference(equality_resolution,[],[f66])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | X0 != X6 | k5_enumset1(X0,X0,X0,X0,X1,X2,X3) != X4) )),
% 0.20/0.55    inference(definition_unfolding,[],[f40,f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f37,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f38,f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | X0 != X6 | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | (((sK3(X0,X1,X2,X3,X4) != X3 & sK3(X0,X1,X2,X3,X4) != X2 & sK3(X0,X1,X2,X3,X4) != X1 & sK3(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4),X4)) & (sK3(X0,X1,X2,X3,X4) = X3 | sK3(X0,X1,X2,X3,X4) = X2 | sK3(X0,X1,X2,X3,X4) = X1 | sK3(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4))) => (((sK3(X0,X1,X2,X3,X4) != X3 & sK3(X0,X1,X2,X3,X4) != X2 & sK3(X0,X1,X2,X3,X4) != X1 & sK3(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4),X4)) & (sK3(X0,X1,X2,X3,X4) = X3 | sK3(X0,X1,X2,X3,X4) = X2 | sK3(X0,X1,X2,X3,X4) = X1 | sK3(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4),X4))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.20/0.55    inference(rectify,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.20/0.55    inference(flattening,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.20/0.55    inference(nnf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).
% 0.20/0.55  fof(f225,plain,(
% 0.20/0.55    ~spl4_1 | ~spl4_6 | ~spl4_7),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f224])).
% 0.20/0.55  fof(f224,plain,(
% 0.20/0.55    $false | (~spl4_1 | ~spl4_6 | ~spl4_7)),
% 0.20/0.55    inference(subsumption_resolution,[],[f223,f27])).
% 0.20/0.55  fof(f223,plain,(
% 0.20/0.55    ~r1_tarski(k1_xboole_0,k4_tarski(sK0,sK1)) | (~spl4_1 | ~spl4_6 | ~spl4_7)),
% 0.20/0.55    inference(resolution,[],[f222,f32])).
% 0.20/0.55  fof(f222,plain,(
% 0.20/0.55    r2_hidden(k4_tarski(sK0,sK1),k1_xboole_0) | (~spl4_1 | ~spl4_6 | ~spl4_7)),
% 0.20/0.55    inference(forward_demodulation,[],[f220,f202])).
% 0.20/0.55  fof(f202,plain,(
% 0.20/0.55    k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | (~spl4_1 | ~spl4_6 | ~spl4_7)),
% 0.20/0.55    inference(forward_demodulation,[],[f201,f133])).
% 0.20/0.55  fof(f133,plain,(
% 0.20/0.55    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k1_xboole_0) | ~spl4_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f131])).
% 0.20/0.55  fof(f131,plain,(
% 0.20/0.55    spl4_7 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k1_xboole_0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.55  fof(f201,plain,(
% 0.20/0.55    k1_xboole_0 = k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(k1_xboole_0)) | (~spl4_1 | ~spl4_6)),
% 0.20/0.55    inference(forward_demodulation,[],[f101,f128])).
% 0.20/0.55  fof(f128,plain,(
% 0.20/0.55    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k2_relat_1(k1_xboole_0) | ~spl4_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f126])).
% 0.20/0.55  fof(f126,plain,(
% 0.20/0.55    spl4_6 <=> k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k2_relat_1(k1_xboole_0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.55  fof(f101,plain,(
% 0.20/0.55    k1_xboole_0 = k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl4_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f99])).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    spl4_1 <=> k1_xboole_0 = k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.55  fof(f220,plain,(
% 0.20/0.55    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))) | (~spl4_6 | ~spl4_7)),
% 0.20/0.55    inference(superposition,[],[f208,f128])).
% 0.20/0.55  fof(f208,plain,(
% 0.20/0.55    ( ! [X5] : (r2_hidden(k4_tarski(sK0,X5),k2_zfmisc_1(k1_relat_1(k1_xboole_0),k5_enumset1(X5,X5,X5,X5,X5,X5,X5)))) ) | ~spl4_7),
% 0.20/0.55    inference(superposition,[],[f86,f133])).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))) )),
% 0.20/0.55    inference(superposition,[],[f69,f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) = k5_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f36,f53,f54,f53])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f28,f53])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f29,f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f34,f51])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,k5_enumset1(X0,X0,X0,X0,X1,X2,X6))) )),
% 0.20/0.55    inference(equality_resolution,[],[f68])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X6,X4,X2,X0,X1] : (r2_hidden(X6,X4) | k5_enumset1(X0,X0,X0,X0,X1,X2,X6) != X4) )),
% 0.20/0.55    inference(equality_resolution,[],[f63])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | X3 != X6 | k5_enumset1(X0,X0,X0,X0,X1,X2,X3) != X4) )),
% 0.20/0.55    inference(definition_unfolding,[],[f43,f51])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | X3 != X6 | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f171,plain,(
% 0.20/0.55    ~spl4_5),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f170])).
% 0.20/0.55  fof(f170,plain,(
% 0.20/0.55    $false | ~spl4_5),
% 0.20/0.55    inference(subsumption_resolution,[],[f162,f27])).
% 0.20/0.55  fof(f162,plain,(
% 0.20/0.55    ~r1_tarski(k1_xboole_0,sK1) | ~spl4_5),
% 0.20/0.55    inference(superposition,[],[f80,f120])).
% 0.20/0.55  fof(f120,plain,(
% 0.20/0.55    k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl4_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f118])).
% 0.20/0.55  fof(f118,plain,(
% 0.20/0.55    spl4_5 <=> k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.55  fof(f153,plain,(
% 0.20/0.55    ~spl4_4),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f152])).
% 0.20/0.55  fof(f152,plain,(
% 0.20/0.55    $false | ~spl4_4),
% 0.20/0.55    inference(subsumption_resolution,[],[f144,f27])).
% 0.20/0.55  fof(f144,plain,(
% 0.20/0.55    ~r1_tarski(k1_xboole_0,sK0) | ~spl4_4),
% 0.20/0.55    inference(superposition,[],[f80,f116])).
% 0.20/0.55  fof(f116,plain,(
% 0.20/0.55    k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl4_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f114])).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    spl4_4 <=> k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.55  fof(f134,plain,(
% 0.20/0.55    spl4_4 | spl4_5 | spl4_7 | ~spl4_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f124,f99,f131,f118,f114])).
% 0.20/0.55  fof(f124,plain,(
% 0.20/0.55    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl4_1),
% 0.20/0.55    inference(superposition,[],[f30,f101])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.20/0.55  fof(f129,plain,(
% 0.20/0.55    spl4_4 | spl4_5 | spl4_6 | ~spl4_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f123,f99,f126,f118,f114])).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k2_relat_1(k1_xboole_0) | k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl4_1),
% 0.20/0.55    inference(superposition,[],[f31,f101])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f121,plain,(
% 0.20/0.55    spl4_4 | spl4_5 | spl4_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f112,f107,f118,f114])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    spl4_3 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.55  fof(f112,plain,(
% 0.20/0.55    k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl4_3),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f111])).
% 0.20/0.55  fof(f111,plain,(
% 0.20/0.55    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl4_3),
% 0.20/0.55    inference(superposition,[],[f109,f30])).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | spl4_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f107])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    spl4_1 | spl4_2 | ~spl4_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f97,f107,f103,f99])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | k1_xboole_0 = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 = k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.55    inference(superposition,[],[f96,f30])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 0.20/0.55    inference(forward_demodulation,[],[f85,f56])).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k5_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 0.20/0.55    inference(backward_demodulation,[],[f55,f56])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k5_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),
% 0.20/0.55    inference(definition_unfolding,[],[f26,f54,f54,f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.20/0.55    inference(ennf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.20/0.55    inference(negated_conjecture,[],[f13])).
% 0.20/0.55  fof(f13,conjecture,(
% 0.20/0.55    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (21315)------------------------------
% 0.20/0.55  % (21315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (21315)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (21315)Memory used [KB]: 10874
% 0.20/0.55  % (21315)Time elapsed: 0.131 s
% 0.20/0.55  % (21315)------------------------------
% 0.20/0.55  % (21315)------------------------------
% 0.20/0.55  % (21311)Success in time 0.185 s
%------------------------------------------------------------------------------
