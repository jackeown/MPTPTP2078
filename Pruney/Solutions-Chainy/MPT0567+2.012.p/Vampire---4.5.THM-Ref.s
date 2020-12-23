%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 234 expanded)
%              Number of leaves         :   15 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  189 (1261 expanded)
%              Number of equality atoms :   28 ( 128 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f144,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f42,f116,f120,f141,f143])).

fof(f143,plain,
    ( spl5_5
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f142,f111,f40,f114])).

fof(f114,plain,
    ( spl5_5
  <=> k1_xboole_0 = k10_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f40,plain,
    ( spl5_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f111,plain,
    ( spl5_4
  <=> ! [X0] : ~ r2_hidden(sK1(sK0,k10_relat_1(sK0,k1_xboole_0),k1_xboole_0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f142,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f112,f95])).

fof(f95,plain,
    ( ! [X2] :
        ( r2_hidden(sK1(sK0,k10_relat_1(sK0,k1_xboole_0),X2),X2)
        | k10_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0)) = X2 )
    | ~ spl5_2 ),
    inference(resolution,[],[f93,f50])).

fof(f50,plain,
    ( ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0))
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0))
        | ~ r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f48,f47])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK0,X1,X0),X1)
        | ~ r2_hidden(X0,k10_relat_1(sK0,X1)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f33,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | r2_hidden(sK3(X0,X1,X6),X1) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f16,f15,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f48,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(sK0,k1_xboole_0,X0),X1)
        | ~ r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f47,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f31,f22])).

fof(f22,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f93,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(sK0,X0,X1),X0)
        | r2_hidden(sK1(sK0,X0,X1),X1)
        | k10_relat_1(sK0,X0) = X1 )
    | ~ spl5_2 ),
    inference(resolution,[],[f27,f41])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f112,plain,
    ( ! [X0] : ~ r2_hidden(sK1(sK0,k10_relat_1(sK0,k1_xboole_0),k1_xboole_0),X0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f141,plain,
    ( k1_xboole_0 != k10_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0))
    | k10_relat_1(sK0,k1_xboole_0) != k10_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0))
    | k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f120,plain,
    ( spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f103,f40,f118])).

fof(f118,plain,
    ( spl5_6
  <=> k10_relat_1(sK0,k1_xboole_0) = k10_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f103,plain,
    ( k10_relat_1(sK0,k1_xboole_0) = k10_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0))
    | ~ spl5_2 ),
    inference(resolution,[],[f95,f50])).

fof(f116,plain,
    ( spl5_4
    | spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f102,f40,f114,f111])).

fof(f102,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k10_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0))
        | ~ r2_hidden(sK1(sK0,k10_relat_1(sK0,k1_xboole_0),k1_xboole_0),X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f95,f43])).

fof(f42,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f20,f40])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

fof(f38,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f21,f36])).

fof(f36,plain,
    ( spl5_1
  <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f21,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (14994)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (14994)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (15005)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f38,f42,f116,f120,f141,f143])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    spl5_5 | ~spl5_2 | ~spl5_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f142,f111,f40,f114])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    spl5_5 <=> k1_xboole_0 = k10_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    spl5_2 <=> v1_relat_1(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    spl5_4 <=> ! [X0] : ~r2_hidden(sK1(sK0,k10_relat_1(sK0,k1_xboole_0),k1_xboole_0),X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    k1_xboole_0 = k10_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0)) | (~spl5_2 | ~spl5_4)),
% 0.20/0.47    inference(resolution,[],[f112,f95])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    ( ! [X2] : (r2_hidden(sK1(sK0,k10_relat_1(sK0,k1_xboole_0),X2),X2) | k10_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0)) = X2) ) | ~spl5_2),
% 0.20/0.47    inference(resolution,[],[f93,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0))) ) | ~spl5_2),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0)) | ~r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0))) ) | ~spl5_2),
% 0.20/0.47    inference(resolution,[],[f48,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X1,X0),X1) | ~r2_hidden(X0,k10_relat_1(sK0,X1))) ) | ~spl5_2),
% 0.20/0.47    inference(resolution,[],[f33,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    v1_relat_1(sK0) | ~spl5_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f40])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X6,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X6,k10_relat_1(X0,X1)) | r2_hidden(sK3(X0,X1,X6),X1)) )),
% 0.20/0.47    inference(equality_resolution,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f16,f15,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(rectify,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(sK3(sK0,k1_xboole_0,X0),X1) | ~r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0))) ) | ~spl5_2),
% 0.20/0.47    inference(resolution,[],[f47,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(resolution,[],[f31,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(rectify,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(sK2(sK0,X0,X1),X0) | r2_hidden(sK1(sK0,X0,X1),X1) | k10_relat_1(sK0,X0) = X1) ) | ~spl5_2),
% 0.20/0.47    inference(resolution,[],[f27,f41])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(sK1(sK0,k10_relat_1(sK0,k1_xboole_0),k1_xboole_0),X0)) ) | ~spl5_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f111])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    k1_xboole_0 != k10_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0)) | k10_relat_1(sK0,k1_xboole_0) != k10_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0)) | k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)),
% 0.20/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    spl5_6 | ~spl5_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f103,f40,f118])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    spl5_6 <=> k10_relat_1(sK0,k1_xboole_0) = k10_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    k10_relat_1(sK0,k1_xboole_0) = k10_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0)) | ~spl5_2),
% 0.20/0.47    inference(resolution,[],[f95,f50])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    spl5_4 | spl5_5 | ~spl5_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f102,f40,f114,f111])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0)) | ~r2_hidden(sK1(sK0,k10_relat_1(sK0,k1_xboole_0),k1_xboole_0),X0)) ) | ~spl5_2),
% 0.20/0.47    inference(resolution,[],[f95,f43])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    spl5_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f40])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    v1_relat_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.20/0.47    inference(negated_conjecture,[],[f4])).
% 0.20/0.47  fof(f4,conjecture,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ~spl5_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f21,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    spl5_1 <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (14994)------------------------------
% 0.20/0.47  % (14994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (14994)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (14994)Memory used [KB]: 10618
% 0.20/0.47  % (14994)Time elapsed: 0.057 s
% 0.20/0.47  % (14994)------------------------------
% 0.20/0.47  % (14994)------------------------------
% 0.20/0.47  % (15007)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.48  % (14987)Success in time 0.118 s
%------------------------------------------------------------------------------
