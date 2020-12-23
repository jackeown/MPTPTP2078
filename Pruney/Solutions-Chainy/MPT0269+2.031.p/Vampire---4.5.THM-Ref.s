%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:51 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 123 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :  270 ( 393 expanded)
%              Number of equality atoms :   65 ( 126 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f859,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f92,f106,f110,f119,f139,f147,f191,f297,f656,f693,f770,f858])).

fof(f858,plain,
    ( ~ spl3_7
    | ~ spl3_10
    | spl3_64
    | ~ spl3_68
    | ~ spl3_73 ),
    inference(avatar_contradiction_clause,[],[f857])).

fof(f857,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_10
    | spl3_64
    | ~ spl3_68
    | ~ spl3_73 ),
    inference(subsumption_resolution,[],[f699,f837])).

fof(f837,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK0)
    | ~ spl3_7
    | ~ spl3_68
    | ~ spl3_73 ),
    inference(unit_resulting_resolution,[],[f91,f769,f692])).

fof(f692,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,k1_tarski(X3))
        | r2_hidden(X3,X2)
        | k1_xboole_0 = X2 )
    | ~ spl3_68 ),
    inference(avatar_component_clause,[],[f691])).

fof(f691,plain,
    ( spl3_68
  <=> ! [X3,X2] :
        ( k1_xboole_0 = X2
        | r2_hidden(X3,X2)
        | ~ r1_tarski(X2,k1_tarski(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f769,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(X0,sK0))
    | ~ spl3_73 ),
    inference(avatar_component_clause,[],[f768])).

fof(f768,plain,
    ( spl3_73
  <=> ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(X0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f91,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_7
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f699,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK1),sK0)
    | ~ spl3_10
    | spl3_64 ),
    inference(unit_resulting_resolution,[],[f655,f105])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f655,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK0)
    | spl3_64 ),
    inference(avatar_component_clause,[],[f653])).

fof(f653,plain,
    ( spl3_64
  <=> r1_tarski(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f770,plain,
    ( spl3_73
    | ~ spl3_13
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f299,f294,f117,f768])).

fof(f117,plain,
    ( spl3_13
  <=> ! [X1,X0,X4] :
        ( ~ r2_hidden(X4,X1)
        | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f294,plain,
    ( spl3_31
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f299,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(X0,sK0))
    | ~ spl3_13
    | ~ spl3_31 ),
    inference(unit_resulting_resolution,[],[f296,f118])).

fof(f118,plain,
    ( ! [X4,X0,X1] :
        ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
        | ~ r2_hidden(X4,X1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f117])).

fof(f296,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f294])).

fof(f693,plain,
    ( spl3_68
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f203,f145,f108,f691])).

fof(f108,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f145,plain,
    ( spl3_20
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f203,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = X2
        | r2_hidden(X3,X2)
        | ~ r1_tarski(X2,k1_tarski(X3)) )
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(superposition,[],[f146,f109])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f145])).

fof(f656,plain,
    ( ~ spl3_64
    | spl3_2
    | ~ spl3_18
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f238,f188,f137,f68,f653])).

fof(f68,plain,
    ( spl3_2
  <=> sK0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f137,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f188,plain,
    ( spl3_22
  <=> r1_tarski(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f238,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK0)
    | spl3_2
    | ~ spl3_18
    | ~ spl3_22 ),
    inference(unit_resulting_resolution,[],[f70,f190,f138])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f137])).

fof(f190,plain,
    ( r1_tarski(sK0,k1_tarski(sK1))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f188])).

fof(f70,plain,
    ( sK0 != k1_tarski(sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f297,plain,
    ( spl3_31
    | spl3_1
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f202,f145,f73,f63,f294])).

fof(f63,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f73,plain,
    ( spl3_3
  <=> k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f202,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(superposition,[],[f146,f75])).

fof(f75,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f191,plain,
    ( spl3_22
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f149,f104,f73,f188])).

fof(f149,plain,
    ( r1_tarski(sK0,k1_tarski(sK1))
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f75,f105])).

fof(f147,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f48,f145])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f139,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f44,f137])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f119,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f60,f117])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f110,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f46,f108])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f106,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f45,f104])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f92,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f36,f90])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f76,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f30,f73])).

fof(f30,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK0 != k1_tarski(sK1)
    & k1_xboole_0 != sK0
    & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( sK0 != k1_tarski(sK1)
      & k1_xboole_0 != sK0
      & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f71,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f32,f68])).

fof(f32,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f31,f63])).

fof(f31,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:10:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (15340)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (15333)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (15336)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (15348)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (15338)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (15337)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (15349)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (15349)Refutation not found, incomplete strategy% (15349)------------------------------
% 0.21/0.51  % (15349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15349)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15349)Memory used [KB]: 10618
% 0.21/0.51  % (15349)Time elapsed: 0.119 s
% 0.21/0.51  % (15349)------------------------------
% 0.21/0.51  % (15349)------------------------------
% 0.21/0.51  % (15335)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (15343)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (15347)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (15360)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (15361)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (15334)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (15354)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (15341)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (15339)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (15352)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (15353)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (15351)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (15334)Refutation not found, incomplete strategy% (15334)------------------------------
% 0.21/0.52  % (15334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (15334)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (15334)Memory used [KB]: 1663
% 1.28/0.53  % (15334)Time elapsed: 0.116 s
% 1.28/0.53  % (15334)------------------------------
% 1.28/0.53  % (15334)------------------------------
% 1.28/0.53  % (15358)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.28/0.53  % (15346)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.28/0.53  % (15344)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.28/0.53  % (15345)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.28/0.53  % (15350)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.28/0.53  % (15342)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.28/0.53  % (15345)Refutation not found, incomplete strategy% (15345)------------------------------
% 1.28/0.53  % (15345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (15345)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (15345)Memory used [KB]: 10618
% 1.28/0.53  % (15345)Time elapsed: 0.133 s
% 1.28/0.53  % (15345)------------------------------
% 1.28/0.53  % (15345)------------------------------
% 1.28/0.54  % (15355)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.28/0.54  % (15359)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.28/0.54  % (15362)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.28/0.54  % (15362)Refutation not found, incomplete strategy% (15362)------------------------------
% 1.28/0.54  % (15362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (15362)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (15362)Memory used [KB]: 1663
% 1.28/0.54  % (15362)Time elapsed: 0.002 s
% 1.28/0.54  % (15362)------------------------------
% 1.28/0.54  % (15362)------------------------------
% 1.28/0.55  % (15356)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.28/0.55  % (15357)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.52/0.63  % (15333)Refutation not found, incomplete strategy% (15333)------------------------------
% 1.52/0.63  % (15333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.64  % (15333)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.64  
% 1.52/0.64  % (15333)Memory used [KB]: 1663
% 1.52/0.64  % (15333)Time elapsed: 0.232 s
% 1.52/0.64  % (15333)------------------------------
% 1.52/0.64  % (15333)------------------------------
% 1.52/0.64  % (15364)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.12/0.65  % (15336)Refutation not found, incomplete strategy% (15336)------------------------------
% 2.12/0.65  % (15336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.65  % (15336)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.65  
% 2.12/0.65  % (15336)Memory used [KB]: 6140
% 2.12/0.65  % (15336)Time elapsed: 0.239 s
% 2.12/0.65  % (15336)------------------------------
% 2.12/0.65  % (15336)------------------------------
% 2.12/0.66  % (15348)Refutation not found, incomplete strategy% (15348)------------------------------
% 2.12/0.66  % (15348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.66  % (15348)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.66  
% 2.12/0.66  % (15348)Memory used [KB]: 6140
% 2.12/0.66  % (15348)Time elapsed: 0.265 s
% 2.12/0.66  % (15348)------------------------------
% 2.12/0.66  % (15348)------------------------------
% 2.12/0.67  % (15363)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.40/0.69  % (15365)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.40/0.69  % (15365)Refutation not found, incomplete strategy% (15365)------------------------------
% 2.40/0.69  % (15365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.40/0.69  % (15365)Termination reason: Refutation not found, incomplete strategy
% 2.40/0.69  
% 2.40/0.69  % (15365)Memory used [KB]: 6140
% 2.40/0.69  % (15365)Time elapsed: 0.096 s
% 2.40/0.69  % (15365)------------------------------
% 2.40/0.69  % (15365)------------------------------
% 2.40/0.69  % (15366)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.40/0.72  % (15363)Refutation found. Thanks to Tanya!
% 2.40/0.72  % SZS status Theorem for theBenchmark
% 2.40/0.72  % SZS output start Proof for theBenchmark
% 2.40/0.72  fof(f859,plain,(
% 2.40/0.72    $false),
% 2.40/0.72    inference(avatar_sat_refutation,[],[f66,f71,f76,f92,f106,f110,f119,f139,f147,f191,f297,f656,f693,f770,f858])).
% 2.40/0.72  fof(f858,plain,(
% 2.40/0.72    ~spl3_7 | ~spl3_10 | spl3_64 | ~spl3_68 | ~spl3_73),
% 2.40/0.72    inference(avatar_contradiction_clause,[],[f857])).
% 2.40/0.72  fof(f857,plain,(
% 2.40/0.72    $false | (~spl3_7 | ~spl3_10 | spl3_64 | ~spl3_68 | ~spl3_73)),
% 2.40/0.72    inference(subsumption_resolution,[],[f699,f837])).
% 2.40/0.72  fof(f837,plain,(
% 2.40/0.72    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK0) | (~spl3_7 | ~spl3_68 | ~spl3_73)),
% 2.40/0.72    inference(unit_resulting_resolution,[],[f91,f769,f692])).
% 2.40/0.72  fof(f692,plain,(
% 2.40/0.72    ( ! [X2,X3] : (~r1_tarski(X2,k1_tarski(X3)) | r2_hidden(X3,X2) | k1_xboole_0 = X2) ) | ~spl3_68),
% 2.40/0.72    inference(avatar_component_clause,[],[f691])).
% 2.40/0.72  fof(f691,plain,(
% 2.40/0.72    spl3_68 <=> ! [X3,X2] : (k1_xboole_0 = X2 | r2_hidden(X3,X2) | ~r1_tarski(X2,k1_tarski(X3)))),
% 2.40/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 2.40/0.72  fof(f769,plain,(
% 2.40/0.72    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(X0,sK0))) ) | ~spl3_73),
% 2.40/0.72    inference(avatar_component_clause,[],[f768])).
% 2.40/0.72  fof(f768,plain,(
% 2.40/0.72    spl3_73 <=> ! [X0] : ~r2_hidden(sK1,k4_xboole_0(X0,sK0))),
% 2.40/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 2.40/0.72  fof(f91,plain,(
% 2.40/0.72    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_7),
% 2.40/0.72    inference(avatar_component_clause,[],[f90])).
% 2.40/0.72  fof(f90,plain,(
% 2.40/0.72    spl3_7 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.40/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.40/0.72  fof(f699,plain,(
% 2.40/0.72    k1_xboole_0 != k4_xboole_0(k1_tarski(sK1),sK0) | (~spl3_10 | spl3_64)),
% 2.40/0.72    inference(unit_resulting_resolution,[],[f655,f105])).
% 2.40/0.72  fof(f105,plain,(
% 2.40/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) ) | ~spl3_10),
% 2.40/0.72    inference(avatar_component_clause,[],[f104])).
% 2.40/0.72  fof(f104,plain,(
% 2.40/0.72    spl3_10 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 2.40/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.40/0.72  fof(f655,plain,(
% 2.40/0.72    ~r1_tarski(k1_tarski(sK1),sK0) | spl3_64),
% 2.40/0.72    inference(avatar_component_clause,[],[f653])).
% 2.40/0.72  fof(f653,plain,(
% 2.40/0.72    spl3_64 <=> r1_tarski(k1_tarski(sK1),sK0)),
% 2.40/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 2.40/0.72  fof(f770,plain,(
% 2.40/0.72    spl3_73 | ~spl3_13 | ~spl3_31),
% 2.40/0.72    inference(avatar_split_clause,[],[f299,f294,f117,f768])).
% 2.40/0.72  fof(f117,plain,(
% 2.40/0.72    spl3_13 <=> ! [X1,X0,X4] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1)))),
% 2.40/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.40/0.72  fof(f294,plain,(
% 2.40/0.72    spl3_31 <=> r2_hidden(sK1,sK0)),
% 2.40/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 2.40/0.72  fof(f299,plain,(
% 2.40/0.72    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(X0,sK0))) ) | (~spl3_13 | ~spl3_31)),
% 2.40/0.72    inference(unit_resulting_resolution,[],[f296,f118])).
% 2.40/0.72  fof(f118,plain,(
% 2.40/0.72    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) ) | ~spl3_13),
% 2.40/0.72    inference(avatar_component_clause,[],[f117])).
% 2.40/0.72  fof(f296,plain,(
% 2.40/0.72    r2_hidden(sK1,sK0) | ~spl3_31),
% 2.40/0.72    inference(avatar_component_clause,[],[f294])).
% 2.40/0.72  fof(f693,plain,(
% 2.40/0.72    spl3_68 | ~spl3_11 | ~spl3_20),
% 2.40/0.72    inference(avatar_split_clause,[],[f203,f145,f108,f691])).
% 2.40/0.72  fof(f108,plain,(
% 2.40/0.72    spl3_11 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 2.40/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.40/0.72  fof(f145,plain,(
% 2.40/0.72    spl3_20 <=> ! [X1,X0] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0))),
% 2.40/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 2.40/0.72  fof(f203,plain,(
% 2.40/0.72    ( ! [X2,X3] : (k1_xboole_0 = X2 | r2_hidden(X3,X2) | ~r1_tarski(X2,k1_tarski(X3))) ) | (~spl3_11 | ~spl3_20)),
% 2.40/0.72    inference(superposition,[],[f146,f109])).
% 2.40/0.72  fof(f109,plain,(
% 2.40/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) ) | ~spl3_11),
% 2.40/0.72    inference(avatar_component_clause,[],[f108])).
% 2.40/0.72  fof(f146,plain,(
% 2.40/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) ) | ~spl3_20),
% 2.40/0.72    inference(avatar_component_clause,[],[f145])).
% 2.40/0.72  fof(f656,plain,(
% 2.40/0.72    ~spl3_64 | spl3_2 | ~spl3_18 | ~spl3_22),
% 2.40/0.72    inference(avatar_split_clause,[],[f238,f188,f137,f68,f653])).
% 2.40/0.72  fof(f68,plain,(
% 2.40/0.72    spl3_2 <=> sK0 = k1_tarski(sK1)),
% 2.40/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.40/0.72  fof(f137,plain,(
% 2.40/0.72    spl3_18 <=> ! [X1,X0] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))),
% 2.40/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.40/0.72  fof(f188,plain,(
% 2.40/0.72    spl3_22 <=> r1_tarski(sK0,k1_tarski(sK1))),
% 2.40/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 2.40/0.72  fof(f238,plain,(
% 2.40/0.72    ~r1_tarski(k1_tarski(sK1),sK0) | (spl3_2 | ~spl3_18 | ~spl3_22)),
% 2.40/0.72    inference(unit_resulting_resolution,[],[f70,f190,f138])).
% 2.40/0.72  fof(f138,plain,(
% 2.40/0.72    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) ) | ~spl3_18),
% 2.40/0.72    inference(avatar_component_clause,[],[f137])).
% 2.40/0.72  fof(f190,plain,(
% 2.40/0.72    r1_tarski(sK0,k1_tarski(sK1)) | ~spl3_22),
% 2.40/0.72    inference(avatar_component_clause,[],[f188])).
% 2.40/0.72  fof(f70,plain,(
% 2.40/0.72    sK0 != k1_tarski(sK1) | spl3_2),
% 2.40/0.72    inference(avatar_component_clause,[],[f68])).
% 2.40/0.72  fof(f297,plain,(
% 2.40/0.72    spl3_31 | spl3_1 | ~spl3_3 | ~spl3_20),
% 2.40/0.72    inference(avatar_split_clause,[],[f202,f145,f73,f63,f294])).
% 2.40/0.72  fof(f63,plain,(
% 2.40/0.72    spl3_1 <=> k1_xboole_0 = sK0),
% 2.40/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.40/0.72  fof(f73,plain,(
% 2.40/0.72    spl3_3 <=> k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 2.40/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.40/0.72  fof(f202,plain,(
% 2.40/0.72    k1_xboole_0 = sK0 | r2_hidden(sK1,sK0) | (~spl3_3 | ~spl3_20)),
% 2.40/0.72    inference(superposition,[],[f146,f75])).
% 2.40/0.72  fof(f75,plain,(
% 2.40/0.72    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~spl3_3),
% 2.40/0.72    inference(avatar_component_clause,[],[f73])).
% 2.40/0.72  fof(f191,plain,(
% 2.40/0.72    spl3_22 | ~spl3_3 | ~spl3_10),
% 2.40/0.72    inference(avatar_split_clause,[],[f149,f104,f73,f188])).
% 2.40/0.72  fof(f149,plain,(
% 2.40/0.72    r1_tarski(sK0,k1_tarski(sK1)) | (~spl3_3 | ~spl3_10)),
% 2.40/0.72    inference(unit_resulting_resolution,[],[f75,f105])).
% 2.40/0.72  fof(f147,plain,(
% 2.40/0.72    spl3_20),
% 2.40/0.72    inference(avatar_split_clause,[],[f48,f145])).
% 2.40/0.72  fof(f48,plain,(
% 2.40/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 2.40/0.72    inference(cnf_transformation,[],[f24])).
% 2.40/0.72  fof(f24,plain,(
% 2.40/0.72    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 2.40/0.72    inference(nnf_transformation,[],[f15])).
% 2.40/0.72  fof(f15,axiom,(
% 2.40/0.72    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.40/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 2.40/0.72  fof(f139,plain,(
% 2.40/0.72    spl3_18),
% 2.40/0.72    inference(avatar_split_clause,[],[f44,f137])).
% 2.40/0.72  fof(f44,plain,(
% 2.40/0.72    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.40/0.72    inference(cnf_transformation,[],[f22])).
% 2.40/0.72  fof(f22,plain,(
% 2.40/0.72    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.40/0.72    inference(flattening,[],[f21])).
% 2.40/0.72  fof(f21,plain,(
% 2.40/0.72    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.40/0.72    inference(nnf_transformation,[],[f3])).
% 2.40/0.72  fof(f3,axiom,(
% 2.40/0.72    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.40/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.40/0.72  fof(f119,plain,(
% 2.40/0.72    spl3_13),
% 2.40/0.72    inference(avatar_split_clause,[],[f60,f117])).
% 2.40/0.72  fof(f60,plain,(
% 2.40/0.72    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.40/0.72    inference(equality_resolution,[],[f52])).
% 2.40/0.72  fof(f52,plain,(
% 2.40/0.72    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.40/0.72    inference(cnf_transformation,[],[f29])).
% 2.40/0.72  fof(f29,plain,(
% 2.40/0.72    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.40/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 2.40/0.72  fof(f28,plain,(
% 2.40/0.72    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.40/0.72    introduced(choice_axiom,[])).
% 2.40/0.72  fof(f27,plain,(
% 2.40/0.72    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.40/0.72    inference(rectify,[],[f26])).
% 2.40/0.72  fof(f26,plain,(
% 2.40/0.72    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.40/0.72    inference(flattening,[],[f25])).
% 2.40/0.72  fof(f25,plain,(
% 2.40/0.72    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.40/0.72    inference(nnf_transformation,[],[f1])).
% 2.40/0.72  fof(f1,axiom,(
% 2.40/0.72    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.40/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.40/0.72  fof(f110,plain,(
% 2.40/0.72    spl3_11),
% 2.40/0.72    inference(avatar_split_clause,[],[f46,f108])).
% 2.40/0.72  fof(f46,plain,(
% 2.40/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.40/0.72    inference(cnf_transformation,[],[f23])).
% 2.40/0.72  fof(f23,plain,(
% 2.40/0.72    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.40/0.72    inference(nnf_transformation,[],[f4])).
% 2.40/0.72  fof(f4,axiom,(
% 2.40/0.72    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.40/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.40/0.72  fof(f106,plain,(
% 2.40/0.72    spl3_10),
% 2.40/0.72    inference(avatar_split_clause,[],[f45,f104])).
% 2.40/0.72  fof(f45,plain,(
% 2.40/0.72    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.40/0.72    inference(cnf_transformation,[],[f23])).
% 2.40/0.72  fof(f92,plain,(
% 2.40/0.72    spl3_7),
% 2.40/0.72    inference(avatar_split_clause,[],[f36,f90])).
% 2.40/0.72  fof(f36,plain,(
% 2.40/0.72    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.40/0.72    inference(cnf_transformation,[],[f7])).
% 2.40/0.72  fof(f7,axiom,(
% 2.40/0.72    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.40/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.40/0.72  fof(f76,plain,(
% 2.40/0.72    spl3_3),
% 2.40/0.72    inference(avatar_split_clause,[],[f30,f73])).
% 2.40/0.72  fof(f30,plain,(
% 2.40/0.72    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 2.40/0.72    inference(cnf_transformation,[],[f20])).
% 2.40/0.72  fof(f20,plain,(
% 2.40/0.72    sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 2.40/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 2.40/0.72  fof(f19,plain,(
% 2.40/0.72    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 2.40/0.72    introduced(choice_axiom,[])).
% 2.40/0.72  fof(f18,plain,(
% 2.40/0.72    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 2.40/0.72    inference(ennf_transformation,[],[f17])).
% 2.40/0.72  fof(f17,negated_conjecture,(
% 2.40/0.72    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 2.40/0.72    inference(negated_conjecture,[],[f16])).
% 2.40/0.72  fof(f16,conjecture,(
% 2.40/0.72    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 2.40/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 2.40/0.72  fof(f71,plain,(
% 2.40/0.72    ~spl3_2),
% 2.40/0.72    inference(avatar_split_clause,[],[f32,f68])).
% 2.40/0.72  fof(f32,plain,(
% 2.40/0.72    sK0 != k1_tarski(sK1)),
% 2.40/0.72    inference(cnf_transformation,[],[f20])).
% 2.40/0.72  fof(f66,plain,(
% 2.40/0.72    ~spl3_1),
% 2.40/0.72    inference(avatar_split_clause,[],[f31,f63])).
% 2.40/0.72  fof(f31,plain,(
% 2.40/0.72    k1_xboole_0 != sK0),
% 2.40/0.72    inference(cnf_transformation,[],[f20])).
% 2.40/0.72  % SZS output end Proof for theBenchmark
% 2.40/0.72  % (15363)------------------------------
% 2.40/0.72  % (15363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.40/0.72  % (15363)Termination reason: Refutation
% 2.40/0.72  
% 2.40/0.72  % (15363)Memory used [KB]: 6780
% 2.40/0.72  % (15363)Time elapsed: 0.135 s
% 2.40/0.72  % (15363)------------------------------
% 2.40/0.72  % (15363)------------------------------
% 2.40/0.72  % (15332)Success in time 0.361 s
%------------------------------------------------------------------------------
