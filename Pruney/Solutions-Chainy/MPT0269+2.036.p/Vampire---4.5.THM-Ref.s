%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 219 expanded)
%              Number of leaves         :   14 (  66 expanded)
%              Depth                    :   17
%              Number of atoms          :  337 (1226 expanded)
%              Number of equality atoms :  130 ( 473 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f226,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f90,f102,f120,f195,f225])).

fof(f225,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f44,f196])).

fof(f196,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(superposition,[],[f194,f54])).

fof(f54,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_3
  <=> k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f194,plain,
    ( ! [X3] : sK0 = k4_xboole_0(sK0,X3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl4_8
  <=> ! [X3] : sK0 = k4_xboole_0(sK0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f44,plain,
    ( k1_xboole_0 != sK0
    | spl4_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f195,plain,
    ( spl4_8
    | spl4_6
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f189,f118,f52,f99,f193])).

fof(f99,plain,
    ( spl4_6
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f118,plain,
    ( spl4_7
  <=> ! [X3] :
        ( sK1 = X3
        | ~ r2_hidden(X3,sK0)
        | sK0 = k1_tarski(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f189,plain,
    ( ! [X3] :
        ( r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,X3) )
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( ! [X3] :
        ( r2_hidden(sK1,sK0)
        | r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,X3)
        | sK0 = k4_xboole_0(sK0,X3) )
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(superposition,[],[f26,f164])).

fof(f164,plain,
    ( ! [X11] :
        ( sK1 = sK2(sK0,X11,sK0)
        | sK0 = k4_xboole_0(sK0,X11) )
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,
    ( ! [X11] :
        ( sK1 = sK2(sK0,X11,sK0)
        | sK0 = k4_xboole_0(sK0,X11)
        | sK1 = sK2(sK0,X11,sK0) )
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(resolution,[],[f148,f146])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | sK1 = X0 )
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | sK1 = X0
        | sK1 = X0 )
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(resolution,[],[f142,f40])).

fof(f40,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f142,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_tarski(sK1))
        | ~ r2_hidden(X0,sK0)
        | sK1 = X0 )
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f139])).

fof(f139,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | r2_hidden(X0,k1_tarski(sK1))
        | ~ r2_hidden(X0,sK0)
        | sK1 = X0 )
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(superposition,[],[f125,f54])).

fof(f125,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 != k4_xboole_0(sK0,X4)
        | r2_hidden(X3,X4)
        | ~ r2_hidden(X3,sK0)
        | sK1 = X3 )
    | ~ spl4_7 ),
    inference(superposition,[],[f29,f119])).

fof(f119,plain,
    ( ! [X3] :
        ( sK0 = k1_tarski(X3)
        | ~ r2_hidden(X3,sK0)
        | sK1 = X3 )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f148,plain,
    ( ! [X2,X1] :
        ( r2_hidden(sK2(X1,X2,sK0),X1)
        | sK1 = sK2(X1,X2,sK0)
        | sK0 = k4_xboole_0(X1,X2) )
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(resolution,[],[f146,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).

fof(f13,plain,(
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

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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

fof(f120,plain,
    ( spl4_7
    | spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f108,f52,f99,f118])).

fof(f108,plain,
    ( ! [X3] :
        ( r2_hidden(sK1,sK0)
        | sK1 = X3
        | sK0 = k1_tarski(X3)
        | ~ r2_hidden(X3,sK0) )
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
    ( ! [X3] :
        ( r2_hidden(sK1,sK0)
        | sK1 = X3
        | sK0 = k1_tarski(X3)
        | ~ r2_hidden(X3,sK0)
        | sK0 = k1_tarski(X3) )
    | ~ spl4_3 ),
    inference(superposition,[],[f33,f93])).

fof(f93,plain,
    ( ! [X0] :
        ( sK1 = sK3(X0,sK0)
        | ~ r2_hidden(X0,sK0)
        | k1_tarski(X0) = sK0 )
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,
    ( ! [X0] :
        ( X0 != X0
        | k1_tarski(X0) = sK0
        | ~ r2_hidden(X0,sK0)
        | sK1 = sK3(X0,sK0) )
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,
    ( ! [X0] :
        ( X0 != X0
        | k1_tarski(X0) = sK0
        | ~ r2_hidden(X0,sK0)
        | k1_tarski(X0) = sK0
        | sK1 = sK3(X0,sK0) )
    | ~ spl4_3 ),
    inference(superposition,[],[f34,f81])).

fof(f81,plain,
    ( ! [X0] :
        ( sK3(X0,sK0) = X0
        | k1_tarski(X0) = sK0
        | sK1 = sK3(X0,sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f80,f69])).

fof(f69,plain,(
    ! [X7] : ~ r2_hidden(X7,k1_xboole_0) ),
    inference(condensation,[],[f68])).

fof(f68,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,k1_xboole_0)
      | ~ r2_hidden(X7,X6) ) ),
    inference(condensation,[],[f67])).

fof(f67,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,k1_xboole_0)
      | ~ r2_hidden(X7,X6)
      | ~ r2_hidden(X5,X6) ) ),
    inference(superposition,[],[f36,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,
    ( ! [X9] :
        ( r2_hidden(sK3(X9,sK0),k1_xboole_0)
        | sK0 = k1_tarski(X9)
        | sK3(X9,sK0) = X9
        | sK1 = sK3(X9,sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f33,f75])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,k1_xboole_0)
        | sK1 = X0 )
    | ~ spl4_3 ),
    inference(resolution,[],[f72,f40])).

fof(f72,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_tarski(sK1))
        | r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_3 ),
    inference(superposition,[],[f35,f54])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X0
      | k1_tarski(X0) = X1
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | sK3(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f102,plain,
    ( ~ spl4_6
    | spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f97,f87,f47,f99])).

fof(f47,plain,
    ( spl4_2
  <=> sK0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f87,plain,
    ( spl4_5
  <=> sK1 = sK3(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f97,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ r2_hidden(sK1,sK0)
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f95])).

fof(f95,plain,
    ( sK1 != sK1
    | sK0 = k1_tarski(sK1)
    | ~ r2_hidden(sK1,sK0)
    | ~ spl4_5 ),
    inference(superposition,[],[f34,f89])).

fof(f89,plain,
    ( sK1 = sK3(sK1,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f90,plain,
    ( spl4_5
    | spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f85,f52,f47,f87])).

fof(f85,plain,
    ( sK0 = k1_tarski(sK1)
    | sK1 = sK3(sK1,sK0)
    | ~ spl4_3 ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_tarski(X0) = sK0
        | sK1 = sK3(X0,sK0) )
    | ~ spl4_3 ),
    inference(equality_factoring,[],[f81])).

fof(f55,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f20,f52])).

fof(f20,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( sK0 != k1_tarski(sK1)
    & k1_xboole_0 != sK0
    & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( sK0 != k1_tarski(sK1)
      & k1_xboole_0 != sK0
      & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f50,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:54:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.46  % (32596)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.48  % (32612)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.48  % (32612)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f226,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f45,f50,f55,f90,f102,f120,f195,f225])).
% 0.20/0.48  fof(f225,plain,(
% 0.20/0.48    spl4_1 | ~spl4_3 | ~spl4_8),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f223])).
% 0.20/0.48  fof(f223,plain,(
% 0.20/0.48    $false | (spl4_1 | ~spl4_3 | ~spl4_8)),
% 0.20/0.48    inference(subsumption_resolution,[],[f44,f196])).
% 0.20/0.48  fof(f196,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | (~spl4_3 | ~spl4_8)),
% 0.20/0.48    inference(superposition,[],[f194,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~spl4_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    spl4_3 <=> k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.48  fof(f194,plain,(
% 0.20/0.48    ( ! [X3] : (sK0 = k4_xboole_0(sK0,X3)) ) | ~spl4_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f193])).
% 0.20/0.48  fof(f193,plain,(
% 0.20/0.48    spl4_8 <=> ! [X3] : sK0 = k4_xboole_0(sK0,X3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    k1_xboole_0 != sK0 | spl4_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    spl4_1 <=> k1_xboole_0 = sK0),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.48  fof(f195,plain,(
% 0.20/0.48    spl4_8 | spl4_6 | ~spl4_3 | ~spl4_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f189,f118,f52,f99,f193])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    spl4_6 <=> r2_hidden(sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    spl4_7 <=> ! [X3] : (sK1 = X3 | ~r2_hidden(X3,sK0) | sK0 = k1_tarski(X3))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.48  fof(f189,plain,(
% 0.20/0.48    ( ! [X3] : (r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,X3)) ) | (~spl4_3 | ~spl4_7)),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f188])).
% 0.20/0.48  fof(f188,plain,(
% 0.20/0.48    ( ! [X3] : (r2_hidden(sK1,sK0) | r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,X3) | sK0 = k4_xboole_0(sK0,X3)) ) | (~spl4_3 | ~spl4_7)),
% 0.20/0.48    inference(superposition,[],[f26,f164])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    ( ! [X11] : (sK1 = sK2(sK0,X11,sK0) | sK0 = k4_xboole_0(sK0,X11)) ) | (~spl4_3 | ~spl4_7)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f160])).
% 0.20/0.49  fof(f160,plain,(
% 0.20/0.49    ( ! [X11] : (sK1 = sK2(sK0,X11,sK0) | sK0 = k4_xboole_0(sK0,X11) | sK1 = sK2(sK0,X11,sK0)) ) | (~spl4_3 | ~spl4_7)),
% 0.20/0.49    inference(resolution,[],[f148,f146])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | sK1 = X0) ) | (~spl4_3 | ~spl4_7)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f143])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | sK1 = X0 | sK1 = X0) ) | (~spl4_3 | ~spl4_7)),
% 0.20/0.49    inference(resolution,[],[f142,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.20/0.49    inference(equality_resolution,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.50    inference(rectify,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(X0,k1_tarski(sK1)) | ~r2_hidden(X0,sK0) | sK1 = X0) ) | (~spl4_3 | ~spl4_7)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f139])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r2_hidden(X0,k1_tarski(sK1)) | ~r2_hidden(X0,sK0) | sK1 = X0) ) | (~spl4_3 | ~spl4_7)),
% 0.20/0.50    inference(superposition,[],[f125,f54])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    ( ! [X4,X3] : (k1_xboole_0 != k4_xboole_0(sK0,X4) | r2_hidden(X3,X4) | ~r2_hidden(X3,sK0) | sK1 = X3) ) | ~spl4_7),
% 0.20/0.50    inference(superposition,[],[f29,f119])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ( ! [X3] : (sK0 = k1_tarski(X3) | ~r2_hidden(X3,sK0) | sK1 = X3) ) | ~spl4_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f118])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 | r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0))),
% 0.20/0.50    inference(nnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    ( ! [X2,X1] : (r2_hidden(sK2(X1,X2,sK0),X1) | sK1 = sK2(X1,X2,sK0) | sK0 = k4_xboole_0(X1,X2)) ) | (~spl4_3 | ~spl4_7)),
% 0.20/0.50    inference(resolution,[],[f146,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.50    inference(rectify,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.50    inference(flattening,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.50    inference(nnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    spl4_7 | spl4_6 | ~spl4_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f108,f52,f99,f118])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    ( ! [X3] : (r2_hidden(sK1,sK0) | sK1 = X3 | sK0 = k1_tarski(X3) | ~r2_hidden(X3,sK0)) ) | ~spl4_3),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f107])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    ( ! [X3] : (r2_hidden(sK1,sK0) | sK1 = X3 | sK0 = k1_tarski(X3) | ~r2_hidden(X3,sK0) | sK0 = k1_tarski(X3)) ) | ~spl4_3),
% 0.20/0.50    inference(superposition,[],[f33,f93])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    ( ! [X0] : (sK1 = sK3(X0,sK0) | ~r2_hidden(X0,sK0) | k1_tarski(X0) = sK0) ) | ~spl4_3),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f92])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    ( ! [X0] : (X0 != X0 | k1_tarski(X0) = sK0 | ~r2_hidden(X0,sK0) | sK1 = sK3(X0,sK0)) ) | ~spl4_3),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f91])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    ( ! [X0] : (X0 != X0 | k1_tarski(X0) = sK0 | ~r2_hidden(X0,sK0) | k1_tarski(X0) = sK0 | sK1 = sK3(X0,sK0)) ) | ~spl4_3),
% 0.20/0.50    inference(superposition,[],[f34,f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ( ! [X0] : (sK3(X0,sK0) = X0 | k1_tarski(X0) = sK0 | sK1 = sK3(X0,sK0)) ) | ~spl4_3),
% 0.20/0.50    inference(resolution,[],[f80,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X7] : (~r2_hidden(X7,k1_xboole_0)) )),
% 0.20/0.50    inference(condensation,[],[f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X6,X7] : (~r2_hidden(X7,k1_xboole_0) | ~r2_hidden(X7,X6)) )),
% 0.20/0.50    inference(condensation,[],[f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X6,X7,X5] : (~r2_hidden(X7,k1_xboole_0) | ~r2_hidden(X7,X6) | ~r2_hidden(X5,X6)) )),
% 0.20/0.50    inference(superposition,[],[f36,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    ( ! [X9] : (r2_hidden(sK3(X9,sK0),k1_xboole_0) | sK0 = k1_tarski(X9) | sK3(X9,sK0) = X9 | sK1 = sK3(X9,sK0)) ) | ~spl4_3),
% 0.20/0.50    inference(resolution,[],[f33,f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,k1_xboole_0) | sK1 = X0) ) | ~spl4_3),
% 0.20/0.50    inference(resolution,[],[f72,f40])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(X0,k1_tarski(sK1)) | r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,sK0)) ) | ~spl4_3),
% 0.20/0.50    inference(superposition,[],[f35,f54])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sK3(X0,X1) != X0 | k1_tarski(X0) = X1 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | sK3(X0,X1) = X0 | k1_tarski(X0) = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    ~spl4_6 | spl4_2 | ~spl4_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f97,f87,f47,f99])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    spl4_2 <=> sK0 = k1_tarski(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    spl4_5 <=> sK1 = sK3(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    sK0 = k1_tarski(sK1) | ~r2_hidden(sK1,sK0) | ~spl4_5),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f95])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    sK1 != sK1 | sK0 = k1_tarski(sK1) | ~r2_hidden(sK1,sK0) | ~spl4_5),
% 0.20/0.50    inference(superposition,[],[f34,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    sK1 = sK3(sK1,sK0) | ~spl4_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f87])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    spl4_5 | spl4_2 | ~spl4_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f85,f52,f47,f87])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    sK0 = k1_tarski(sK1) | sK1 = sK3(sK1,sK0) | ~spl4_3),
% 0.20/0.50    inference(equality_resolution,[],[f84])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    ( ! [X0] : (sK1 != X0 | k1_tarski(X0) = sK0 | sK1 = sK3(X0,sK0)) ) | ~spl4_3),
% 0.20/0.50    inference(equality_factoring,[],[f81])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    spl4_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f20,f52])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f7,plain,(
% 0.20/0.50    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.20/0.50    inference(negated_conjecture,[],[f5])).
% 0.20/0.50  fof(f5,conjecture,(
% 0.20/0.50    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ~spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f22,f47])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    sK0 != k1_tarski(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ~spl4_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f21,f42])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    k1_xboole_0 != sK0),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (32612)------------------------------
% 0.20/0.50  % (32612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (32612)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (32612)Memory used [KB]: 10874
% 0.20/0.50  % (32612)Time elapsed: 0.073 s
% 0.20/0.50  % (32612)------------------------------
% 0.20/0.50  % (32612)------------------------------
% 0.20/0.50  % (32588)Success in time 0.141 s
%------------------------------------------------------------------------------
