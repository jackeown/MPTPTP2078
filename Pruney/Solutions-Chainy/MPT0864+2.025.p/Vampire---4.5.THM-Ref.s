%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 401 expanded)
%              Number of leaves         :   21 ( 124 expanded)
%              Depth                    :   22
%              Number of atoms          :  424 (2122 expanded)
%              Number of equality atoms :  226 (1252 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f588,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f75,f82,f88,f120,f310,f391,f402,f408,f579,f585])).

fof(f585,plain,
    ( spl6_7
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f443,f399,f117])).

fof(f117,plain,
    ( spl6_7
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f399,plain,
    ( spl6_12
  <=> sK0 = k4_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f443,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f439,f54])).

fof(f54,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f439,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k1_tarski(X0))
        | k1_tarski(X0) = k1_xboole_0 )
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f438,f55])).

fof(f55,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f438,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k1_tarski(X0))
        | k1_tarski(X0) = k1_xboole_0 )
    | ~ spl6_12 ),
    inference(duplicate_literal_removal,[],[f437])).

fof(f437,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k1_tarski(X0))
        | k1_tarski(X0) = k1_xboole_0
        | k1_tarski(X0) = k1_xboole_0 )
    | ~ spl6_12 ),
    inference(superposition,[],[f434,f94])).

fof(f94,plain,(
    ! [X1] :
      ( sK5(k1_tarski(X1)) = X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f55,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

% (3066)Termination reason: Refutation not found, incomplete strategy

% (3066)Memory used [KB]: 10618
% (3066)Time elapsed: 0.164 s
% (3066)------------------------------
% (3066)------------------------------
fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f434,plain,
    ( ! [X0] :
        ( sK0 != sK5(X0)
        | ~ r2_hidden(sK0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_12 ),
    inference(superposition,[],[f43,f401])).

fof(f401,plain,
    ( sK0 = k4_tarski(sK0,sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f399])).

fof(f43,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK5(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f579,plain,
    ( ~ spl6_7
    | ~ spl6_12
    | spl6_13 ),
    inference(avatar_contradiction_clause,[],[f573])).

fof(f573,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_12
    | spl6_13 ),
    inference(unit_resulting_resolution,[],[f407,f569,f125])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | sK0 = X0 )
    | ~ spl6_7 ),
    inference(superposition,[],[f55,f119])).

fof(f119,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f569,plain,
    ( ! [X10] : r2_hidden(k4_tarski(sK0,X10),k1_xboole_0)
    | ~ spl6_12 ),
    inference(superposition,[],[f51,f558])).

fof(f558,plain,
    ( ! [X0] : k1_xboole_0 = k2_tarski(k4_tarski(sK0,X0),sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f555,f49])).

fof(f49,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f555,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_tarski(k4_tarski(X0,X1),sK0))
        | k1_xboole_0 = k2_tarski(k4_tarski(X0,X1),sK0) )
    | ~ spl6_12 ),
    inference(equality_resolution,[],[f531])).

fof(f531,plain,
    ( ! [X6,X8,X7] :
        ( k4_tarski(X7,X8) != X6
        | ~ r2_hidden(X7,k2_tarski(X6,sK0))
        | k1_xboole_0 = k2_tarski(X6,sK0) )
    | ~ spl6_12 ),
    inference(duplicate_literal_removal,[],[f528])).

fof(f528,plain,
    ( ! [X6,X8,X7] :
        ( k4_tarski(X7,X8) != X6
        | ~ r2_hidden(X7,k2_tarski(X6,sK0))
        | k1_xboole_0 = k2_tarski(X6,sK0)
        | k1_xboole_0 = k2_tarski(X6,sK0) )
    | ~ spl6_12 ),
    inference(superposition,[],[f43,f508])).

fof(f508,plain,
    ( ! [X0] :
        ( sK5(k2_tarski(X0,sK0)) = X0
        | k1_xboole_0 = k2_tarski(X0,sK0) )
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f507,f49])).

fof(f507,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k2_tarski(X0,sK0))
        | k1_xboole_0 = k2_tarski(X0,sK0)
        | sK5(k2_tarski(X0,sK0)) = X0 )
    | ~ spl6_12 ),
    inference(equality_resolution,[],[f491])).

fof(f491,plain,
    ( ! [X6,X7] :
        ( sK0 != X7
        | ~ r2_hidden(sK0,k2_tarski(X6,X7))
        | k1_xboole_0 = k2_tarski(X6,X7)
        | sK5(k2_tarski(X6,X7)) = X6 )
    | ~ spl6_12 ),
    inference(duplicate_literal_removal,[],[f485])).

fof(f485,plain,
    ( ! [X6,X7] :
        ( sK0 != X7
        | ~ r2_hidden(sK0,k2_tarski(X6,X7))
        | k1_xboole_0 = k2_tarski(X6,X7)
        | sK5(k2_tarski(X6,X7)) = X6
        | k1_xboole_0 = k2_tarski(X6,X7) )
    | ~ spl6_12 ),
    inference(superposition,[],[f434,f99])).

fof(f99,plain,(
    ! [X4,X5] :
      ( sK5(k2_tarski(X4,X5)) = X5
      | sK5(k2_tarski(X4,X5)) = X4
      | k1_xboole_0 = k2_tarski(X4,X5) ) ),
    inference(resolution,[],[f52,f42])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f407,plain,
    ( sK0 != k4_tarski(sK0,sK0)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f405])).

fof(f405,plain,
    ( spl6_13
  <=> sK0 = k4_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f408,plain,
    ( ~ spl6_13
    | spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f403,f307,f85,f405])).

fof(f85,plain,
    ( spl6_6
  <=> sK0 = k4_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f307,plain,
    ( spl6_10
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f403,plain,
    ( sK0 != k4_tarski(sK0,sK0)
    | spl6_6
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f86,f309])).

fof(f309,plain,
    ( sK0 = sK1
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f307])).

fof(f86,plain,
    ( sK0 != k4_tarski(sK1,sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f402,plain,
    ( spl6_12
    | ~ spl6_3
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f397,f307,f66,f399])).

fof(f66,plain,
    ( spl6_3
  <=> sK0 = k4_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f397,plain,
    ( sK0 = k4_tarski(sK0,sK2)
    | ~ spl6_3
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f68,f309])).

fof(f68,plain,
    ( sK0 = k4_tarski(sK1,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f391,plain,
    ( ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f362,f295])).

fof(f295,plain,
    ( ! [X1] : k2_mcart_1(sK0) = X1
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(superposition,[],[f30,f291])).

fof(f291,plain,
    ( ! [X2] : sK0 = k4_tarski(sK0,X2)
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(resolution,[],[f287,f125])).

fof(f287,plain,
    ( ! [X10] : r2_hidden(k4_tarski(sK0,X10),k1_xboole_0)
    | ~ spl6_6 ),
    inference(superposition,[],[f51,f274])).

fof(f274,plain,
    ( ! [X0] : k1_xboole_0 = k2_tarski(k4_tarski(sK0,X0),sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f272,f49])).

fof(f272,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_tarski(k4_tarski(X0,X1),sK0))
        | k1_xboole_0 = k2_tarski(k4_tarski(X0,X1),sK0) )
    | ~ spl6_6 ),
    inference(equality_resolution,[],[f208])).

fof(f208,plain,
    ( ! [X6,X8,X7] :
        ( k4_tarski(X7,X8) != X6
        | ~ r2_hidden(X7,k2_tarski(X6,sK0))
        | k1_xboole_0 = k2_tarski(X6,sK0) )
    | ~ spl6_6 ),
    inference(duplicate_literal_removal,[],[f205])).

fof(f205,plain,
    ( ! [X6,X8,X7] :
        ( k4_tarski(X7,X8) != X6
        | ~ r2_hidden(X7,k2_tarski(X6,sK0))
        | k1_xboole_0 = k2_tarski(X6,sK0)
        | k1_xboole_0 = k2_tarski(X6,sK0) )
    | ~ spl6_6 ),
    inference(superposition,[],[f43,f198])).

fof(f198,plain,
    ( ! [X0] :
        ( sK5(k2_tarski(X0,sK0)) = X0
        | k1_xboole_0 = k2_tarski(X0,sK0) )
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f197,f49])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k2_tarski(X0,sK0))
        | k1_xboole_0 = k2_tarski(X0,sK0)
        | sK5(k2_tarski(X0,sK0)) = X0 )
    | ~ spl6_6 ),
    inference(equality_resolution,[],[f144])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( sK0 != X1
        | ~ r2_hidden(sK0,k2_tarski(X0,X1))
        | k2_tarski(X0,X1) = k1_xboole_0
        | sK5(k2_tarski(X0,X1)) = X0 )
    | ~ spl6_6 ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( sK0 != X1
        | ~ r2_hidden(sK0,k2_tarski(X0,X1))
        | k2_tarski(X0,X1) = k1_xboole_0
        | sK5(k2_tarski(X0,X1)) = X0
        | k2_tarski(X0,X1) = k1_xboole_0 )
    | ~ spl6_6 ),
    inference(superposition,[],[f105,f99])).

fof(f105,plain,
    ( ! [X0] :
        ( sK0 != sK5(X0)
        | ~ r2_hidden(sK0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_6 ),
    inference(superposition,[],[f44,f87])).

fof(f87,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f44,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK5(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f30,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f362,plain,
    ( k1_xboole_0 != k2_mcart_1(sK0)
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(superposition,[],[f126,f295])).

fof(f126,plain,
    ( ! [X1] : k1_xboole_0 != k2_xboole_0(k1_xboole_0,X1)
    | ~ spl6_7 ),
    inference(superposition,[],[f46,f119])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f310,plain,
    ( spl6_10
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f305,f72,f57,f307])).

fof(f57,plain,
    ( spl6_1
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f72,plain,
    ( spl6_4
  <=> k1_mcart_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f305,plain,
    ( sK0 = sK1
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f74,f59])).

fof(f59,plain,
    ( sK0 = k1_mcart_1(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f74,plain,
    ( k1_mcart_1(sK0) = sK1
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f120,plain,
    ( spl6_7
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f115,f85,f117])).

fof(f115,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f114,f54])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k1_tarski(X0))
        | k1_tarski(X0) = k1_xboole_0 )
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f113,f55])).

fof(f113,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k1_tarski(X0))
        | k1_tarski(X0) = k1_xboole_0 )
    | ~ spl6_6 ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k1_tarski(X0))
        | k1_tarski(X0) = k1_xboole_0
        | k1_tarski(X0) = k1_xboole_0 )
    | ~ spl6_6 ),
    inference(superposition,[],[f105,f94])).

fof(f88,plain,
    ( spl6_6
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f83,f79,f66,f85])).

fof(f79,plain,
    ( spl6_5
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f83,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f68,f81])).

fof(f81,plain,
    ( sK0 = sK2
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f82,plain,
    ( spl6_5
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f77,f66,f61,f79])).

fof(f61,plain,
    ( spl6_2
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f77,plain,
    ( sK0 = sK2
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f76,f63])).

fof(f63,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f76,plain,
    ( k2_mcart_1(sK0) = sK2
    | ~ spl6_3 ),
    inference(superposition,[],[f30,f68])).

fof(f75,plain,
    ( spl6_4
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f70,f66,f72])).

fof(f70,plain,
    ( k1_mcart_1(sK0) = sK1
    | ~ spl6_3 ),
    inference(superposition,[],[f29,f68])).

fof(f29,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f69,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f27,f66])).

fof(f27,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f64,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f28,f61,f57])).

fof(f28,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (3072)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.49  % (3064)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.50  % (3063)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.50  % (3064)Refutation not found, incomplete strategy% (3064)------------------------------
% 0.21/0.50  % (3064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3064)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (3064)Memory used [KB]: 1791
% 0.21/0.50  % (3064)Time elapsed: 0.059 s
% 0.21/0.50  % (3064)------------------------------
% 0.21/0.50  % (3064)------------------------------
% 0.21/0.50  % (3056)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (3079)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (3054)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (3052)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (3055)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (3058)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (3068)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (3060)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (3057)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (3071)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (3079)Refutation not found, incomplete strategy% (3079)------------------------------
% 0.21/0.52  % (3079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3076)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (3079)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3079)Memory used [KB]: 1663
% 0.21/0.53  % (3079)Time elapsed: 0.004 s
% 0.21/0.53  % (3079)------------------------------
% 0.21/0.53  % (3079)------------------------------
% 0.21/0.53  % (3076)Refutation not found, incomplete strategy% (3076)------------------------------
% 0.21/0.53  % (3076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3076)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3076)Memory used [KB]: 6268
% 0.21/0.53  % (3076)Time elapsed: 0.132 s
% 0.21/0.53  % (3076)------------------------------
% 0.21/0.53  % (3076)------------------------------
% 0.21/0.53  % (3073)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (3053)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (3078)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (3077)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (3051)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (3051)Refutation not found, incomplete strategy% (3051)------------------------------
% 0.21/0.53  % (3051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3051)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3051)Memory used [KB]: 1663
% 0.21/0.53  % (3051)Time elapsed: 0.127 s
% 0.21/0.53  % (3051)------------------------------
% 0.21/0.53  % (3051)------------------------------
% 0.21/0.53  % (3077)Refutation not found, incomplete strategy% (3077)------------------------------
% 0.21/0.53  % (3077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3077)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3077)Memory used [KB]: 6268
% 0.21/0.53  % (3077)Time elapsed: 0.130 s
% 0.21/0.53  % (3077)------------------------------
% 0.21/0.53  % (3077)------------------------------
% 0.21/0.53  % (3078)Refutation not found, incomplete strategy% (3078)------------------------------
% 0.21/0.53  % (3078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3078)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3078)Memory used [KB]: 10746
% 0.21/0.53  % (3078)Time elapsed: 0.129 s
% 0.21/0.53  % (3078)------------------------------
% 0.21/0.53  % (3078)------------------------------
% 0.21/0.53  % (3050)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (3068)Refutation not found, incomplete strategy% (3068)------------------------------
% 0.21/0.53  % (3068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3068)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3068)Memory used [KB]: 1791
% 0.21/0.53  % (3068)Time elapsed: 0.125 s
% 0.21/0.53  % (3068)------------------------------
% 0.21/0.53  % (3068)------------------------------
% 0.21/0.54  % (3060)Refutation not found, incomplete strategy% (3060)------------------------------
% 0.21/0.54  % (3060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3060)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3060)Memory used [KB]: 10746
% 0.21/0.54  % (3060)Time elapsed: 0.125 s
% 0.21/0.54  % (3060)------------------------------
% 0.21/0.54  % (3060)------------------------------
% 0.21/0.54  % (3065)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (3075)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (3069)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (3070)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (3075)Refutation not found, incomplete strategy% (3075)------------------------------
% 0.21/0.54  % (3075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3075)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3075)Memory used [KB]: 6268
% 0.21/0.54  % (3075)Time elapsed: 0.140 s
% 0.21/0.54  % (3075)------------------------------
% 0.21/0.54  % (3075)------------------------------
% 0.21/0.54  % (3074)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (3067)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (3067)Refutation not found, incomplete strategy% (3067)------------------------------
% 0.21/0.54  % (3067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3067)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3067)Memory used [KB]: 1663
% 0.21/0.54  % (3067)Time elapsed: 0.142 s
% 0.21/0.54  % (3067)------------------------------
% 0.21/0.54  % (3067)------------------------------
% 0.21/0.54  % (3074)Refutation not found, incomplete strategy% (3074)------------------------------
% 0.21/0.54  % (3074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3074)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3074)Memory used [KB]: 10746
% 0.21/0.54  % (3074)Time elapsed: 0.151 s
% 0.21/0.54  % (3074)------------------------------
% 0.21/0.54  % (3074)------------------------------
% 0.21/0.55  % (3059)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (3061)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (3062)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (3061)Refutation not found, incomplete strategy% (3061)------------------------------
% 0.21/0.55  % (3061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3061)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3061)Memory used [KB]: 6268
% 0.21/0.55  % (3061)Time elapsed: 0.153 s
% 0.21/0.55  % (3061)------------------------------
% 0.21/0.55  % (3061)------------------------------
% 0.21/0.55  % (3062)Refutation not found, incomplete strategy% (3062)------------------------------
% 0.21/0.55  % (3062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3062)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3062)Memory used [KB]: 10618
% 0.21/0.55  % (3062)Time elapsed: 0.152 s
% 0.21/0.55  % (3062)------------------------------
% 0.21/0.55  % (3062)------------------------------
% 0.21/0.56  % (3066)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (3066)Refutation not found, incomplete strategy% (3066)------------------------------
% 0.21/0.56  % (3066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3071)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f588,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f64,f69,f75,f82,f88,f120,f310,f391,f402,f408,f579,f585])).
% 0.21/0.56  fof(f585,plain,(
% 0.21/0.56    spl6_7 | ~spl6_12),
% 0.21/0.56    inference(avatar_split_clause,[],[f443,f399,f117])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    spl6_7 <=> k1_xboole_0 = k1_tarski(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.56  fof(f399,plain,(
% 0.21/0.56    spl6_12 <=> sK0 = k4_tarski(sK0,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.56  fof(f443,plain,(
% 0.21/0.56    k1_xboole_0 = k1_tarski(sK0) | ~spl6_12),
% 0.21/0.56    inference(resolution,[],[f439,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.21/0.56    inference(equality_resolution,[],[f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.21/0.56    inference(equality_resolution,[],[f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.56    inference(rectify,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.56  fof(f439,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(sK0,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0) ) | ~spl6_12),
% 0.21/0.56    inference(subsumption_resolution,[],[f438,f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.56    inference(equality_resolution,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f438,plain,(
% 0.21/0.56    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0) ) | ~spl6_12),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f437])).
% 0.21/0.56  fof(f437,plain,(
% 0.21/0.56    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0 | k1_tarski(X0) = k1_xboole_0) ) | ~spl6_12),
% 0.21/0.56    inference(superposition,[],[f434,f94])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    ( ! [X1] : (sK5(k1_tarski(X1)) = X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 0.21/0.56    inference(resolution,[],[f55,f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  % (3066)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (3066)Memory used [KB]: 10618
% 0.21/0.57  % (3066)Time elapsed: 0.164 s
% 0.21/0.57  % (3066)------------------------------
% 0.21/0.57  % (3066)------------------------------
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.57  fof(f434,plain,(
% 0.21/0.57    ( ! [X0] : (sK0 != sK5(X0) | ~r2_hidden(sK0,X0) | k1_xboole_0 = X0) ) | ~spl6_12),
% 0.21/0.57    inference(superposition,[],[f43,f401])).
% 0.21/0.57  fof(f401,plain,(
% 0.21/0.57    sK0 = k4_tarski(sK0,sK2) | ~spl6_12),
% 0.21/0.57    inference(avatar_component_clause,[],[f399])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK5(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f579,plain,(
% 0.21/0.57    ~spl6_7 | ~spl6_12 | spl6_13),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f573])).
% 0.21/0.57  fof(f573,plain,(
% 0.21/0.57    $false | (~spl6_7 | ~spl6_12 | spl6_13)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f407,f569,f125])).
% 0.21/0.57  fof(f125,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | sK0 = X0) ) | ~spl6_7),
% 0.21/0.57    inference(superposition,[],[f55,f119])).
% 0.21/0.57  fof(f119,plain,(
% 0.21/0.57    k1_xboole_0 = k1_tarski(sK0) | ~spl6_7),
% 0.21/0.57    inference(avatar_component_clause,[],[f117])).
% 0.21/0.57  fof(f569,plain,(
% 0.21/0.57    ( ! [X10] : (r2_hidden(k4_tarski(sK0,X10),k1_xboole_0)) ) | ~spl6_12),
% 0.21/0.57    inference(superposition,[],[f51,f558])).
% 0.21/0.57  fof(f558,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k2_tarski(k4_tarski(sK0,X0),sK0)) ) | ~spl6_12),
% 0.21/0.57    inference(resolution,[],[f555,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 0.21/0.57    inference(equality_resolution,[],[f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 0.21/0.57    inference(equality_resolution,[],[f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.57    inference(rectify,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.57    inference(flattening,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.57    inference(nnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.57  fof(f555,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_tarski(k4_tarski(X0,X1),sK0)) | k1_xboole_0 = k2_tarski(k4_tarski(X0,X1),sK0)) ) | ~spl6_12),
% 0.21/0.57    inference(equality_resolution,[],[f531])).
% 0.21/0.57  fof(f531,plain,(
% 0.21/0.57    ( ! [X6,X8,X7] : (k4_tarski(X7,X8) != X6 | ~r2_hidden(X7,k2_tarski(X6,sK0)) | k1_xboole_0 = k2_tarski(X6,sK0)) ) | ~spl6_12),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f528])).
% 0.21/0.57  fof(f528,plain,(
% 0.21/0.57    ( ! [X6,X8,X7] : (k4_tarski(X7,X8) != X6 | ~r2_hidden(X7,k2_tarski(X6,sK0)) | k1_xboole_0 = k2_tarski(X6,sK0) | k1_xboole_0 = k2_tarski(X6,sK0)) ) | ~spl6_12),
% 0.21/0.57    inference(superposition,[],[f43,f508])).
% 0.21/0.57  fof(f508,plain,(
% 0.21/0.57    ( ! [X0] : (sK5(k2_tarski(X0,sK0)) = X0 | k1_xboole_0 = k2_tarski(X0,sK0)) ) | ~spl6_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f507,f49])).
% 0.21/0.57  fof(f507,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(sK0,k2_tarski(X0,sK0)) | k1_xboole_0 = k2_tarski(X0,sK0) | sK5(k2_tarski(X0,sK0)) = X0) ) | ~spl6_12),
% 0.21/0.57    inference(equality_resolution,[],[f491])).
% 0.21/0.58  fof(f491,plain,(
% 0.21/0.58    ( ! [X6,X7] : (sK0 != X7 | ~r2_hidden(sK0,k2_tarski(X6,X7)) | k1_xboole_0 = k2_tarski(X6,X7) | sK5(k2_tarski(X6,X7)) = X6) ) | ~spl6_12),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f485])).
% 0.21/0.58  fof(f485,plain,(
% 0.21/0.58    ( ! [X6,X7] : (sK0 != X7 | ~r2_hidden(sK0,k2_tarski(X6,X7)) | k1_xboole_0 = k2_tarski(X6,X7) | sK5(k2_tarski(X6,X7)) = X6 | k1_xboole_0 = k2_tarski(X6,X7)) ) | ~spl6_12),
% 0.21/0.58    inference(superposition,[],[f434,f99])).
% 0.21/0.58  fof(f99,plain,(
% 0.21/0.58    ( ! [X4,X5] : (sK5(k2_tarski(X4,X5)) = X5 | sK5(k2_tarski(X4,X5)) = X4 | k1_xboole_0 = k2_tarski(X4,X5)) )),
% 0.21/0.58    inference(resolution,[],[f52,f42])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.21/0.58    inference(equality_resolution,[],[f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.58    inference(cnf_transformation,[],[f20])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 0.21/0.58    inference(equality_resolution,[],[f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 0.21/0.58    inference(equality_resolution,[],[f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.58    inference(cnf_transformation,[],[f20])).
% 0.21/0.58  fof(f407,plain,(
% 0.21/0.58    sK0 != k4_tarski(sK0,sK0) | spl6_13),
% 0.21/0.58    inference(avatar_component_clause,[],[f405])).
% 0.21/0.58  fof(f405,plain,(
% 0.21/0.58    spl6_13 <=> sK0 = k4_tarski(sK0,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.58  fof(f408,plain,(
% 0.21/0.58    ~spl6_13 | spl6_6 | ~spl6_10),
% 0.21/0.58    inference(avatar_split_clause,[],[f403,f307,f85,f405])).
% 0.21/0.58  fof(f85,plain,(
% 0.21/0.58    spl6_6 <=> sK0 = k4_tarski(sK1,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.58  fof(f307,plain,(
% 0.21/0.58    spl6_10 <=> sK0 = sK1),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.58  fof(f403,plain,(
% 0.21/0.58    sK0 != k4_tarski(sK0,sK0) | (spl6_6 | ~spl6_10)),
% 0.21/0.58    inference(forward_demodulation,[],[f86,f309])).
% 0.21/0.58  fof(f309,plain,(
% 0.21/0.58    sK0 = sK1 | ~spl6_10),
% 0.21/0.58    inference(avatar_component_clause,[],[f307])).
% 0.21/0.58  fof(f86,plain,(
% 0.21/0.58    sK0 != k4_tarski(sK1,sK0) | spl6_6),
% 0.21/0.58    inference(avatar_component_clause,[],[f85])).
% 0.21/0.58  fof(f402,plain,(
% 0.21/0.58    spl6_12 | ~spl6_3 | ~spl6_10),
% 0.21/0.58    inference(avatar_split_clause,[],[f397,f307,f66,f399])).
% 0.21/0.58  fof(f66,plain,(
% 0.21/0.58    spl6_3 <=> sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.58  fof(f397,plain,(
% 0.21/0.58    sK0 = k4_tarski(sK0,sK2) | (~spl6_3 | ~spl6_10)),
% 0.21/0.58    inference(forward_demodulation,[],[f68,f309])).
% 0.21/0.58  fof(f68,plain,(
% 0.21/0.58    sK0 = k4_tarski(sK1,sK2) | ~spl6_3),
% 0.21/0.58    inference(avatar_component_clause,[],[f66])).
% 0.21/0.58  fof(f391,plain,(
% 0.21/0.58    ~spl6_6 | ~spl6_7),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f390])).
% 0.21/0.58  fof(f390,plain,(
% 0.21/0.58    $false | (~spl6_6 | ~spl6_7)),
% 0.21/0.58    inference(subsumption_resolution,[],[f362,f295])).
% 0.21/0.58  fof(f295,plain,(
% 0.21/0.58    ( ! [X1] : (k2_mcart_1(sK0) = X1) ) | (~spl6_6 | ~spl6_7)),
% 0.21/0.58    inference(superposition,[],[f30,f291])).
% 0.21/0.58  fof(f291,plain,(
% 0.21/0.58    ( ! [X2] : (sK0 = k4_tarski(sK0,X2)) ) | (~spl6_6 | ~spl6_7)),
% 0.21/0.58    inference(resolution,[],[f287,f125])).
% 0.21/0.58  fof(f287,plain,(
% 0.21/0.58    ( ! [X10] : (r2_hidden(k4_tarski(sK0,X10),k1_xboole_0)) ) | ~spl6_6),
% 0.21/0.58    inference(superposition,[],[f51,f274])).
% 0.21/0.58  fof(f274,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k2_tarski(k4_tarski(sK0,X0),sK0)) ) | ~spl6_6),
% 0.21/0.58    inference(resolution,[],[f272,f49])).
% 0.21/0.58  fof(f272,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k2_tarski(k4_tarski(X0,X1),sK0)) | k1_xboole_0 = k2_tarski(k4_tarski(X0,X1),sK0)) ) | ~spl6_6),
% 0.21/0.58    inference(equality_resolution,[],[f208])).
% 0.21/0.58  fof(f208,plain,(
% 0.21/0.58    ( ! [X6,X8,X7] : (k4_tarski(X7,X8) != X6 | ~r2_hidden(X7,k2_tarski(X6,sK0)) | k1_xboole_0 = k2_tarski(X6,sK0)) ) | ~spl6_6),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f205])).
% 0.21/0.58  fof(f205,plain,(
% 0.21/0.58    ( ! [X6,X8,X7] : (k4_tarski(X7,X8) != X6 | ~r2_hidden(X7,k2_tarski(X6,sK0)) | k1_xboole_0 = k2_tarski(X6,sK0) | k1_xboole_0 = k2_tarski(X6,sK0)) ) | ~spl6_6),
% 0.21/0.58    inference(superposition,[],[f43,f198])).
% 0.21/0.58  fof(f198,plain,(
% 0.21/0.58    ( ! [X0] : (sK5(k2_tarski(X0,sK0)) = X0 | k1_xboole_0 = k2_tarski(X0,sK0)) ) | ~spl6_6),
% 0.21/0.58    inference(subsumption_resolution,[],[f197,f49])).
% 0.21/0.58  fof(f197,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(sK0,k2_tarski(X0,sK0)) | k1_xboole_0 = k2_tarski(X0,sK0) | sK5(k2_tarski(X0,sK0)) = X0) ) | ~spl6_6),
% 0.21/0.58    inference(equality_resolution,[],[f144])).
% 0.21/0.58  fof(f144,plain,(
% 0.21/0.58    ( ! [X0,X1] : (sK0 != X1 | ~r2_hidden(sK0,k2_tarski(X0,X1)) | k2_tarski(X0,X1) = k1_xboole_0 | sK5(k2_tarski(X0,X1)) = X0) ) | ~spl6_6),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f134])).
% 0.21/0.58  fof(f134,plain,(
% 0.21/0.58    ( ! [X0,X1] : (sK0 != X1 | ~r2_hidden(sK0,k2_tarski(X0,X1)) | k2_tarski(X0,X1) = k1_xboole_0 | sK5(k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k1_xboole_0) ) | ~spl6_6),
% 0.21/0.58    inference(superposition,[],[f105,f99])).
% 0.21/0.58  fof(f105,plain,(
% 0.21/0.58    ( ! [X0] : (sK0 != sK5(X0) | ~r2_hidden(sK0,X0) | k1_xboole_0 = X0) ) | ~spl6_6),
% 0.21/0.58    inference(superposition,[],[f44,f87])).
% 0.21/0.58  fof(f87,plain,(
% 0.21/0.58    sK0 = k4_tarski(sK1,sK0) | ~spl6_6),
% 0.21/0.58    inference(avatar_component_clause,[],[f85])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK5(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f26])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.58  fof(f362,plain,(
% 0.21/0.58    k1_xboole_0 != k2_mcart_1(sK0) | (~spl6_6 | ~spl6_7)),
% 0.21/0.58    inference(superposition,[],[f126,f295])).
% 0.21/0.58  fof(f126,plain,(
% 0.21/0.58    ( ! [X1] : (k1_xboole_0 != k2_xboole_0(k1_xboole_0,X1)) ) | ~spl6_7),
% 0.21/0.58    inference(superposition,[],[f46,f119])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.58  fof(f310,plain,(
% 0.21/0.58    spl6_10 | ~spl6_1 | ~spl6_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f305,f72,f57,f307])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    spl6_1 <=> sK0 = k1_mcart_1(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.58  fof(f72,plain,(
% 0.21/0.58    spl6_4 <=> k1_mcart_1(sK0) = sK1),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.58  fof(f305,plain,(
% 0.21/0.58    sK0 = sK1 | (~spl6_1 | ~spl6_4)),
% 0.21/0.58    inference(backward_demodulation,[],[f74,f59])).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    sK0 = k1_mcart_1(sK0) | ~spl6_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f57])).
% 0.21/0.58  fof(f74,plain,(
% 0.21/0.58    k1_mcart_1(sK0) = sK1 | ~spl6_4),
% 0.21/0.58    inference(avatar_component_clause,[],[f72])).
% 0.21/0.58  fof(f120,plain,(
% 0.21/0.58    spl6_7 | ~spl6_6),
% 0.21/0.58    inference(avatar_split_clause,[],[f115,f85,f117])).
% 0.21/0.58  fof(f115,plain,(
% 0.21/0.58    k1_xboole_0 = k1_tarski(sK0) | ~spl6_6),
% 0.21/0.58    inference(resolution,[],[f114,f54])).
% 0.21/0.58  fof(f114,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(sK0,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0) ) | ~spl6_6),
% 0.21/0.58    inference(subsumption_resolution,[],[f113,f55])).
% 0.21/0.58  fof(f113,plain,(
% 0.21/0.58    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0) ) | ~spl6_6),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f112])).
% 0.21/0.58  fof(f112,plain,(
% 0.21/0.58    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0 | k1_tarski(X0) = k1_xboole_0) ) | ~spl6_6),
% 0.21/0.58    inference(superposition,[],[f105,f94])).
% 0.21/0.58  fof(f88,plain,(
% 0.21/0.58    spl6_6 | ~spl6_3 | ~spl6_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f83,f79,f66,f85])).
% 0.21/0.58  fof(f79,plain,(
% 0.21/0.58    spl6_5 <=> sK0 = sK2),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.58  fof(f83,plain,(
% 0.21/0.58    sK0 = k4_tarski(sK1,sK0) | (~spl6_3 | ~spl6_5)),
% 0.21/0.58    inference(backward_demodulation,[],[f68,f81])).
% 0.21/0.58  fof(f81,plain,(
% 0.21/0.58    sK0 = sK2 | ~spl6_5),
% 0.21/0.58    inference(avatar_component_clause,[],[f79])).
% 0.21/0.58  fof(f82,plain,(
% 0.21/0.58    spl6_5 | ~spl6_2 | ~spl6_3),
% 0.21/0.58    inference(avatar_split_clause,[],[f77,f66,f61,f79])).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    spl6_2 <=> sK0 = k2_mcart_1(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.58  fof(f77,plain,(
% 0.21/0.58    sK0 = sK2 | (~spl6_2 | ~spl6_3)),
% 0.21/0.58    inference(forward_demodulation,[],[f76,f63])).
% 0.21/0.58  fof(f63,plain,(
% 0.21/0.58    sK0 = k2_mcart_1(sK0) | ~spl6_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f61])).
% 0.21/0.58  fof(f76,plain,(
% 0.21/0.58    k2_mcart_1(sK0) = sK2 | ~spl6_3),
% 0.21/0.58    inference(superposition,[],[f30,f68])).
% 0.21/0.58  fof(f75,plain,(
% 0.21/0.58    spl6_4 | ~spl6_3),
% 0.21/0.58    inference(avatar_split_clause,[],[f70,f66,f72])).
% 0.21/0.58  fof(f70,plain,(
% 0.21/0.58    k1_mcart_1(sK0) = sK1 | ~spl6_3),
% 0.21/0.58    inference(superposition,[],[f29,f68])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f7])).
% 0.21/0.58  fof(f69,plain,(
% 0.21/0.58    spl6_3),
% 0.21/0.58    inference(avatar_split_clause,[],[f27,f66])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,plain,(
% 0.21/0.58    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14,f13])).
% 0.21/0.58  fof(f13,plain,(
% 0.21/0.58    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f14,plain,(
% 0.21/0.58    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f11,plain,(
% 0.21/0.58    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.21/0.58    inference(ennf_transformation,[],[f10])).
% 0.21/0.59  fof(f10,negated_conjecture,(
% 0.21/0.59    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.59    inference(negated_conjecture,[],[f9])).
% 0.21/0.59  fof(f9,conjecture,(
% 0.21/0.59    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.59  fof(f64,plain,(
% 0.21/0.59    spl6_1 | spl6_2),
% 0.21/0.59    inference(avatar_split_clause,[],[f28,f61,f57])).
% 0.21/0.59  fof(f28,plain,(
% 0.21/0.59    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f15])).
% 0.21/0.59  % SZS output end Proof for theBenchmark
% 0.21/0.59  % (3071)------------------------------
% 0.21/0.59  % (3071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (3071)Termination reason: Refutation
% 0.21/0.59  
% 0.21/0.59  % (3071)Memory used [KB]: 6524
% 0.21/0.59  % (3071)Time elapsed: 0.158 s
% 0.21/0.59  % (3071)------------------------------
% 0.21/0.59  % (3071)------------------------------
% 1.82/0.59  % (3049)Success in time 0.216 s
%------------------------------------------------------------------------------
