%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 266 expanded)
%              Number of leaves         :   21 (  86 expanded)
%              Depth                    :   13
%              Number of atoms          :  347 ( 993 expanded)
%              Number of equality atoms :  280 ( 861 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f143,f161,f188,f214,f240])).

fof(f240,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f222,f91])).

fof(f91,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f30,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f30,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f222,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_2 ),
    inference(superposition,[],[f89,f127])).

fof(f127,plain,
    ( k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl4_2
  <=> k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f89,plain,(
    ! [X6,X4,X2,X10,X7,X5,X3,X1] : r2_hidden(X10,k6_enumset1(X10,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X6,X4,X2,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | k6_enumset1(X10,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | X0 != X10
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 )
            | ~ r2_hidden(X9,X8) )
          & ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9
            | r2_hidden(X9,X8) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

fof(f214,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f196,f91])).

fof(f196,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl4_5 ),
    inference(superposition,[],[f89,f142])).

fof(f142,plain,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl4_5
  <=> k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f188,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f170,f91])).

fof(f170,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(superposition,[],[f89,f138])).

fof(f138,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl4_4
  <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f161,plain,
    ( spl4_5
    | spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f149,f121,f136,f140])).

fof(f121,plain,
    ( spl4_1
  <=> k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f149,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f147])).

fof(f147,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl4_1 ),
    inference(superposition,[],[f32,f123])).

fof(f123,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f143,plain,
    ( spl4_4
    | spl4_5
    | spl4_3 ),
    inference(avatar_split_clause,[],[f134,f129,f140,f136])).

fof(f129,plain,
    ( spl4_3
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f134,plain,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl4_3 ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl4_3 ),
    inference(superposition,[],[f131,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f131,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f132,plain,
    ( spl4_1
    | spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f119,f129,f125,f121])).

fof(f119,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f118,f35])).

fof(f118,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(forward_demodulation,[],[f107,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f40,f67,f68,f67])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f67])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f107,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(backward_demodulation,[],[f69,f70])).

fof(f69,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)))) ),
    inference(definition_unfolding,[],[f28,f68,f68,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f28,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))
   => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:21:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (812941314)
% 0.14/0.37  ipcrm: permission denied for id (819265539)
% 0.14/0.37  ipcrm: permission denied for id (819331077)
% 0.14/0.37  ipcrm: permission denied for id (813039622)
% 0.14/0.37  ipcrm: permission denied for id (813072391)
% 0.14/0.37  ipcrm: permission denied for id (816611336)
% 0.14/0.37  ipcrm: permission denied for id (813137930)
% 0.14/0.38  ipcrm: permission denied for id (819429388)
% 0.14/0.38  ipcrm: permission denied for id (813203469)
% 0.14/0.38  ipcrm: permission denied for id (816742414)
% 0.14/0.38  ipcrm: permission denied for id (819462159)
% 0.14/0.38  ipcrm: permission denied for id (816807952)
% 0.14/0.38  ipcrm: permission denied for id (813301777)
% 0.14/0.38  ipcrm: permission denied for id (819494930)
% 0.14/0.39  ipcrm: permission denied for id (816906260)
% 0.14/0.39  ipcrm: permission denied for id (816939029)
% 0.14/0.39  ipcrm: permission denied for id (817004567)
% 0.14/0.39  ipcrm: permission denied for id (819593240)
% 0.14/0.39  ipcrm: permission denied for id (819626009)
% 0.14/0.39  ipcrm: permission denied for id (817102874)
% 0.14/0.40  ipcrm: permission denied for id (813596699)
% 0.14/0.40  ipcrm: permission denied for id (813629468)
% 0.14/0.40  ipcrm: permission denied for id (813695006)
% 0.14/0.40  ipcrm: permission denied for id (817168415)
% 0.14/0.40  ipcrm: permission denied for id (817201184)
% 0.14/0.40  ipcrm: permission denied for id (817233953)
% 0.21/0.40  ipcrm: permission denied for id (817266722)
% 0.21/0.41  ipcrm: permission denied for id (813858852)
% 0.21/0.41  ipcrm: permission denied for id (817332261)
% 0.21/0.41  ipcrm: permission denied for id (819724326)
% 0.21/0.41  ipcrm: permission denied for id (813924391)
% 0.21/0.41  ipcrm: permission denied for id (817397800)
% 0.21/0.41  ipcrm: permission denied for id (817430569)
% 0.21/0.41  ipcrm: permission denied for id (817463338)
% 0.21/0.41  ipcrm: permission denied for id (817496107)
% 0.21/0.42  ipcrm: permission denied for id (819757100)
% 0.21/0.42  ipcrm: permission denied for id (817561645)
% 0.21/0.42  ipcrm: permission denied for id (814088238)
% 0.21/0.42  ipcrm: permission denied for id (817627184)
% 0.21/0.42  ipcrm: permission denied for id (814153777)
% 0.21/0.42  ipcrm: permission denied for id (814186547)
% 0.21/0.42  ipcrm: permission denied for id (814252084)
% 0.21/0.43  ipcrm: permission denied for id (814284853)
% 0.21/0.43  ipcrm: permission denied for id (819855414)
% 0.21/0.43  ipcrm: permission denied for id (819888183)
% 0.21/0.43  ipcrm: permission denied for id (817758264)
% 0.21/0.43  ipcrm: permission denied for id (817856571)
% 0.21/0.43  ipcrm: permission denied for id (814481468)
% 0.21/0.43  ipcrm: permission denied for id (817889341)
% 0.21/0.44  ipcrm: permission denied for id (814547006)
% 0.21/0.44  ipcrm: permission denied for id (819986495)
% 0.21/0.44  ipcrm: permission denied for id (814678080)
% 0.21/0.44  ipcrm: permission denied for id (818020418)
% 0.21/0.44  ipcrm: permission denied for id (814743619)
% 0.21/0.44  ipcrm: permission denied for id (818053188)
% 0.21/0.44  ipcrm: permission denied for id (818085957)
% 0.21/0.45  ipcrm: permission denied for id (818118726)
% 0.21/0.45  ipcrm: permission denied for id (814841927)
% 0.21/0.45  ipcrm: permission denied for id (820052040)
% 0.21/0.45  ipcrm: permission denied for id (814874697)
% 0.21/0.45  ipcrm: permission denied for id (814907466)
% 0.21/0.45  ipcrm: permission denied for id (818184267)
% 0.21/0.45  ipcrm: permission denied for id (818217036)
% 0.21/0.45  ipcrm: permission denied for id (820117582)
% 0.21/0.46  ipcrm: permission denied for id (815104079)
% 0.21/0.46  ipcrm: permission denied for id (815136848)
% 0.21/0.46  ipcrm: permission denied for id (818315345)
% 0.21/0.46  ipcrm: permission denied for id (815169618)
% 0.21/0.46  ipcrm: permission denied for id (815202387)
% 0.21/0.46  ipcrm: permission denied for id (815235156)
% 0.21/0.46  ipcrm: permission denied for id (815267925)
% 0.21/0.46  ipcrm: permission denied for id (815300694)
% 0.21/0.47  ipcrm: permission denied for id (815333463)
% 0.21/0.47  ipcrm: permission denied for id (818413658)
% 0.21/0.47  ipcrm: permission denied for id (815464539)
% 0.21/0.47  ipcrm: permission denied for id (818446428)
% 0.21/0.47  ipcrm: permission denied for id (820215901)
% 0.21/0.47  ipcrm: permission denied for id (818511966)
% 0.21/0.47  ipcrm: permission denied for id (815497311)
% 0.21/0.48  ipcrm: permission denied for id (815530080)
% 0.21/0.48  ipcrm: permission denied for id (815562849)
% 0.21/0.48  ipcrm: permission denied for id (818577506)
% 0.21/0.48  ipcrm: permission denied for id (815661156)
% 0.21/0.48  ipcrm: permission denied for id (818643045)
% 0.21/0.48  ipcrm: permission denied for id (815726694)
% 0.21/0.48  ipcrm: permission denied for id (818675815)
% 0.21/0.49  ipcrm: permission denied for id (815792232)
% 0.21/0.49  ipcrm: permission denied for id (818708585)
% 0.21/0.49  ipcrm: permission denied for id (815857770)
% 0.21/0.49  ipcrm: permission denied for id (815890539)
% 0.21/0.49  ipcrm: permission denied for id (818741356)
% 0.21/0.49  ipcrm: permission denied for id (818774125)
% 0.21/0.49  ipcrm: permission denied for id (818839663)
% 0.21/0.49  ipcrm: permission denied for id (820314224)
% 0.21/0.50  ipcrm: permission denied for id (818905201)
% 0.21/0.50  ipcrm: permission denied for id (816054386)
% 0.21/0.50  ipcrm: permission denied for id (818937971)
% 0.21/0.50  ipcrm: permission denied for id (816119924)
% 0.21/0.50  ipcrm: permission denied for id (816185463)
% 0.21/0.50  ipcrm: permission denied for id (819036280)
% 0.21/0.51  ipcrm: permission denied for id (820445305)
% 0.21/0.51  ipcrm: permission denied for id (816316539)
% 0.21/0.51  ipcrm: permission denied for id (819134588)
% 0.21/0.51  ipcrm: permission denied for id (816349309)
% 0.21/0.51  ipcrm: permission denied for id (819167358)
% 0.21/0.51  ipcrm: permission denied for id (816414847)
% 0.21/0.63  % (6222)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.63  % (6229)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.63  % (6222)Refutation found. Thanks to Tanya!
% 0.21/0.63  % SZS status Theorem for theBenchmark
% 0.21/0.63  % SZS output start Proof for theBenchmark
% 0.21/0.63  fof(f241,plain,(
% 0.21/0.63    $false),
% 0.21/0.63    inference(avatar_sat_refutation,[],[f132,f143,f161,f188,f214,f240])).
% 0.21/0.63  fof(f240,plain,(
% 0.21/0.63    ~spl4_2),
% 0.21/0.63    inference(avatar_contradiction_clause,[],[f239])).
% 0.21/0.63  fof(f239,plain,(
% 0.21/0.63    $false | ~spl4_2),
% 0.21/0.63    inference(subsumption_resolution,[],[f222,f91])).
% 0.21/0.63  fof(f91,plain,(
% 0.21/0.63    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.63    inference(superposition,[],[f30,f72])).
% 0.21/0.63  fof(f72,plain,(
% 0.21/0.63    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.63    inference(equality_resolution,[],[f34])).
% 0.21/0.63  fof(f34,plain,(
% 0.21/0.63    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.63    inference(cnf_transformation,[],[f22])).
% 0.21/0.63  fof(f22,plain,(
% 0.21/0.63    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.63    inference(flattening,[],[f21])).
% 0.21/0.63  fof(f21,plain,(
% 0.21/0.63    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.63    inference(nnf_transformation,[],[f8])).
% 0.21/0.63  fof(f8,axiom,(
% 0.21/0.63    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.63  fof(f30,plain,(
% 0.21/0.63    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.63    inference(cnf_transformation,[],[f9])).
% 0.21/0.63  fof(f9,axiom,(
% 0.21/0.63    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.63  fof(f222,plain,(
% 0.21/0.63    r2_hidden(sK2,k1_xboole_0) | ~spl4_2),
% 0.21/0.63    inference(superposition,[],[f89,f127])).
% 0.21/0.63  fof(f127,plain,(
% 0.21/0.63    k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl4_2),
% 0.21/0.63    inference(avatar_component_clause,[],[f125])).
% 0.21/0.63  fof(f125,plain,(
% 0.21/0.63    spl4_2 <=> k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 0.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.63  fof(f89,plain,(
% 0.21/0.63    ( ! [X6,X4,X2,X10,X7,X5,X3,X1] : (r2_hidden(X10,k6_enumset1(X10,X1,X2,X3,X4,X5,X6,X7))) )),
% 0.21/0.63    inference(equality_resolution,[],[f88])).
% 0.21/0.63  fof(f88,plain,(
% 0.21/0.63    ( ! [X6,X4,X2,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | k6_enumset1(X10,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 0.21/0.63    inference(equality_resolution,[],[f46])).
% 0.21/0.63  fof(f46,plain,(
% 0.21/0.63    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | X0 != X10 | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 0.21/0.63    inference(cnf_transformation,[],[f27])).
% 0.21/0.63  fof(f27,plain,(
% 0.21/0.63    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | (((sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~r2_hidden(X10,X8))) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 0.21/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 0.21/0.63  fof(f26,plain,(
% 0.21/0.63    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | r2_hidden(X9,X8))) => (((sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 0.21/0.63    introduced(choice_axiom,[])).
% 0.21/0.63  fof(f25,plain,(
% 0.21/0.63    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~r2_hidden(X10,X8))) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 0.21/0.63    inference(rectify,[],[f24])).
% 0.21/0.63  fof(f24,plain,(
% 0.21/0.63    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~r2_hidden(X9,X8))) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 0.21/0.63    inference(flattening,[],[f23])).
% 0.21/0.63  fof(f23,plain,(
% 0.21/0.63    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~r2_hidden(X9,X8))) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 0.21/0.63    inference(nnf_transformation,[],[f18])).
% 0.21/0.63  fof(f18,plain,(
% 0.21/0.63    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 0.21/0.63    inference(ennf_transformation,[],[f11])).
% 0.21/0.63  fof(f11,axiom,(
% 0.21/0.63    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).
% 0.21/0.63  fof(f214,plain,(
% 0.21/0.63    ~spl4_5),
% 0.21/0.63    inference(avatar_contradiction_clause,[],[f213])).
% 0.21/0.63  fof(f213,plain,(
% 0.21/0.63    $false | ~spl4_5),
% 0.21/0.63    inference(subsumption_resolution,[],[f196,f91])).
% 0.21/0.63  fof(f196,plain,(
% 0.21/0.63    r2_hidden(sK1,k1_xboole_0) | ~spl4_5),
% 0.21/0.63    inference(superposition,[],[f89,f142])).
% 0.21/0.63  fof(f142,plain,(
% 0.21/0.63    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl4_5),
% 0.21/0.63    inference(avatar_component_clause,[],[f140])).
% 0.21/0.63  fof(f140,plain,(
% 0.21/0.63    spl4_5 <=> k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 0.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.63  fof(f188,plain,(
% 0.21/0.63    ~spl4_4),
% 0.21/0.63    inference(avatar_contradiction_clause,[],[f187])).
% 0.21/0.63  fof(f187,plain,(
% 0.21/0.63    $false | ~spl4_4),
% 0.21/0.63    inference(subsumption_resolution,[],[f170,f91])).
% 0.21/0.63  fof(f170,plain,(
% 0.21/0.63    r2_hidden(sK0,k1_xboole_0) | ~spl4_4),
% 0.21/0.63    inference(superposition,[],[f89,f138])).
% 0.21/0.63  fof(f138,plain,(
% 0.21/0.63    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl4_4),
% 0.21/0.63    inference(avatar_component_clause,[],[f136])).
% 0.21/0.63  fof(f136,plain,(
% 0.21/0.63    spl4_4 <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.63  fof(f161,plain,(
% 0.21/0.63    spl4_5 | spl4_4 | ~spl4_1),
% 0.21/0.63    inference(avatar_split_clause,[],[f149,f121,f136,f140])).
% 0.21/0.63  fof(f121,plain,(
% 0.21/0.63    spl4_1 <=> k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.63  fof(f149,plain,(
% 0.21/0.63    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl4_1),
% 0.21/0.63    inference(trivial_inequality_removal,[],[f147])).
% 0.21/0.63  fof(f147,plain,(
% 0.21/0.63    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl4_1),
% 0.21/0.63    inference(superposition,[],[f32,f123])).
% 0.21/0.63  fof(f123,plain,(
% 0.21/0.63    k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl4_1),
% 0.21/0.63    inference(avatar_component_clause,[],[f121])).
% 0.21/0.63  fof(f32,plain,(
% 0.21/0.63    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.21/0.63    inference(cnf_transformation,[],[f22])).
% 0.21/0.63  fof(f143,plain,(
% 0.21/0.63    spl4_4 | spl4_5 | spl4_3),
% 0.21/0.63    inference(avatar_split_clause,[],[f134,f129,f140,f136])).
% 0.21/0.63  fof(f129,plain,(
% 0.21/0.63    spl4_3 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 0.21/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.63  fof(f134,plain,(
% 0.21/0.63    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl4_3),
% 0.21/0.63    inference(trivial_inequality_removal,[],[f133])).
% 0.21/0.63  fof(f133,plain,(
% 0.21/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl4_3),
% 0.21/0.63    inference(superposition,[],[f131,f35])).
% 0.21/0.63  fof(f35,plain,(
% 0.21/0.63    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.63    inference(cnf_transformation,[],[f17])).
% 0.21/0.63  fof(f17,plain,(
% 0.21/0.63    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.63    inference(ennf_transformation,[],[f12])).
% 0.21/0.63  fof(f12,axiom,(
% 0.21/0.63    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.21/0.63  fof(f131,plain,(
% 0.21/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | spl4_3),
% 0.21/0.63    inference(avatar_component_clause,[],[f129])).
% 0.21/0.63  fof(f132,plain,(
% 0.21/0.63    spl4_1 | spl4_2 | ~spl4_3),
% 0.21/0.63    inference(avatar_split_clause,[],[f119,f129,f125,f121])).
% 0.21/0.63  fof(f119,plain,(
% 0.21/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.21/0.63    inference(superposition,[],[f118,f35])).
% 0.21/0.63  fof(f118,plain,(
% 0.21/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 0.21/0.63    inference(forward_demodulation,[],[f107,f70])).
% 0.21/0.63  fof(f70,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.21/0.63    inference(definition_unfolding,[],[f40,f67,f68,f67])).
% 0.21/0.63  fof(f68,plain,(
% 0.21/0.63    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.63    inference(definition_unfolding,[],[f29,f67])).
% 0.21/0.63  fof(f29,plain,(
% 0.21/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f1])).
% 0.21/0.63  fof(f1,axiom,(
% 0.21/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.63  fof(f67,plain,(
% 0.21/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.63    inference(definition_unfolding,[],[f31,f66])).
% 0.21/0.63  fof(f66,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.63    inference(definition_unfolding,[],[f38,f65])).
% 0.21/0.63  fof(f65,plain,(
% 0.21/0.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.63    inference(definition_unfolding,[],[f41,f64])).
% 0.21/0.63  fof(f64,plain,(
% 0.21/0.63    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.63    inference(definition_unfolding,[],[f42,f63])).
% 0.21/0.63  fof(f63,plain,(
% 0.21/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.63    inference(definition_unfolding,[],[f43,f44])).
% 0.21/0.63  fof(f44,plain,(
% 0.21/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f7])).
% 0.21/0.63  fof(f7,axiom,(
% 0.21/0.63    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.63  fof(f43,plain,(
% 0.21/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f6])).
% 0.21/0.63  fof(f6,axiom,(
% 0.21/0.63    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.63  fof(f42,plain,(
% 0.21/0.63    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f5])).
% 0.21/0.63  fof(f5,axiom,(
% 0.21/0.63    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.63  fof(f41,plain,(
% 0.21/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f4])).
% 0.21/0.63  fof(f4,axiom,(
% 0.21/0.63    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.63  fof(f38,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f3])).
% 0.21/0.63  fof(f3,axiom,(
% 0.21/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.63  fof(f31,plain,(
% 0.21/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f2])).
% 0.21/0.63  fof(f2,axiom,(
% 0.21/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.63  fof(f40,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.21/0.63    inference(cnf_transformation,[],[f10])).
% 0.21/0.63  fof(f10,axiom,(
% 0.21/0.63    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.21/0.63  fof(f107,plain,(
% 0.21/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 0.21/0.63    inference(backward_demodulation,[],[f69,f70])).
% 0.21/0.63  fof(f69,plain,(
% 0.21/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),
% 0.21/0.63    inference(definition_unfolding,[],[f28,f68,f68,f37])).
% 0.21/0.63  fof(f37,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f13])).
% 0.21/0.63  fof(f13,axiom,(
% 0.21/0.63    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.63  fof(f28,plain,(
% 0.21/0.63    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.21/0.63    inference(cnf_transformation,[],[f20])).
% 0.21/0.63  fof(f20,plain,(
% 0.21/0.63    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.21/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).
% 0.21/0.63  fof(f19,plain,(
% 0.21/0.63    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.21/0.63    introduced(choice_axiom,[])).
% 0.21/0.63  fof(f16,plain,(
% 0.21/0.63    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.21/0.63    inference(ennf_transformation,[],[f15])).
% 0.21/0.63  fof(f15,negated_conjecture,(
% 0.21/0.63    ~! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.21/0.63    inference(negated_conjecture,[],[f14])).
% 0.21/0.63  fof(f14,conjecture,(
% 0.21/0.63    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).
% 0.21/0.63  % SZS output end Proof for theBenchmark
% 0.21/0.63  % (6222)------------------------------
% 0.21/0.63  % (6222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.63  % (6222)Termination reason: Refutation
% 0.21/0.63  
% 0.21/0.63  % (6222)Memory used [KB]: 10874
% 0.21/0.63  % (6222)Time elapsed: 0.082 s
% 0.21/0.63  % (6222)------------------------------
% 0.21/0.63  % (6222)------------------------------
% 0.21/0.63  % (6085)Success in time 0.275 s
%------------------------------------------------------------------------------
