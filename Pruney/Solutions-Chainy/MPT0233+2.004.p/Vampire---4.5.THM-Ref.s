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
% DateTime   : Thu Dec  3 12:37:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 435 expanded)
%              Number of leaves         :   22 ( 115 expanded)
%              Depth                    :   19
%              Number of atoms          :  446 (2257 expanded)
%              Number of equality atoms :  265 (1519 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f596,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f154,f374,f470,f561,f595])).

fof(f595,plain,
    ( ~ spl7_1
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f594])).

fof(f594,plain,
    ( $false
    | ~ spl7_1
    | spl7_4 ),
    inference(subsumption_resolution,[],[f593,f587])).

fof(f587,plain,
    ( k2_tarski(sK1,sK2) != k2_tarski(sK2,sK2)
    | ~ spl7_1
    | spl7_4 ),
    inference(forward_demodulation,[],[f152,f583])).

fof(f583,plain,
    ( sK2 = sK4
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f582,f53])).

fof(f53,plain,(
    sK1 != sK4 ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( sK1 != sK4
    & sK1 != sK3
    & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK1 != sK4
      & sK1 != sK3
      & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f582,plain,
    ( sK1 = sK4
    | sK2 = sK4
    | ~ spl7_1 ),
    inference(resolution,[],[f576,f118])).

fof(f118,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK5(X0,X1,X2) != X1
              & sK5(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X1
            | sK5(X0,X1,X2) = X0
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X1
            & sK5(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X1
          | sK5(X0,X1,X2) = X0
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f576,plain,
    ( r2_hidden(sK4,k2_tarski(sK1,sK2))
    | ~ spl7_1 ),
    inference(superposition,[],[f115,f141])).

fof(f141,plain,
    ( k2_tarski(sK1,sK2) = k2_tarski(sK3,sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl7_1
  <=> k2_tarski(sK1,sK2) = k2_tarski(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f115,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f152,plain,
    ( k2_tarski(sK1,sK2) != k2_tarski(sK4,sK4)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl7_4
  <=> k2_tarski(sK1,sK2) = k2_tarski(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f593,plain,
    ( k2_tarski(sK1,sK2) = k2_tarski(sK2,sK2)
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f584,f589])).

fof(f589,plain,
    ( sK2 = sK3
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f588,f52])).

fof(f52,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f37])).

fof(f588,plain,
    ( sK1 = sK3
    | sK2 = sK3
    | ~ spl7_1 ),
    inference(resolution,[],[f577,f118])).

fof(f577,plain,
    ( r2_hidden(sK3,k2_tarski(sK1,sK2))
    | ~ spl7_1 ),
    inference(superposition,[],[f117,f141])).

fof(f117,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f584,plain,
    ( k2_tarski(sK1,sK2) = k2_tarski(sK3,sK2)
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f141,f583])).

fof(f561,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f560])).

fof(f560,plain,
    ( $false
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f558,f509])).

fof(f509,plain,
    ( sK1 != sK2
    | ~ spl7_4 ),
    inference(superposition,[],[f53,f505])).

fof(f505,plain,
    ( sK2 = sK4
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f504,f53])).

fof(f504,plain,
    ( sK1 = sK4
    | sK2 = sK4
    | ~ spl7_4 ),
    inference(resolution,[],[f483,f118])).

fof(f483,plain,
    ( r2_hidden(sK4,k2_tarski(sK1,sK2))
    | ~ spl7_4 ),
    inference(superposition,[],[f115,f153])).

fof(f153,plain,
    ( k2_tarski(sK1,sK2) = k2_tarski(sK4,sK4)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f151])).

fof(f558,plain,
    ( sK1 = sK2
    | ~ spl7_4 ),
    inference(resolution,[],[f535,f117])).

fof(f535,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,k2_tarski(sK1,sK2))
        | sK2 = X9 )
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f526])).

fof(f526,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,k2_tarski(sK1,sK2))
        | sK2 = X9
        | sK2 = X9 )
    | ~ spl7_4 ),
    inference(superposition,[],[f118,f507])).

fof(f507,plain,
    ( k2_tarski(sK1,sK2) = k2_tarski(sK2,sK2)
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f153,f505])).

fof(f470,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f467,f413])).

fof(f413,plain,
    ( sK1 != sK2
    | ~ spl7_3 ),
    inference(superposition,[],[f52,f409])).

fof(f409,plain,
    ( sK2 = sK3
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f408,f52])).

fof(f408,plain,
    ( sK1 = sK3
    | sK2 = sK3
    | ~ spl7_3 ),
    inference(resolution,[],[f387,f118])).

fof(f387,plain,
    ( r2_hidden(sK3,k2_tarski(sK1,sK2))
    | ~ spl7_3 ),
    inference(superposition,[],[f115,f149])).

fof(f149,plain,
    ( k2_tarski(sK1,sK2) = k2_tarski(sK3,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl7_3
  <=> k2_tarski(sK1,sK2) = k2_tarski(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f467,plain,
    ( sK1 = sK2
    | ~ spl7_3 ),
    inference(resolution,[],[f438,f117])).

fof(f438,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,k2_tarski(sK1,sK2))
        | sK2 = X9 )
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f429])).

fof(f429,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,k2_tarski(sK1,sK2))
        | sK2 = X9
        | sK2 = X9 )
    | ~ spl7_3 ),
    inference(superposition,[],[f118,f411])).

fof(f411,plain,
    ( k2_tarski(sK1,sK2) = k2_tarski(sK2,sK2)
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f149,f409])).

fof(f374,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f373])).

fof(f373,plain,
    ( $false
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f372,f53])).

fof(f372,plain,
    ( sK1 = sK4
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f371,f52])).

fof(f371,plain,
    ( sK1 = sK3
    | sK1 = sK4
    | ~ spl7_2 ),
    inference(resolution,[],[f364,f118])).

fof(f364,plain,
    ( r2_hidden(sK1,k2_tarski(sK3,sK4))
    | ~ spl7_2 ),
    inference(resolution,[],[f353,f121])).

fof(f121,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK6(X0,X1,X2,X3) != X0
              & sK6(X0,X1,X2,X3) != X1
              & sK6(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( sK6(X0,X1,X2,X3) = X0
            | sK6(X0,X1,X2,X3) = X1
            | sK6(X0,X1,X2,X3) = X2
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f47,f48])).

fof(f48,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK6(X0,X1,X2,X3) != X0
            & sK6(X0,X1,X2,X3) != X1
            & sK6(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( sK6(X0,X1,X2,X3) = X0
          | sK6(X0,X1,X2,X3) = X1
          | sK6(X0,X1,X2,X3) = X2
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f353,plain,
    ( sP0(sK4,sK3,sK1,k2_tarski(sK3,sK4))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f352,f189])).

fof(f189,plain,
    ( k2_tarski(sK3,sK4) = k5_xboole_0(k1_xboole_0,k2_tarski(sK3,sK4))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f188,f73])).

fof(f73,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f188,plain,
    ( k2_tarski(sK3,sK4) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK3,sK4),k1_xboole_0))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f187,f156])).

fof(f156,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_tarski(sK3,sK4))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f124,f145])).

fof(f145,plain,
    ( k1_xboole_0 = k2_tarski(sK1,sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl7_2
  <=> k1_xboole_0 = k2_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f124,plain,(
    k2_tarski(sK1,sK2) = k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(resolution,[],[f51,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f51,plain,(
    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f187,plain,
    ( k2_tarski(sK3,sK4) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK3,sK4),k3_xboole_0(k1_xboole_0,k2_tarski(sK3,sK4))))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f186,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f186,plain,
    ( k2_tarski(sK3,sK4) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK3,sK4),k3_xboole_0(k2_tarski(sK3,sK4),k1_xboole_0)))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f185,f73])).

fof(f185,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK3,sK4),k3_xboole_0(k2_tarski(sK3,sK4),k1_xboole_0))) = k5_xboole_0(k2_tarski(sK3,sK4),k1_xboole_0)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f181,f73])).

fof(f181,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK3,sK4),k3_xboole_0(k2_tarski(sK3,sK4),k1_xboole_0))) = k5_xboole_0(k2_tarski(sK3,sK4),k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl7_2 ),
    inference(superposition,[],[f105,f156])).

fof(f105,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f79,f95,f95])).

fof(f95,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f78,f75])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f352,plain,
    ( sP0(sK4,sK3,sK1,k5_xboole_0(k1_xboole_0,k2_tarski(sK3,sK4)))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f346,f73])).

fof(f346,plain,
    ( sP0(sK4,sK3,sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK3,sK4),k1_xboole_0)))
    | ~ spl7_2 ),
    inference(superposition,[],[f272,f156])).

fof(f272,plain,
    ( ! [X23,X22] : sP0(X22,X23,sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(X23,X22),k3_xboole_0(k1_xboole_0,k2_tarski(X23,X22)))))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f257,f76])).

fof(f257,plain,
    ( ! [X23,X22] : sP0(X22,X23,sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(X23,X22),k3_xboole_0(k2_tarski(X23,X22),k1_xboole_0))))
    | ~ spl7_2 ),
    inference(superposition,[],[f122,f199])).

fof(f199,plain,
    ( k1_xboole_0 = k2_tarski(sK1,sK1)
    | ~ spl7_2 ),
    inference(resolution,[],[f165,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f165,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),k1_xboole_0)
    | ~ spl7_2 ),
    inference(superposition,[],[f112,f145])).

fof(f112,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f56,f71])).

fof(f71,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f122,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(definition_unfolding,[],[f90,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f81,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f63,f95])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f33,f34])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f154,plain,
    ( spl7_1
    | spl7_2
    | spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f123,f151,f147,f143,f139])).

fof(f123,plain,
    ( k2_tarski(sK1,sK2) = k2_tarski(sK4,sK4)
    | k2_tarski(sK1,sK2) = k2_tarski(sK3,sK3)
    | k1_xboole_0 = k2_tarski(sK1,sK2)
    | k2_tarski(sK1,sK2) = k2_tarski(sK3,sK4) ),
    inference(resolution,[],[f51,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0
      | k2_tarski(X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f54,f71,f71])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:12:38 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.52  % (8799)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (8791)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (8807)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (8796)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (8783)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (8782)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (8791)Refutation not found, incomplete strategy% (8791)------------------------------
% 0.21/0.53  % (8791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8791)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (8791)Memory used [KB]: 10618
% 0.21/0.53  % (8791)Time elapsed: 0.116 s
% 0.21/0.53  % (8791)------------------------------
% 0.21/0.53  % (8791)------------------------------
% 0.21/0.53  % (8784)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (8779)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (8785)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (8786)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (8780)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (8780)Refutation not found, incomplete strategy% (8780)------------------------------
% 0.21/0.54  % (8780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8780)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8780)Memory used [KB]: 1663
% 0.21/0.54  % (8780)Time elapsed: 0.125 s
% 0.21/0.54  % (8780)------------------------------
% 0.21/0.54  % (8780)------------------------------
% 0.21/0.54  % (8801)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (8805)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (8804)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (8798)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (8795)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (8802)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (8808)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (8787)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (8803)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (8800)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (8790)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (8806)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (8788)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (8795)Refutation not found, incomplete strategy% (8795)------------------------------
% 0.21/0.55  % (8795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8797)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (8793)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (8794)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (8792)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.57  % (8795)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (8795)Memory used [KB]: 10746
% 0.21/0.57  % (8795)Time elapsed: 0.139 s
% 0.21/0.57  % (8795)------------------------------
% 0.21/0.57  % (8795)------------------------------
% 0.21/0.57  % (8808)Refutation not found, incomplete strategy% (8808)------------------------------
% 0.21/0.57  % (8808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (8808)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (8808)Memory used [KB]: 1663
% 0.21/0.57  % (8808)Time elapsed: 0.003 s
% 0.21/0.57  % (8808)------------------------------
% 0.21/0.57  % (8808)------------------------------
% 0.21/0.57  % (8803)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f596,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f154,f374,f470,f561,f595])).
% 0.21/0.57  fof(f595,plain,(
% 0.21/0.57    ~spl7_1 | spl7_4),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f594])).
% 0.21/0.57  fof(f594,plain,(
% 0.21/0.57    $false | (~spl7_1 | spl7_4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f593,f587])).
% 0.21/0.57  fof(f587,plain,(
% 0.21/0.57    k2_tarski(sK1,sK2) != k2_tarski(sK2,sK2) | (~spl7_1 | spl7_4)),
% 0.21/0.57    inference(forward_demodulation,[],[f152,f583])).
% 0.21/0.57  fof(f583,plain,(
% 0.21/0.57    sK2 = sK4 | ~spl7_1),
% 0.21/0.57    inference(subsumption_resolution,[],[f582,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    sK1 != sK4),
% 0.21/0.57    inference(cnf_transformation,[],[f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.21/0.57    inference(ennf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.21/0.57    inference(negated_conjecture,[],[f25])).
% 0.21/0.57  fof(f25,conjecture,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 0.21/0.57  fof(f582,plain,(
% 0.21/0.57    sK1 = sK4 | sK2 = sK4 | ~spl7_1),
% 0.21/0.57    inference(resolution,[],[f576,f118])).
% 0.21/0.57  fof(f118,plain,(
% 0.21/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.21/0.57    inference(equality_resolution,[],[f64])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.57    inference(rectify,[],[f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.57    inference(flattening,[],[f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.57    inference(nnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.57  fof(f576,plain,(
% 0.21/0.57    r2_hidden(sK4,k2_tarski(sK1,sK2)) | ~spl7_1),
% 0.21/0.57    inference(superposition,[],[f115,f141])).
% 0.21/0.57  fof(f141,plain,(
% 0.21/0.57    k2_tarski(sK1,sK2) = k2_tarski(sK3,sK4) | ~spl7_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f139])).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    spl7_1 <=> k2_tarski(sK1,sK2) = k2_tarski(sK3,sK4)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.57  fof(f115,plain,(
% 0.21/0.57    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 0.21/0.57    inference(equality_resolution,[],[f114])).
% 0.21/0.57  fof(f114,plain,(
% 0.21/0.57    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 0.21/0.57    inference(equality_resolution,[],[f66])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f44])).
% 0.21/0.57  fof(f152,plain,(
% 0.21/0.57    k2_tarski(sK1,sK2) != k2_tarski(sK4,sK4) | spl7_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f151])).
% 0.21/0.57  fof(f151,plain,(
% 0.21/0.57    spl7_4 <=> k2_tarski(sK1,sK2) = k2_tarski(sK4,sK4)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.57  fof(f593,plain,(
% 0.21/0.57    k2_tarski(sK1,sK2) = k2_tarski(sK2,sK2) | ~spl7_1),
% 0.21/0.57    inference(forward_demodulation,[],[f584,f589])).
% 0.21/0.57  fof(f589,plain,(
% 0.21/0.57    sK2 = sK3 | ~spl7_1),
% 0.21/0.57    inference(subsumption_resolution,[],[f588,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    sK1 != sK3),
% 0.21/0.57    inference(cnf_transformation,[],[f37])).
% 0.21/0.57  fof(f588,plain,(
% 0.21/0.57    sK1 = sK3 | sK2 = sK3 | ~spl7_1),
% 0.21/0.57    inference(resolution,[],[f577,f118])).
% 0.21/0.57  fof(f577,plain,(
% 0.21/0.57    r2_hidden(sK3,k2_tarski(sK1,sK2)) | ~spl7_1),
% 0.21/0.57    inference(superposition,[],[f117,f141])).
% 0.21/0.57  fof(f117,plain,(
% 0.21/0.57    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 0.21/0.57    inference(equality_resolution,[],[f116])).
% 0.21/0.57  fof(f116,plain,(
% 0.21/0.57    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 0.21/0.57    inference(equality_resolution,[],[f65])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f44])).
% 0.21/0.57  fof(f584,plain,(
% 0.21/0.57    k2_tarski(sK1,sK2) = k2_tarski(sK3,sK2) | ~spl7_1),
% 0.21/0.57    inference(backward_demodulation,[],[f141,f583])).
% 0.21/0.57  fof(f561,plain,(
% 0.21/0.57    ~spl7_4),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f560])).
% 0.21/0.57  fof(f560,plain,(
% 0.21/0.57    $false | ~spl7_4),
% 0.21/0.57    inference(subsumption_resolution,[],[f558,f509])).
% 0.21/0.57  fof(f509,plain,(
% 0.21/0.57    sK1 != sK2 | ~spl7_4),
% 0.21/0.57    inference(superposition,[],[f53,f505])).
% 0.21/0.57  fof(f505,plain,(
% 0.21/0.57    sK2 = sK4 | ~spl7_4),
% 0.21/0.57    inference(subsumption_resolution,[],[f504,f53])).
% 0.21/0.57  fof(f504,plain,(
% 0.21/0.57    sK1 = sK4 | sK2 = sK4 | ~spl7_4),
% 0.21/0.57    inference(resolution,[],[f483,f118])).
% 0.21/0.57  fof(f483,plain,(
% 0.21/0.57    r2_hidden(sK4,k2_tarski(sK1,sK2)) | ~spl7_4),
% 0.21/0.57    inference(superposition,[],[f115,f153])).
% 0.21/0.57  fof(f153,plain,(
% 0.21/0.57    k2_tarski(sK1,sK2) = k2_tarski(sK4,sK4) | ~spl7_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f151])).
% 0.21/0.57  fof(f558,plain,(
% 0.21/0.57    sK1 = sK2 | ~spl7_4),
% 0.21/0.57    inference(resolution,[],[f535,f117])).
% 0.21/0.57  fof(f535,plain,(
% 0.21/0.57    ( ! [X9] : (~r2_hidden(X9,k2_tarski(sK1,sK2)) | sK2 = X9) ) | ~spl7_4),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f526])).
% 0.21/0.57  fof(f526,plain,(
% 0.21/0.57    ( ! [X9] : (~r2_hidden(X9,k2_tarski(sK1,sK2)) | sK2 = X9 | sK2 = X9) ) | ~spl7_4),
% 0.21/0.57    inference(superposition,[],[f118,f507])).
% 0.21/0.57  fof(f507,plain,(
% 0.21/0.57    k2_tarski(sK1,sK2) = k2_tarski(sK2,sK2) | ~spl7_4),
% 0.21/0.57    inference(backward_demodulation,[],[f153,f505])).
% 0.21/0.57  fof(f470,plain,(
% 0.21/0.57    ~spl7_3),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f469])).
% 0.21/0.57  fof(f469,plain,(
% 0.21/0.57    $false | ~spl7_3),
% 0.21/0.57    inference(subsumption_resolution,[],[f467,f413])).
% 0.21/0.57  fof(f413,plain,(
% 0.21/0.57    sK1 != sK2 | ~spl7_3),
% 0.21/0.57    inference(superposition,[],[f52,f409])).
% 0.21/0.57  fof(f409,plain,(
% 0.21/0.57    sK2 = sK3 | ~spl7_3),
% 0.21/0.57    inference(subsumption_resolution,[],[f408,f52])).
% 0.21/0.57  fof(f408,plain,(
% 0.21/0.57    sK1 = sK3 | sK2 = sK3 | ~spl7_3),
% 0.21/0.57    inference(resolution,[],[f387,f118])).
% 0.21/0.57  fof(f387,plain,(
% 0.21/0.57    r2_hidden(sK3,k2_tarski(sK1,sK2)) | ~spl7_3),
% 0.21/0.57    inference(superposition,[],[f115,f149])).
% 0.21/0.57  fof(f149,plain,(
% 0.21/0.57    k2_tarski(sK1,sK2) = k2_tarski(sK3,sK3) | ~spl7_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f147])).
% 0.21/0.57  fof(f147,plain,(
% 0.21/0.57    spl7_3 <=> k2_tarski(sK1,sK2) = k2_tarski(sK3,sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.57  fof(f467,plain,(
% 0.21/0.57    sK1 = sK2 | ~spl7_3),
% 0.21/0.57    inference(resolution,[],[f438,f117])).
% 0.21/0.57  fof(f438,plain,(
% 0.21/0.57    ( ! [X9] : (~r2_hidden(X9,k2_tarski(sK1,sK2)) | sK2 = X9) ) | ~spl7_3),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f429])).
% 0.21/0.57  fof(f429,plain,(
% 0.21/0.57    ( ! [X9] : (~r2_hidden(X9,k2_tarski(sK1,sK2)) | sK2 = X9 | sK2 = X9) ) | ~spl7_3),
% 0.21/0.57    inference(superposition,[],[f118,f411])).
% 0.21/0.57  fof(f411,plain,(
% 0.21/0.57    k2_tarski(sK1,sK2) = k2_tarski(sK2,sK2) | ~spl7_3),
% 0.21/0.57    inference(backward_demodulation,[],[f149,f409])).
% 0.21/0.57  fof(f374,plain,(
% 0.21/0.57    ~spl7_2),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f373])).
% 0.21/0.57  fof(f373,plain,(
% 0.21/0.57    $false | ~spl7_2),
% 0.21/0.57    inference(subsumption_resolution,[],[f372,f53])).
% 0.21/0.57  fof(f372,plain,(
% 0.21/0.57    sK1 = sK4 | ~spl7_2),
% 0.21/0.57    inference(subsumption_resolution,[],[f371,f52])).
% 0.21/0.57  fof(f371,plain,(
% 0.21/0.57    sK1 = sK3 | sK1 = sK4 | ~spl7_2),
% 0.21/0.57    inference(resolution,[],[f364,f118])).
% 0.21/0.57  fof(f364,plain,(
% 0.21/0.57    r2_hidden(sK1,k2_tarski(sK3,sK4)) | ~spl7_2),
% 0.21/0.57    inference(resolution,[],[f353,f121])).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    ( ! [X0,X5,X3,X1] : (~sP0(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 0.21/0.57    inference(equality_resolution,[],[f83])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f47,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.57    inference(rectify,[],[f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.21/0.57    inference(flattening,[],[f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.21/0.57    inference(nnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.57  fof(f353,plain,(
% 0.21/0.57    sP0(sK4,sK3,sK1,k2_tarski(sK3,sK4)) | ~spl7_2),
% 0.21/0.57    inference(forward_demodulation,[],[f352,f189])).
% 0.21/0.57  fof(f189,plain,(
% 0.21/0.57    k2_tarski(sK3,sK4) = k5_xboole_0(k1_xboole_0,k2_tarski(sK3,sK4)) | ~spl7_2),
% 0.21/0.57    inference(forward_demodulation,[],[f188,f73])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.57  fof(f188,plain,(
% 0.21/0.57    k2_tarski(sK3,sK4) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK3,sK4),k1_xboole_0)) | ~spl7_2),
% 0.21/0.57    inference(forward_demodulation,[],[f187,f156])).
% 0.21/0.57  fof(f156,plain,(
% 0.21/0.57    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_tarski(sK3,sK4)) | ~spl7_2),
% 0.21/0.57    inference(backward_demodulation,[],[f124,f145])).
% 0.21/0.57  fof(f145,plain,(
% 0.21/0.57    k1_xboole_0 = k2_tarski(sK1,sK2) | ~spl7_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f143])).
% 0.21/0.57  fof(f143,plain,(
% 0.21/0.57    spl7_2 <=> k1_xboole_0 = k2_tarski(sK1,sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.57  fof(f124,plain,(
% 0.21/0.57    k2_tarski(sK1,sK2) = k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 0.21/0.57    inference(resolution,[],[f51,f60])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 0.21/0.57    inference(cnf_transformation,[],[f37])).
% 0.21/0.57  fof(f187,plain,(
% 0.21/0.57    k2_tarski(sK3,sK4) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK3,sK4),k3_xboole_0(k1_xboole_0,k2_tarski(sK3,sK4)))) | ~spl7_2),
% 0.21/0.57    inference(forward_demodulation,[],[f186,f76])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.57  fof(f186,plain,(
% 0.21/0.57    k2_tarski(sK3,sK4) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK3,sK4),k3_xboole_0(k2_tarski(sK3,sK4),k1_xboole_0))) | ~spl7_2),
% 0.21/0.57    inference(forward_demodulation,[],[f185,f73])).
% 0.21/0.57  fof(f185,plain,(
% 0.21/0.57    k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK3,sK4),k3_xboole_0(k2_tarski(sK3,sK4),k1_xboole_0))) = k5_xboole_0(k2_tarski(sK3,sK4),k1_xboole_0) | ~spl7_2),
% 0.21/0.57    inference(forward_demodulation,[],[f181,f73])).
% 0.21/0.57  fof(f181,plain,(
% 0.21/0.57    k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK3,sK4),k3_xboole_0(k2_tarski(sK3,sK4),k1_xboole_0))) = k5_xboole_0(k2_tarski(sK3,sK4),k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl7_2),
% 0.21/0.57    inference(superposition,[],[f105,f156])).
% 0.21/0.57  fof(f105,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f79,f95,f95])).
% 0.21/0.57  fof(f95,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f78,f75])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.57  fof(f352,plain,(
% 0.21/0.57    sP0(sK4,sK3,sK1,k5_xboole_0(k1_xboole_0,k2_tarski(sK3,sK4))) | ~spl7_2),
% 0.21/0.57    inference(forward_demodulation,[],[f346,f73])).
% 0.21/0.57  fof(f346,plain,(
% 0.21/0.57    sP0(sK4,sK3,sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK3,sK4),k1_xboole_0))) | ~spl7_2),
% 0.21/0.57    inference(superposition,[],[f272,f156])).
% 0.21/0.57  fof(f272,plain,(
% 0.21/0.57    ( ! [X23,X22] : (sP0(X22,X23,sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(X23,X22),k3_xboole_0(k1_xboole_0,k2_tarski(X23,X22)))))) ) | ~spl7_2),
% 0.21/0.57    inference(forward_demodulation,[],[f257,f76])).
% 0.21/0.57  fof(f257,plain,(
% 0.21/0.57    ( ! [X23,X22] : (sP0(X22,X23,sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(X23,X22),k3_xboole_0(k2_tarski(X23,X22),k1_xboole_0))))) ) | ~spl7_2),
% 0.21/0.57    inference(superposition,[],[f122,f199])).
% 0.21/0.57  fof(f199,plain,(
% 0.21/0.57    k1_xboole_0 = k2_tarski(sK1,sK1) | ~spl7_2),
% 0.21/0.57    inference(resolution,[],[f165,f62])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.57  fof(f165,plain,(
% 0.21/0.57    r1_tarski(k2_tarski(sK1,sK1),k1_xboole_0) | ~spl7_2),
% 0.21/0.57    inference(superposition,[],[f112,f145])).
% 0.21/0.57  fof(f112,plain,(
% 0.21/0.57    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2))) )),
% 0.21/0.57    inference(equality_resolution,[],[f102])).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X1) != X0) )),
% 0.21/0.57    inference(definition_unfolding,[],[f56,f71])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,axiom,(
% 0.21/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.57    inference(flattening,[],[f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.57    inference(nnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))))) )),
% 0.21/0.57    inference(equality_resolution,[],[f108])).
% 0.21/0.57  fof(f108,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3) )),
% 0.21/0.57    inference(definition_unfolding,[],[f90,f97])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f81,f96])).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f63,f95])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.57    inference(cnf_transformation,[],[f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.57    inference(nnf_transformation,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 0.21/0.57    inference(definition_folding,[],[f33,f34])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.57  fof(f154,plain,(
% 0.21/0.57    spl7_1 | spl7_2 | spl7_3 | spl7_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f123,f151,f147,f143,f139])).
% 0.21/0.57  fof(f123,plain,(
% 0.21/0.57    k2_tarski(sK1,sK2) = k2_tarski(sK4,sK4) | k2_tarski(sK1,sK2) = k2_tarski(sK3,sK3) | k1_xboole_0 = k2_tarski(sK1,sK2) | k2_tarski(sK1,sK2) = k2_tarski(sK3,sK4)),
% 0.21/0.57    inference(resolution,[],[f51,f103])).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X2,X2) = X0 | k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0 | k2_tarski(X1,X2) = X0) )),
% 0.21/0.57    inference(definition_unfolding,[],[f54,f71,f71])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (8803)------------------------------
% 0.21/0.57  % (8803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (8803)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (8803)Memory used [KB]: 11001
% 0.21/0.57  % (8803)Time elapsed: 0.147 s
% 0.21/0.57  % (8803)------------------------------
% 0.21/0.57  % (8803)------------------------------
% 0.21/0.57  % (8781)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.59  % (8789)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.59  % (8778)Success in time 0.227 s
%------------------------------------------------------------------------------
