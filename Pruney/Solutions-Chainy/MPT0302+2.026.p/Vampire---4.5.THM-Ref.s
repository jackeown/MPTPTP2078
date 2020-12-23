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
% DateTime   : Thu Dec  3 12:42:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 200 expanded)
%              Number of leaves         :   17 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  287 ( 728 expanded)
%              Number of equality atoms :   49 ( 182 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (2729)Termination reason: Refutation not found, incomplete strategy

% (2729)Memory used [KB]: 10746
% (2729)Time elapsed: 0.143 s
% (2729)------------------------------
% (2729)------------------------------
fof(f280,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f137,f188,f246,f279])).

fof(f279,plain,
    ( ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f277,f268])).

fof(f268,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f267,f39])).

fof(f39,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK2 != sK3
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK2 != sK3
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f267,plain,
    ( sK2 = sK3
    | ~ r1_tarski(sK2,sK3)
    | ~ spl7_2 ),
    inference(resolution,[],[f266,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f266,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f263])).

fof(f263,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ r2_xboole_0(sK2,sK3)
    | ~ spl7_2 ),
    inference(resolution,[],[f198,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f198,plain,
    ( ! [X16] :
        ( ~ r2_hidden(sK5(sK2,X16),sK3)
        | ~ r2_xboole_0(sK2,X16) )
    | ~ spl7_2 ),
    inference(resolution,[],[f129,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f129,plain,
    ( ! [X8] :
        ( r2_hidden(X8,sK2)
        | ~ r2_hidden(X8,sK3) )
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl7_2
  <=> ! [X8] :
        ( ~ r2_hidden(X8,sK3)
        | r2_hidden(X8,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f277,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f274])).

fof(f274,plain,
    ( r1_tarski(sK2,sK3)
    | r1_tarski(sK2,sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f250,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f250,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(X1,sK3),sK2)
        | r1_tarski(X1,sK3) )
    | ~ spl7_3 ),
    inference(resolution,[],[f133,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f133,plain,
    ( ! [X11] :
        ( r2_hidden(X11,sK3)
        | ~ r2_hidden(X11,sK2) )
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl7_3
  <=> ! [X11] :
        ( ~ r2_hidden(X11,sK2)
        | r2_hidden(X11,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f246,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f244,f38])).

fof(f38,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f17])).

fof(f244,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_4 ),
    inference(resolution,[],[f242,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f98,f46])).

fof(f98,plain,(
    ! [X1] : ~ r2_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f96,f47])).

fof(f96,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f90,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f90,plain,(
    ! [X4,X3] :
      ( sP0(k1_xboole_0,X3,X4)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f49,f63])).

fof(f63,plain,(
    ! [X0] : sP1(X0,k1_xboole_0,X0) ),
    inference(superposition,[],[f62,f40])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f62,plain,(
    ! [X0,X1] : sP1(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f14,f13])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sP0(X1,sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sP0(X1,sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f242,plain,
    ( ! [X2] : r1_tarski(sK3,X2)
    | ~ spl7_4 ),
    inference(resolution,[],[f136,f42])).

fof(f136,plain,
    ( ! [X10] : ~ r2_hidden(X10,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl7_4
  <=> ! [X10] : ~ r2_hidden(X10,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f188,plain,(
    ~ spl7_1 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f186,f37])).

fof(f37,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f186,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_1 ),
    inference(resolution,[],[f184,f102])).

fof(f184,plain,
    ( ! [X2] : r1_tarski(sK2,X2)
    | ~ spl7_1 ),
    inference(resolution,[],[f126,f42])).

fof(f126,plain,
    ( ! [X9] : ~ r2_hidden(X9,sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl7_1
  <=> ! [X9] : ~ r2_hidden(X9,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f137,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f114,f135,f132])).

fof(f114,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,sK3)
      | ~ r2_hidden(X11,sK2)
      | r2_hidden(X11,sK3) ) ),
    inference(resolution,[],[f60,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3))
      | r2_hidden(X0,sK3) ) ),
    inference(superposition,[],[f58,f36])).

fof(f36,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f130,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f113,f128,f125])).

fof(f113,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,sK3)
      | ~ r2_hidden(X9,sK2)
      | r2_hidden(X8,sK2) ) ),
    inference(resolution,[],[f60,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3))
      | r2_hidden(X1,sK2) ) ),
    inference(superposition,[],[f59,f36])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:47:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (2708)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (2708)Refutation not found, incomplete strategy% (2708)------------------------------
% 0.22/0.51  % (2708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (2708)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (2708)Memory used [KB]: 1663
% 0.22/0.51  % (2708)Time elapsed: 0.095 s
% 0.22/0.51  % (2708)------------------------------
% 0.22/0.51  % (2708)------------------------------
% 0.22/0.51  % (2717)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (2711)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (2712)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (2714)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (2713)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (2709)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (2715)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (2717)Refutation not found, incomplete strategy% (2717)------------------------------
% 0.22/0.52  % (2717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (2717)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (2717)Memory used [KB]: 10618
% 0.22/0.52  % (2717)Time elapsed: 0.108 s
% 0.22/0.52  % (2717)------------------------------
% 0.22/0.52  % (2717)------------------------------
% 0.22/0.53  % (2733)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (2710)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (2716)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (2724)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (2725)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (2721)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (2731)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (2722)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (2710)Refutation not found, incomplete strategy% (2710)------------------------------
% 0.22/0.53  % (2710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2710)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (2710)Memory used [KB]: 10746
% 0.22/0.53  % (2710)Time elapsed: 0.117 s
% 0.22/0.53  % (2710)------------------------------
% 0.22/0.53  % (2710)------------------------------
% 0.22/0.53  % (2737)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (2723)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (2726)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (2734)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (2730)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (2719)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (2727)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (2737)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (2720)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (2720)Refutation not found, incomplete strategy% (2720)------------------------------
% 0.22/0.54  % (2720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2720)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (2720)Memory used [KB]: 10618
% 0.22/0.54  % (2720)Time elapsed: 0.132 s
% 0.22/0.54  % (2720)------------------------------
% 0.22/0.54  % (2720)------------------------------
% 0.22/0.54  % (2732)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (2729)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (2739)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (2738)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (2736)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (2719)Refutation not found, incomplete strategy% (2719)------------------------------
% 0.22/0.54  % (2719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (2726)Refutation not found, incomplete strategy% (2726)------------------------------
% 1.43/0.55  % (2726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (2730)Refutation not found, incomplete strategy% (2730)------------------------------
% 1.43/0.55  % (2730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (2730)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (2730)Memory used [KB]: 1663
% 1.43/0.55  % (2730)Time elapsed: 0.142 s
% 1.43/0.55  % (2730)------------------------------
% 1.43/0.55  % (2730)------------------------------
% 1.43/0.55  % (2726)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (2726)Memory used [KB]: 10618
% 1.43/0.55  % (2726)Time elapsed: 0.141 s
% 1.43/0.55  % (2726)------------------------------
% 1.43/0.55  % (2726)------------------------------
% 1.43/0.55  % (2736)Refutation not found, incomplete strategy% (2736)------------------------------
% 1.43/0.55  % (2736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (2729)Refutation not found, incomplete strategy% (2729)------------------------------
% 1.43/0.55  % (2729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (2719)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (2719)Memory used [KB]: 10618
% 1.43/0.55  % (2719)Time elapsed: 0.133 s
% 1.43/0.55  % (2719)------------------------------
% 1.43/0.55  % (2719)------------------------------
% 1.43/0.55  % SZS output start Proof for theBenchmark
% 1.43/0.55  % (2729)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (2729)Memory used [KB]: 10746
% 1.43/0.55  % (2729)Time elapsed: 0.143 s
% 1.43/0.55  % (2729)------------------------------
% 1.43/0.55  % (2729)------------------------------
% 1.43/0.55  fof(f280,plain,(
% 1.43/0.55    $false),
% 1.43/0.55    inference(avatar_sat_refutation,[],[f130,f137,f188,f246,f279])).
% 1.43/0.55  fof(f279,plain,(
% 1.43/0.55    ~spl7_2 | ~spl7_3),
% 1.43/0.55    inference(avatar_contradiction_clause,[],[f278])).
% 1.43/0.55  fof(f278,plain,(
% 1.43/0.55    $false | (~spl7_2 | ~spl7_3)),
% 1.43/0.55    inference(subsumption_resolution,[],[f277,f268])).
% 1.43/0.55  fof(f268,plain,(
% 1.43/0.55    ~r1_tarski(sK2,sK3) | ~spl7_2),
% 1.43/0.55    inference(subsumption_resolution,[],[f267,f39])).
% 1.43/0.55  fof(f39,plain,(
% 1.43/0.55    sK2 != sK3),
% 1.43/0.55    inference(cnf_transformation,[],[f17])).
% 1.43/0.55  fof(f17,plain,(
% 1.43/0.55    sK2 != sK3 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2)),
% 1.43/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f10,f16])).
% 1.43/0.55  fof(f16,plain,(
% 1.43/0.55    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK2 != sK3 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2))),
% 1.43/0.55    introduced(choice_axiom,[])).
% 1.43/0.55  fof(f10,plain,(
% 1.43/0.55    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 1.43/0.55    inference(flattening,[],[f9])).
% 1.43/0.55  fof(f9,plain,(
% 1.43/0.55    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 1.43/0.55    inference(ennf_transformation,[],[f8])).
% 1.43/0.55  fof(f8,negated_conjecture,(
% 1.43/0.55    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.43/0.55    inference(negated_conjecture,[],[f7])).
% 1.43/0.55  fof(f7,conjecture,(
% 1.43/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 1.43/0.55  fof(f267,plain,(
% 1.43/0.55    sK2 = sK3 | ~r1_tarski(sK2,sK3) | ~spl7_2),
% 1.43/0.55    inference(resolution,[],[f266,f46])).
% 1.43/0.55  fof(f46,plain,(
% 1.43/0.55    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f23])).
% 1.43/0.55  fof(f23,plain,(
% 1.43/0.55    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.43/0.55    inference(flattening,[],[f22])).
% 1.43/0.55  fof(f22,plain,(
% 1.43/0.55    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.43/0.55    inference(nnf_transformation,[],[f3])).
% 1.43/0.55  fof(f3,axiom,(
% 1.43/0.55    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.43/0.55  fof(f266,plain,(
% 1.43/0.55    ~r2_xboole_0(sK2,sK3) | ~spl7_2),
% 1.43/0.55    inference(duplicate_literal_removal,[],[f263])).
% 1.43/0.55  fof(f263,plain,(
% 1.43/0.55    ~r2_xboole_0(sK2,sK3) | ~r2_xboole_0(sK2,sK3) | ~spl7_2),
% 1.43/0.55    inference(resolution,[],[f198,f47])).
% 1.43/0.55  fof(f47,plain,(
% 1.43/0.55    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f25])).
% 1.43/0.55  fof(f25,plain,(
% 1.43/0.55    ! [X0,X1] : ((~r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK5(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 1.43/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f24])).
% 1.43/0.55  fof(f24,plain,(
% 1.43/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK5(X0,X1),X1)))),
% 1.43/0.55    introduced(choice_axiom,[])).
% 1.43/0.55  fof(f12,plain,(
% 1.43/0.55    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 1.43/0.55    inference(ennf_transformation,[],[f4])).
% 1.43/0.55  fof(f4,axiom,(
% 1.43/0.55    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 1.43/0.55  fof(f198,plain,(
% 1.43/0.55    ( ! [X16] : (~r2_hidden(sK5(sK2,X16),sK3) | ~r2_xboole_0(sK2,X16)) ) | ~spl7_2),
% 1.43/0.55    inference(resolution,[],[f129,f48])).
% 1.43/0.55  fof(f48,plain,(
% 1.43/0.55    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f25])).
% 1.43/0.55  fof(f129,plain,(
% 1.43/0.55    ( ! [X8] : (r2_hidden(X8,sK2) | ~r2_hidden(X8,sK3)) ) | ~spl7_2),
% 1.43/0.55    inference(avatar_component_clause,[],[f128])).
% 1.43/0.55  fof(f128,plain,(
% 1.43/0.55    spl7_2 <=> ! [X8] : (~r2_hidden(X8,sK3) | r2_hidden(X8,sK2))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.43/0.55  fof(f277,plain,(
% 1.43/0.55    r1_tarski(sK2,sK3) | ~spl7_3),
% 1.43/0.55    inference(duplicate_literal_removal,[],[f274])).
% 1.43/0.55  fof(f274,plain,(
% 1.43/0.55    r1_tarski(sK2,sK3) | r1_tarski(sK2,sK3) | ~spl7_3),
% 1.43/0.55    inference(resolution,[],[f250,f42])).
% 1.43/0.55  fof(f42,plain,(
% 1.43/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f21])).
% 1.43/0.55  fof(f21,plain,(
% 1.43/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.43/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 1.43/0.55  fof(f20,plain,(
% 1.43/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.43/0.55    introduced(choice_axiom,[])).
% 1.43/0.55  fof(f19,plain,(
% 1.43/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.43/0.55    inference(rectify,[],[f18])).
% 1.43/0.55  fof(f18,plain,(
% 1.43/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.43/0.55    inference(nnf_transformation,[],[f11])).
% 1.43/0.55  fof(f11,plain,(
% 1.43/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.43/0.55    inference(ennf_transformation,[],[f1])).
% 1.43/0.55  fof(f1,axiom,(
% 1.43/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.43/0.55  fof(f250,plain,(
% 1.43/0.55    ( ! [X1] : (~r2_hidden(sK4(X1,sK3),sK2) | r1_tarski(X1,sK3)) ) | ~spl7_3),
% 1.43/0.55    inference(resolution,[],[f133,f43])).
% 1.43/0.55  fof(f43,plain,(
% 1.43/0.55    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f21])).
% 1.43/0.55  fof(f133,plain,(
% 1.43/0.55    ( ! [X11] : (r2_hidden(X11,sK3) | ~r2_hidden(X11,sK2)) ) | ~spl7_3),
% 1.43/0.55    inference(avatar_component_clause,[],[f132])).
% 1.43/0.55  fof(f132,plain,(
% 1.43/0.55    spl7_3 <=> ! [X11] : (~r2_hidden(X11,sK2) | r2_hidden(X11,sK3))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.43/0.55  fof(f246,plain,(
% 1.43/0.55    ~spl7_4),
% 1.43/0.55    inference(avatar_contradiction_clause,[],[f245])).
% 1.43/0.55  fof(f245,plain,(
% 1.43/0.55    $false | ~spl7_4),
% 1.43/0.55    inference(subsumption_resolution,[],[f244,f38])).
% 1.43/0.55  fof(f38,plain,(
% 1.43/0.55    k1_xboole_0 != sK3),
% 1.43/0.55    inference(cnf_transformation,[],[f17])).
% 1.43/0.55  fof(f244,plain,(
% 1.43/0.55    k1_xboole_0 = sK3 | ~spl7_4),
% 1.43/0.55    inference(resolution,[],[f242,f102])).
% 1.43/0.55  fof(f102,plain,(
% 1.43/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.43/0.55    inference(resolution,[],[f98,f46])).
% 1.43/0.55  fof(f98,plain,(
% 1.43/0.55    ( ! [X1] : (~r2_xboole_0(X1,k1_xboole_0)) )),
% 1.43/0.55    inference(resolution,[],[f96,f47])).
% 1.43/0.55  fof(f96,plain,(
% 1.43/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.43/0.55    inference(condensation,[],[f94])).
% 1.43/0.55  fof(f94,plain,(
% 1.43/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.43/0.55    inference(resolution,[],[f90,f54])).
% 1.43/0.55  fof(f54,plain,(
% 1.43/0.55    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f32])).
% 1.43/0.55  fof(f32,plain,(
% 1.43/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 1.43/0.55    inference(rectify,[],[f31])).
% 1.43/0.55  fof(f31,plain,(
% 1.43/0.55    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.43/0.55    inference(flattening,[],[f30])).
% 1.43/0.55  fof(f30,plain,(
% 1.43/0.55    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.43/0.55    inference(nnf_transformation,[],[f13])).
% 1.43/0.55  fof(f13,plain,(
% 1.43/0.55    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 1.43/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.43/0.55  fof(f90,plain,(
% 1.43/0.55    ( ! [X4,X3] : (sP0(k1_xboole_0,X3,X4) | ~r2_hidden(X3,X4)) )),
% 1.43/0.55    inference(resolution,[],[f49,f63])).
% 1.43/0.55  fof(f63,plain,(
% 1.43/0.55    ( ! [X0] : (sP1(X0,k1_xboole_0,X0)) )),
% 1.43/0.55    inference(superposition,[],[f62,f40])).
% 1.43/0.55  fof(f40,plain,(
% 1.43/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.43/0.55    inference(cnf_transformation,[],[f5])).
% 1.43/0.55  fof(f5,axiom,(
% 1.43/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.43/0.55  fof(f62,plain,(
% 1.43/0.55    ( ! [X0,X1] : (sP1(X0,X1,k4_xboole_0(X0,X1))) )),
% 1.43/0.55    inference(equality_resolution,[],[f56])).
% 1.43/0.55  fof(f56,plain,(
% 1.43/0.55    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.43/0.55    inference(cnf_transformation,[],[f33])).
% 1.43/0.55  fof(f33,plain,(
% 1.43/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.43/0.55    inference(nnf_transformation,[],[f15])).
% 1.43/0.55  fof(f15,plain,(
% 1.43/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 1.43/0.55    inference(definition_folding,[],[f2,f14,f13])).
% 1.43/0.55  fof(f14,plain,(
% 1.43/0.55    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 1.43/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.43/0.55  fof(f2,axiom,(
% 1.43/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.43/0.55  fof(f49,plain,(
% 1.43/0.55    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f29])).
% 1.43/0.55  fof(f29,plain,(
% 1.43/0.55    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(X1,sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.43/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).
% 1.43/0.55  fof(f28,plain,(
% 1.43/0.55    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(X1,sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.43/0.55    introduced(choice_axiom,[])).
% 1.43/0.55  fof(f27,plain,(
% 1.43/0.55    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.43/0.55    inference(rectify,[],[f26])).
% 1.43/0.55  fof(f26,plain,(
% 1.43/0.55    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 1.43/0.55    inference(nnf_transformation,[],[f14])).
% 1.43/0.55  fof(f242,plain,(
% 1.43/0.55    ( ! [X2] : (r1_tarski(sK3,X2)) ) | ~spl7_4),
% 1.43/0.55    inference(resolution,[],[f136,f42])).
% 1.43/0.55  fof(f136,plain,(
% 1.43/0.55    ( ! [X10] : (~r2_hidden(X10,sK3)) ) | ~spl7_4),
% 1.43/0.55    inference(avatar_component_clause,[],[f135])).
% 1.43/0.55  fof(f135,plain,(
% 1.43/0.55    spl7_4 <=> ! [X10] : ~r2_hidden(X10,sK3)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.43/0.55  fof(f188,plain,(
% 1.43/0.55    ~spl7_1),
% 1.43/0.55    inference(avatar_contradiction_clause,[],[f187])).
% 1.43/0.55  fof(f187,plain,(
% 1.43/0.55    $false | ~spl7_1),
% 1.43/0.55    inference(subsumption_resolution,[],[f186,f37])).
% 1.43/0.55  fof(f37,plain,(
% 1.43/0.55    k1_xboole_0 != sK2),
% 1.43/0.55    inference(cnf_transformation,[],[f17])).
% 1.43/0.55  fof(f186,plain,(
% 1.43/0.55    k1_xboole_0 = sK2 | ~spl7_1),
% 1.43/0.55    inference(resolution,[],[f184,f102])).
% 1.43/0.55  fof(f184,plain,(
% 1.43/0.55    ( ! [X2] : (r1_tarski(sK2,X2)) ) | ~spl7_1),
% 1.43/0.55    inference(resolution,[],[f126,f42])).
% 1.43/0.55  fof(f126,plain,(
% 1.43/0.55    ( ! [X9] : (~r2_hidden(X9,sK2)) ) | ~spl7_1),
% 1.43/0.55    inference(avatar_component_clause,[],[f125])).
% 1.43/0.55  fof(f125,plain,(
% 1.43/0.55    spl7_1 <=> ! [X9] : ~r2_hidden(X9,sK2)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.43/0.55  fof(f137,plain,(
% 1.43/0.55    spl7_3 | spl7_4),
% 1.43/0.55    inference(avatar_split_clause,[],[f114,f135,f132])).
% 1.43/0.55  fof(f114,plain,(
% 1.43/0.55    ( ! [X10,X11] : (~r2_hidden(X10,sK3) | ~r2_hidden(X11,sK2) | r2_hidden(X11,sK3)) )),
% 1.43/0.55    inference(resolution,[],[f60,f81])).
% 1.43/0.55  fof(f81,plain,(
% 1.43/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) | r2_hidden(X0,sK3)) )),
% 1.43/0.55    inference(superposition,[],[f58,f36])).
% 1.43/0.55  fof(f36,plain,(
% 1.43/0.55    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2)),
% 1.43/0.55    inference(cnf_transformation,[],[f17])).
% 1.43/0.55  fof(f58,plain,(
% 1.43/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f35])).
% 1.43/0.55  fof(f35,plain,(
% 1.43/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.43/0.55    inference(flattening,[],[f34])).
% 1.43/0.55  fof(f34,plain,(
% 1.43/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.43/0.55    inference(nnf_transformation,[],[f6])).
% 1.43/0.55  fof(f6,axiom,(
% 1.43/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.43/0.55  fof(f60,plain,(
% 1.43/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f35])).
% 1.43/0.55  fof(f130,plain,(
% 1.43/0.55    spl7_1 | spl7_2),
% 1.43/0.55    inference(avatar_split_clause,[],[f113,f128,f125])).
% 1.43/0.55  fof(f113,plain,(
% 1.43/0.55    ( ! [X8,X9] : (~r2_hidden(X8,sK3) | ~r2_hidden(X9,sK2) | r2_hidden(X8,sK2)) )),
% 1.43/0.55    inference(resolution,[],[f60,f88])).
% 1.43/0.55  fof(f88,plain,(
% 1.43/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) | r2_hidden(X1,sK2)) )),
% 1.43/0.55    inference(superposition,[],[f59,f36])).
% 1.43/0.55  fof(f59,plain,(
% 1.43/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f35])).
% 1.43/0.55  % SZS output end Proof for theBenchmark
% 1.43/0.55  % (2737)------------------------------
% 1.43/0.55  % (2737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (2737)Termination reason: Refutation
% 1.43/0.55  
% 1.43/0.55  % (2737)Memory used [KB]: 6396
% 1.43/0.55  % (2737)Time elapsed: 0.125 s
% 1.43/0.55  % (2737)------------------------------
% 1.43/0.55  % (2737)------------------------------
% 1.43/0.55  % (2728)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.55  % (2705)Success in time 0.185 s
%------------------------------------------------------------------------------
