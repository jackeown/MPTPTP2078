%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:30 EST 2020

% Result     : Theorem 2.77s
% Output     : Refutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 490 expanded)
%              Number of leaves         :   42 ( 179 expanded)
%              Depth                    :   12
%              Number of atoms          :  529 (2239 expanded)
%              Number of equality atoms :  187 ( 916 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f889,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f128,f171,f186,f208,f219,f276,f287,f301,f320,f329,f330,f413,f526,f595,f596,f597,f605,f606,f607,f767,f768,f792,f793,f875,f886,f887,f888])).

fof(f888,plain,
    ( sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f887,plain,
    ( sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f886,plain,
    ( spl5_37
    | ~ spl5_20
    | spl5_21 ),
    inference(avatar_split_clause,[],[f881,f294,f284,f883])).

fof(f883,plain,
    ( spl5_37
  <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f284,plain,
    ( spl5_20
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f294,plain,
    ( spl5_21
  <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f881,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_20
    | spl5_21 ),
    inference(subsumption_resolution,[],[f877,f295])).

fof(f295,plain,
    ( sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f294])).

fof(f877,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_20 ),
    inference(resolution,[],[f286,f70])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f38,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

% (20128)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f286,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f284])).

fof(f875,plain,
    ( spl5_33
    | spl5_34
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f871,f273,f521,f517])).

fof(f517,plain,
    ( spl5_33
  <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f521,plain,
    ( spl5_34
  <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f273,plain,
    ( spl5_19
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f871,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_19 ),
    inference(resolution,[],[f275,f70])).

fof(f275,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f273])).

fof(f793,plain,
    ( sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f792,plain,
    ( spl5_8
    | ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f791])).

fof(f791,plain,
    ( $false
    | spl5_8
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f790,f67])).

fof(f67,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f790,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_8
    | ~ spl5_21 ),
    inference(forward_demodulation,[],[f180,f296])).

fof(f296,plain,
    ( sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f294])).

fof(f180,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl5_8
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f768,plain,
    ( sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f767,plain,
    ( spl5_6
    | ~ spl5_34 ),
    inference(avatar_contradiction_clause,[],[f766])).

fof(f766,plain,
    ( $false
    | spl5_6
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f765,f67])).

fof(f765,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_6
    | ~ spl5_34 ),
    inference(forward_demodulation,[],[f165,f523])).

fof(f523,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f521])).

fof(f165,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl5_6
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f607,plain,
    ( spl5_21
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f292,f179,f294])).

fof(f292,plain,
    ( sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_8 ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,
    ( sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_8 ),
    inference(resolution,[],[f181,f70])).

fof(f181,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f179])).

fof(f606,plain,
    ( ~ spl5_8
    | ~ spl5_20
    | spl5_9
    | spl5_2 ),
    inference(avatar_split_clause,[],[f415,f77,f183,f284,f179])).

fof(f183,plain,
    ( spl5_9
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f77,plain,
    ( spl5_2
  <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f415,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_2 ),
    inference(equality_resolution,[],[f140])).

fof(f140,plain,
    ( ! [X23] :
        ( k2_enumset1(sK1,sK1,sK1,sK1) != X23
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X23),sK2)
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X23),k2_enumset1(sK0,sK0,sK0,sK1))
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X23),X23) )
    | spl5_2 ),
    inference(superposition,[],[f79,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f37,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f79,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f605,plain,
    ( sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f597,plain,
    ( sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f596,plain,
    ( sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f595,plain,
    ( ~ spl5_6
    | spl5_34 ),
    inference(avatar_contradiction_clause,[],[f594])).

fof(f594,plain,
    ( $false
    | ~ spl5_6
    | spl5_34 ),
    inference(subsumption_resolution,[],[f590,f522])).

fof(f522,plain,
    ( sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_34 ),
    inference(avatar_component_clause,[],[f521])).

fof(f590,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f586])).

fof(f586,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_6 ),
    inference(resolution,[],[f166,f70])).

fof(f166,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f164])).

fof(f526,plain,
    ( ~ spl5_6
    | ~ spl5_19
    | spl5_3
    | spl5_7 ),
    inference(avatar_split_clause,[],[f525,f168,f82,f273,f164])).

fof(f82,plain,
    ( spl5_3
  <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f168,plain,
    ( spl5_7
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f525,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_3
    | spl5_7 ),
    inference(subsumption_resolution,[],[f396,f170])).

fof(f170,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f168])).

fof(f396,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_3 ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,
    ( ! [X22] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != X22
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X22),sK2)
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X22),k2_enumset1(sK0,sK0,sK0,sK1))
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X22),X22) )
    | spl5_3 ),
    inference(superposition,[],[f84,f51])).

fof(f84,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f413,plain,
    ( sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | r2_hidden(sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f330,plain,
    ( sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f329,plain,
    ( spl5_22
    | spl5_23
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f317,f193,f326,f322])).

fof(f322,plain,
    ( spl5_22
  <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f326,plain,
    ( spl5_23
  <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f193,plain,
    ( spl5_10
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f317,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl5_10 ),
    inference(resolution,[],[f195,f70])).

fof(f195,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f193])).

fof(f320,plain,
    ( spl5_1
    | ~ spl5_10
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | spl5_1
    | ~ spl5_10
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f199,f195,f74,f195,f51])).

fof(f74,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_1
  <=> k2_enumset1(sK0,sK0,sK0,sK1) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f199,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl5_11
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f301,plain,
    ( spl5_10
    | spl5_1 ),
    inference(avatar_split_clause,[],[f300,f72,f193])).

fof(f300,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl5_1 ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl5_1 ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,
    ( ! [X20] :
        ( k2_enumset1(sK0,sK0,sK0,sK1) != X20
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X20),k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X20),X20) )
    | spl5_1 ),
    inference(superposition,[],[f74,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f35,f30])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f287,plain,
    ( spl5_8
    | spl5_20
    | spl5_2 ),
    inference(avatar_split_clause,[],[f281,f77,f284,f179])).

fof(f281,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_2 ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,
    ( ! [X19] :
        ( k2_enumset1(sK1,sK1,sK1,sK1) != X19
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X19),k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X19),X19) )
    | spl5_2 ),
    inference(superposition,[],[f79,f53])).

fof(f276,plain,
    ( spl5_6
    | spl5_19
    | spl5_3 ),
    inference(avatar_split_clause,[],[f270,f82,f273,f164])).

fof(f270,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_3 ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,
    ( ! [X18] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != X18
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X18),k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X18),X18) )
    | spl5_3 ),
    inference(superposition,[],[f84,f53])).

fof(f219,plain,
    ( spl5_13
    | spl5_14
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f209,f205,f216,f212])).

fof(f212,plain,
    ( spl5_13
  <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f216,plain,
    ( spl5_14
  <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f205,plain,
    ( spl5_12
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f209,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_12 ),
    inference(resolution,[],[f207,f70])).

fof(f207,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f205])).

fof(f208,plain,
    ( spl5_12
    | spl5_4 ),
    inference(avatar_split_clause,[],[f203,f87,f205])).

% (20125)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
fof(f87,plain,
    ( spl5_4
  <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f203,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl5_4 ),
    inference(subsumption_resolution,[],[f202,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f64,f50])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f33,f30])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f202,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl5_4 ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,
    ( ! [X21] :
        ( k1_xboole_0 != X21
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X21),k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X21),X21) )
    | spl5_4 ),
    inference(superposition,[],[f89,f53])).

fof(f89,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f186,plain,
    ( spl5_8
    | ~ spl5_9
    | spl5_2 ),
    inference(avatar_split_clause,[],[f176,f77,f183,f179])).

fof(f176,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_2 ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,
    ( ! [X15] :
        ( k2_enumset1(sK1,sK1,sK1,sK1) != X15
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X15),sK2)
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X15),X15) )
    | spl5_2 ),
    inference(superposition,[],[f79,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f36,f30])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f171,plain,
    ( spl5_6
    | ~ spl5_7
    | spl5_3 ),
    inference(avatar_split_clause,[],[f161,f82,f168,f164])).

fof(f161,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_3 ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,
    ( ! [X14] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != X14
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X14),sK2)
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X14),X14) )
    | spl5_3 ),
    inference(superposition,[],[f84,f52])).

fof(f128,plain,
    ( ~ spl5_5
    | spl5_4 ),
    inference(avatar_split_clause,[],[f123,f87,f125])).

fof(f125,plain,
    ( spl5_5
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f123,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f122,f91])).

fof(f122,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl5_4 ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,
    ( ! [X17] :
        ( k1_xboole_0 != X17
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X17),sK2)
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X17),X17) )
    | spl5_4 ),
    inference(superposition,[],[f89,f52])).

fof(f90,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f49,f87])).

fof(f49,plain,(
    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f23,f30,f44])).

fof(f23,plain,(
    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
    & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
   => ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
      & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
          & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(f85,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f48,f82])).

fof(f48,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f24,f30,f44,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f44])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f80,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f47,f77])).

fof(f47,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f25,f30,f44,f45])).

fof(f25,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f46,f72])).

fof(f46,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f26,f44,f30,f44])).

fof(f26,plain,(
    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:07:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (20039)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (20024)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (20030)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (20028)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (20048)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.19/0.51  % (20040)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.19/0.51  % (20049)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.19/0.51  % (20036)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.19/0.51  % (20040)Refutation not found, incomplete strategy% (20040)------------------------------
% 1.19/0.51  % (20040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (20040)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.51  
% 1.19/0.51  % (20040)Memory used [KB]: 1663
% 1.19/0.51  % (20040)Time elapsed: 0.058 s
% 1.19/0.51  % (20040)------------------------------
% 1.19/0.51  % (20040)------------------------------
% 1.19/0.51  % (20047)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.19/0.51  % (20033)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.19/0.51  % (20031)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.19/0.52  % (20041)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.19/0.52  % (20045)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.30/0.53  % (20032)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.30/0.53  % (20053)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.30/0.53  % (20053)Refutation not found, incomplete strategy% (20053)------------------------------
% 1.30/0.53  % (20053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (20053)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (20053)Memory used [KB]: 6140
% 1.30/0.53  % (20053)Time elapsed: 0.121 s
% 1.30/0.53  % (20053)------------------------------
% 1.30/0.53  % (20053)------------------------------
% 1.30/0.53  % (20038)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.30/0.53  % (20038)Refutation not found, incomplete strategy% (20038)------------------------------
% 1.30/0.53  % (20038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (20038)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (20038)Memory used [KB]: 10618
% 1.30/0.53  % (20038)Time elapsed: 0.134 s
% 1.30/0.53  % (20038)------------------------------
% 1.30/0.53  % (20038)------------------------------
% 1.30/0.53  % (20027)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.30/0.53  % (20025)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.30/0.53  % (20025)Refutation not found, incomplete strategy% (20025)------------------------------
% 1.30/0.53  % (20025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (20025)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (20025)Memory used [KB]: 1663
% 1.30/0.53  % (20025)Time elapsed: 0.127 s
% 1.30/0.53  % (20025)------------------------------
% 1.30/0.53  % (20025)------------------------------
% 1.30/0.53  % (20035)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.30/0.54  % (20037)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.30/0.54  % (20054)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.30/0.54  % (20050)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.30/0.54  % (20050)Refutation not found, incomplete strategy% (20050)------------------------------
% 1.30/0.54  % (20050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (20050)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (20050)Memory used [KB]: 10618
% 1.30/0.54  % (20050)Time elapsed: 0.140 s
% 1.30/0.54  % (20050)------------------------------
% 1.30/0.54  % (20050)------------------------------
% 1.30/0.54  % (20046)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.30/0.54  % (20044)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.30/0.55  % (20044)Refutation not found, incomplete strategy% (20044)------------------------------
% 1.30/0.55  % (20044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (20044)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (20044)Memory used [KB]: 1663
% 1.30/0.55  % (20044)Time elapsed: 0.141 s
% 1.30/0.55  % (20044)------------------------------
% 1.30/0.55  % (20044)------------------------------
% 1.30/0.55  % (20052)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.30/0.55  % (20052)Refutation not found, incomplete strategy% (20052)------------------------------
% 1.30/0.55  % (20052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (20052)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (20052)Memory used [KB]: 6140
% 1.30/0.55  % (20052)Time elapsed: 0.142 s
% 1.30/0.55  % (20052)------------------------------
% 1.30/0.55  % (20052)------------------------------
% 1.30/0.55  % (20042)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.30/0.55  % (20042)Refutation not found, incomplete strategy% (20042)------------------------------
% 1.30/0.55  % (20042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (20055)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.55  % (20026)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.30/0.56  % (20042)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.56  
% 1.30/0.56  % (20042)Memory used [KB]: 10618
% 1.30/0.56  % (20042)Time elapsed: 0.153 s
% 1.30/0.56  % (20042)------------------------------
% 1.30/0.56  % (20042)------------------------------
% 1.30/0.56  % (20043)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.30/0.57  % (20051)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.30/0.57  % (20043)Refutation not found, incomplete strategy% (20043)------------------------------
% 1.30/0.57  % (20043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.57  % (20043)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.57  
% 1.30/0.57  % (20043)Memory used [KB]: 1663
% 1.30/0.57  % (20043)Time elapsed: 0.172 s
% 1.30/0.57  % (20043)------------------------------
% 1.30/0.57  % (20043)------------------------------
% 1.30/0.57  % (20055)Refutation not found, incomplete strategy% (20055)------------------------------
% 1.30/0.57  % (20055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.57  % (20055)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.57  
% 1.30/0.57  % (20055)Memory used [KB]: 1663
% 1.30/0.57  % (20055)Time elapsed: 0.003 s
% 1.30/0.57  % (20055)------------------------------
% 1.30/0.57  % (20055)------------------------------
% 1.30/0.62  % (20113)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.95/0.64  % (20114)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.95/0.64  % (20024)Refutation not found, incomplete strategy% (20024)------------------------------
% 1.95/0.64  % (20024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.64  % (20024)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.64  
% 1.95/0.64  % (20024)Memory used [KB]: 1663
% 1.95/0.64  % (20024)Time elapsed: 0.244 s
% 1.95/0.64  % (20024)------------------------------
% 1.95/0.64  % (20024)------------------------------
% 1.95/0.65  % (20115)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.95/0.65  % (20115)Refutation not found, incomplete strategy% (20115)------------------------------
% 1.95/0.65  % (20115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.65  % (20115)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.65  
% 1.95/0.65  % (20115)Memory used [KB]: 6140
% 1.95/0.65  % (20115)Time elapsed: 0.092 s
% 1.95/0.65  % (20115)------------------------------
% 1.95/0.65  % (20115)------------------------------
% 1.95/0.65  % (20041)Refutation not found, incomplete strategy% (20041)------------------------------
% 1.95/0.65  % (20041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.65  % (20041)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.65  
% 1.95/0.65  % (20041)Memory used [KB]: 6140
% 1.95/0.65  % (20041)Time elapsed: 0.259 s
% 1.95/0.65  % (20041)------------------------------
% 1.95/0.65  % (20041)------------------------------
% 1.95/0.66  % (20027)Refutation not found, incomplete strategy% (20027)------------------------------
% 1.95/0.66  % (20027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.66  % (20027)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.66  
% 1.95/0.66  % (20027)Memory used [KB]: 6140
% 1.95/0.66  % (20027)Time elapsed: 0.259 s
% 1.95/0.66  % (20027)------------------------------
% 1.95/0.66  % (20027)------------------------------
% 1.95/0.67  % (20116)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 1.95/0.67  % (20117)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 1.95/0.67  % (20119)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 1.95/0.68  % (20117)Refutation not found, incomplete strategy% (20117)------------------------------
% 1.95/0.68  % (20117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.68  % (20117)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.68  
% 1.95/0.68  % (20117)Memory used [KB]: 10618
% 1.95/0.68  % (20117)Time elapsed: 0.100 s
% 1.95/0.68  % (20117)------------------------------
% 1.95/0.68  % (20117)------------------------------
% 1.95/0.68  % (20118)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 1.95/0.69  % (20120)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.38/0.71  % (20121)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.38/0.71  % (20122)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.38/0.71  % (20122)Refutation not found, incomplete strategy% (20122)------------------------------
% 2.38/0.71  % (20122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.38/0.71  % (20122)Termination reason: Refutation not found, incomplete strategy
% 2.38/0.71  
% 2.38/0.71  % (20122)Memory used [KB]: 10746
% 2.38/0.71  % (20122)Time elapsed: 0.114 s
% 2.38/0.71  % (20122)------------------------------
% 2.38/0.71  % (20122)------------------------------
% 2.77/0.78  % (20123)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.77/0.78  % (20114)Refutation found. Thanks to Tanya!
% 2.77/0.78  % SZS status Theorem for theBenchmark
% 2.77/0.78  % SZS output start Proof for theBenchmark
% 2.77/0.78  fof(f889,plain,(
% 2.77/0.78    $false),
% 2.77/0.78    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f128,f171,f186,f208,f219,f276,f287,f301,f320,f329,f330,f413,f526,f595,f596,f597,f605,f606,f607,f767,f768,f792,f793,f875,f886,f887,f888])).
% 2.77/0.78  fof(f888,plain,(
% 2.77/0.78    sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 2.77/0.78    introduced(theory_tautology_sat_conflict,[])).
% 2.77/0.78  fof(f887,plain,(
% 2.77/0.78    sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)),
% 2.77/0.78    introduced(theory_tautology_sat_conflict,[])).
% 2.77/0.78  fof(f886,plain,(
% 2.77/0.78    spl5_37 | ~spl5_20 | spl5_21),
% 2.77/0.78    inference(avatar_split_clause,[],[f881,f294,f284,f883])).
% 2.77/0.78  fof(f883,plain,(
% 2.77/0.78    spl5_37 <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))),
% 2.77/0.78    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 2.77/0.78  fof(f284,plain,(
% 2.77/0.78    spl5_20 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 2.77/0.78    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 2.77/0.78  fof(f294,plain,(
% 2.77/0.78    spl5_21 <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))),
% 2.77/0.78    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 2.77/0.78  fof(f881,plain,(
% 2.77/0.78    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | (~spl5_20 | spl5_21)),
% 2.77/0.78    inference(subsumption_resolution,[],[f877,f295])).
% 2.77/0.78  fof(f295,plain,(
% 2.77/0.78    sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_21),
% 2.77/0.78    inference(avatar_component_clause,[],[f294])).
% 2.77/0.78  fof(f877,plain,(
% 2.77/0.78    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_20),
% 2.77/0.78    inference(resolution,[],[f286,f70])).
% 2.77/0.78  fof(f70,plain,(
% 2.77/0.78    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 2.77/0.78    inference(equality_resolution,[],[f62])).
% 2.77/0.78  fof(f62,plain,(
% 2.77/0.78    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 2.77/0.78    inference(definition_unfolding,[],[f38,f44])).
% 2.77/0.78  fof(f44,plain,(
% 2.77/0.78    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.77/0.78    inference(definition_unfolding,[],[f29,f31])).
% 2.77/0.78  fof(f31,plain,(
% 2.77/0.78    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.77/0.78    inference(cnf_transformation,[],[f7])).
% 2.77/0.78  fof(f7,axiom,(
% 2.77/0.78    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.77/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.77/0.78  fof(f29,plain,(
% 2.77/0.78    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.77/0.78    inference(cnf_transformation,[],[f6])).
% 2.77/0.78  fof(f6,axiom,(
% 2.77/0.78    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.77/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.77/0.78  fof(f38,plain,(
% 2.77/0.78    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.77/0.78    inference(cnf_transformation,[],[f22])).
% 2.77/0.78  % (20128)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.77/0.78  fof(f22,plain,(
% 2.77/0.78    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.77/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).
% 2.77/0.78  fof(f21,plain,(
% 2.77/0.78    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.77/0.78    introduced(choice_axiom,[])).
% 2.77/0.78  fof(f20,plain,(
% 2.77/0.78    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.77/0.78    inference(rectify,[],[f19])).
% 2.77/0.78  fof(f19,plain,(
% 2.77/0.78    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.77/0.78    inference(flattening,[],[f18])).
% 2.77/0.78  fof(f18,plain,(
% 2.77/0.78    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.77/0.78    inference(nnf_transformation,[],[f4])).
% 2.77/0.78  fof(f4,axiom,(
% 2.77/0.78    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.77/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.77/0.78  fof(f286,plain,(
% 2.77/0.78    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl5_20),
% 2.77/0.78    inference(avatar_component_clause,[],[f284])).
% 2.77/0.78  fof(f875,plain,(
% 2.77/0.78    spl5_33 | spl5_34 | ~spl5_19),
% 2.77/0.78    inference(avatar_split_clause,[],[f871,f273,f521,f517])).
% 2.77/0.78  fof(f517,plain,(
% 2.77/0.78    spl5_33 <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.77/0.78    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 2.77/0.78  fof(f521,plain,(
% 2.77/0.78    spl5_34 <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.77/0.78    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 2.77/0.79  fof(f273,plain,(
% 2.77/0.79    spl5_19 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 2.77/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 2.77/0.79  fof(f871,plain,(
% 2.77/0.79    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_19),
% 2.77/0.79    inference(resolution,[],[f275,f70])).
% 2.77/0.79  fof(f275,plain,(
% 2.77/0.79    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl5_19),
% 2.77/0.79    inference(avatar_component_clause,[],[f273])).
% 2.77/0.79  fof(f793,plain,(
% 2.77/0.79    sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 2.77/0.79    introduced(theory_tautology_sat_conflict,[])).
% 2.77/0.79  fof(f792,plain,(
% 2.77/0.79    spl5_8 | ~spl5_21),
% 2.77/0.79    inference(avatar_contradiction_clause,[],[f791])).
% 2.77/0.79  fof(f791,plain,(
% 2.77/0.79    $false | (spl5_8 | ~spl5_21)),
% 2.77/0.79    inference(subsumption_resolution,[],[f790,f67])).
% 2.77/0.79  fof(f67,plain,(
% 2.77/0.79    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 2.77/0.79    inference(equality_resolution,[],[f66])).
% 2.77/0.79  fof(f66,plain,(
% 2.77/0.79    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 2.77/0.79    inference(equality_resolution,[],[f60])).
% 2.77/0.79  fof(f60,plain,(
% 2.77/0.79    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 2.77/0.79    inference(definition_unfolding,[],[f40,f44])).
% 2.77/0.79  fof(f40,plain,(
% 2.77/0.79    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.77/0.79    inference(cnf_transformation,[],[f22])).
% 2.77/0.79  fof(f790,plain,(
% 2.77/0.79    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | (spl5_8 | ~spl5_21)),
% 2.77/0.79    inference(forward_demodulation,[],[f180,f296])).
% 2.77/0.79  fof(f296,plain,(
% 2.77/0.79    sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_21),
% 2.77/0.79    inference(avatar_component_clause,[],[f294])).
% 2.77/0.79  fof(f180,plain,(
% 2.77/0.79    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_8),
% 2.77/0.79    inference(avatar_component_clause,[],[f179])).
% 2.77/0.79  fof(f179,plain,(
% 2.77/0.79    spl5_8 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))),
% 2.77/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.77/0.79  fof(f768,plain,(
% 2.77/0.79    sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)),
% 2.77/0.79    introduced(theory_tautology_sat_conflict,[])).
% 2.77/0.79  fof(f767,plain,(
% 2.77/0.79    spl5_6 | ~spl5_34),
% 2.77/0.79    inference(avatar_contradiction_clause,[],[f766])).
% 2.77/0.79  fof(f766,plain,(
% 2.77/0.79    $false | (spl5_6 | ~spl5_34)),
% 2.77/0.79    inference(subsumption_resolution,[],[f765,f67])).
% 2.77/0.79  fof(f765,plain,(
% 2.77/0.79    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | (spl5_6 | ~spl5_34)),
% 2.77/0.79    inference(forward_demodulation,[],[f165,f523])).
% 2.77/0.79  fof(f523,plain,(
% 2.77/0.79    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_34),
% 2.77/0.79    inference(avatar_component_clause,[],[f521])).
% 2.77/0.79  fof(f165,plain,(
% 2.77/0.79    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_6),
% 2.77/0.79    inference(avatar_component_clause,[],[f164])).
% 2.77/0.79  fof(f164,plain,(
% 2.77/0.79    spl5_6 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.77/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.77/0.79  fof(f607,plain,(
% 2.77/0.79    spl5_21 | ~spl5_8),
% 2.77/0.79    inference(avatar_split_clause,[],[f292,f179,f294])).
% 2.77/0.79  fof(f292,plain,(
% 2.77/0.79    sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_8),
% 2.77/0.79    inference(duplicate_literal_removal,[],[f288])).
% 2.77/0.79  fof(f288,plain,(
% 2.77/0.79    sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_8),
% 2.77/0.79    inference(resolution,[],[f181,f70])).
% 2.77/0.79  fof(f181,plain,(
% 2.77/0.79    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_8),
% 2.77/0.79    inference(avatar_component_clause,[],[f179])).
% 2.77/0.79  fof(f606,plain,(
% 2.77/0.79    ~spl5_8 | ~spl5_20 | spl5_9 | spl5_2),
% 2.77/0.79    inference(avatar_split_clause,[],[f415,f77,f183,f284,f179])).
% 2.77/0.79  fof(f183,plain,(
% 2.77/0.79    spl5_9 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)),
% 2.77/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.77/0.79  fof(f77,plain,(
% 2.77/0.79    spl5_2 <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 2.77/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.77/0.79  fof(f415,plain,(
% 2.77/0.79    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_2),
% 2.77/0.79    inference(equality_resolution,[],[f140])).
% 2.77/0.79  fof(f140,plain,(
% 2.77/0.79    ( ! [X23] : (k2_enumset1(sK1,sK1,sK1,sK1) != X23 | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X23),sK2) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X23),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X23),X23)) ) | spl5_2),
% 2.77/0.79    inference(superposition,[],[f79,f51])).
% 2.77/0.79  fof(f51,plain,(
% 2.77/0.79    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.77/0.79    inference(definition_unfolding,[],[f37,f30])).
% 2.77/0.79  fof(f30,plain,(
% 2.77/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.77/0.79    inference(cnf_transformation,[],[f2])).
% 2.77/0.79  fof(f2,axiom,(
% 2.77/0.79    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.77/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.77/0.79  fof(f37,plain,(
% 2.77/0.79    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.77/0.79    inference(cnf_transformation,[],[f17])).
% 2.77/0.79  fof(f17,plain,(
% 2.77/0.79    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.77/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 2.77/0.79  fof(f16,plain,(
% 2.77/0.79    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.77/0.79    introduced(choice_axiom,[])).
% 2.77/0.79  fof(f15,plain,(
% 2.77/0.79    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.77/0.79    inference(rectify,[],[f14])).
% 2.77/0.79  fof(f14,plain,(
% 2.77/0.79    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.77/0.79    inference(flattening,[],[f13])).
% 2.77/0.79  fof(f13,plain,(
% 2.77/0.79    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.77/0.79    inference(nnf_transformation,[],[f1])).
% 2.77/0.79  fof(f1,axiom,(
% 2.77/0.79    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.77/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.77/0.79  fof(f79,plain,(
% 2.77/0.79    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK1,sK1,sK1,sK1) | spl5_2),
% 2.77/0.79    inference(avatar_component_clause,[],[f77])).
% 2.77/0.79  fof(f605,plain,(
% 2.77/0.79    sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)),
% 2.77/0.79    introduced(theory_tautology_sat_conflict,[])).
% 2.77/0.79  fof(f597,plain,(
% 2.77/0.79    sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)),
% 2.77/0.79    introduced(theory_tautology_sat_conflict,[])).
% 2.77/0.79  fof(f596,plain,(
% 2.77/0.79    sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK1,sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)),
% 2.77/0.79    introduced(theory_tautology_sat_conflict,[])).
% 2.77/0.79  fof(f595,plain,(
% 2.77/0.79    ~spl5_6 | spl5_34),
% 2.77/0.79    inference(avatar_contradiction_clause,[],[f594])).
% 2.77/0.79  fof(f594,plain,(
% 2.77/0.79    $false | (~spl5_6 | spl5_34)),
% 2.77/0.79    inference(subsumption_resolution,[],[f590,f522])).
% 2.77/0.79  fof(f522,plain,(
% 2.77/0.79    sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_34),
% 2.77/0.79    inference(avatar_component_clause,[],[f521])).
% 2.77/0.79  fof(f590,plain,(
% 2.77/0.79    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_6),
% 2.77/0.79    inference(duplicate_literal_removal,[],[f586])).
% 2.77/0.79  fof(f586,plain,(
% 2.77/0.79    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_6),
% 2.77/0.79    inference(resolution,[],[f166,f70])).
% 2.77/0.79  fof(f166,plain,(
% 2.77/0.79    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_6),
% 2.77/0.79    inference(avatar_component_clause,[],[f164])).
% 2.77/0.79  fof(f526,plain,(
% 2.77/0.79    ~spl5_6 | ~spl5_19 | spl5_3 | spl5_7),
% 2.77/0.79    inference(avatar_split_clause,[],[f525,f168,f82,f273,f164])).
% 2.77/0.79  fof(f82,plain,(
% 2.77/0.79    spl5_3 <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 2.77/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.77/0.79  fof(f168,plain,(
% 2.77/0.79    spl5_7 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)),
% 2.77/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.77/0.79  fof(f525,plain,(
% 2.77/0.79    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | (spl5_3 | spl5_7)),
% 2.77/0.79    inference(subsumption_resolution,[],[f396,f170])).
% 2.77/0.79  fof(f170,plain,(
% 2.77/0.79    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) | spl5_7),
% 2.77/0.79    inference(avatar_component_clause,[],[f168])).
% 2.77/0.79  fof(f396,plain,(
% 2.77/0.79    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_3),
% 2.77/0.79    inference(equality_resolution,[],[f139])).
% 2.77/0.79  fof(f139,plain,(
% 2.77/0.79    ( ! [X22] : (k2_enumset1(sK0,sK0,sK0,sK0) != X22 | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X22),sK2) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X22),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X22),X22)) ) | spl5_3),
% 2.77/0.79    inference(superposition,[],[f84,f51])).
% 2.77/0.79  fof(f84,plain,(
% 2.77/0.79    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK0,sK0,sK0,sK0) | spl5_3),
% 2.77/0.79    inference(avatar_component_clause,[],[f82])).
% 2.77/0.79  fof(f413,plain,(
% 2.77/0.79    sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | r2_hidden(sK1,sK2)),
% 2.77/0.79    introduced(theory_tautology_sat_conflict,[])).
% 2.77/0.79  fof(f330,plain,(
% 2.77/0.79    sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)),
% 2.77/0.79    introduced(theory_tautology_sat_conflict,[])).
% 2.77/0.79  fof(f329,plain,(
% 2.77/0.79    spl5_22 | spl5_23 | ~spl5_10),
% 2.77/0.79    inference(avatar_split_clause,[],[f317,f193,f326,f322])).
% 2.77/0.79  fof(f322,plain,(
% 2.77/0.79    spl5_22 <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 2.77/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 2.77/0.79  fof(f326,plain,(
% 2.77/0.79    spl5_23 <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 2.77/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 2.77/0.79  fof(f193,plain,(
% 2.77/0.79    spl5_10 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 2.77/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.77/0.79  fof(f317,plain,(
% 2.77/0.79    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl5_10),
% 2.77/0.79    inference(resolution,[],[f195,f70])).
% 2.77/0.79  fof(f195,plain,(
% 2.77/0.79    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl5_10),
% 2.77/0.79    inference(avatar_component_clause,[],[f193])).
% 2.77/0.79  fof(f320,plain,(
% 2.77/0.79    spl5_1 | ~spl5_10 | spl5_11),
% 2.77/0.79    inference(avatar_contradiction_clause,[],[f316])).
% 2.77/0.79  fof(f316,plain,(
% 2.77/0.79    $false | (spl5_1 | ~spl5_10 | spl5_11)),
% 2.77/0.79    inference(unit_resulting_resolution,[],[f199,f195,f74,f195,f51])).
% 2.77/0.79  fof(f74,plain,(
% 2.77/0.79    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) | spl5_1),
% 2.77/0.79    inference(avatar_component_clause,[],[f72])).
% 2.77/0.79  fof(f72,plain,(
% 2.77/0.79    spl5_1 <=> k2_enumset1(sK0,sK0,sK0,sK1) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 2.77/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.77/0.79  fof(f199,plain,(
% 2.77/0.79    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | spl5_11),
% 2.77/0.79    inference(avatar_component_clause,[],[f197])).
% 2.77/0.79  fof(f197,plain,(
% 2.77/0.79    spl5_11 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)),
% 2.77/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.77/0.79  fof(f301,plain,(
% 2.77/0.79    spl5_10 | spl5_1),
% 2.77/0.79    inference(avatar_split_clause,[],[f300,f72,f193])).
% 2.77/0.79  fof(f300,plain,(
% 2.77/0.79    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | spl5_1),
% 2.77/0.79    inference(duplicate_literal_removal,[],[f299])).
% 2.77/0.79  fof(f299,plain,(
% 2.77/0.79    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | spl5_1),
% 2.77/0.79    inference(equality_resolution,[],[f120])).
% 2.77/0.79  fof(f120,plain,(
% 2.77/0.79    ( ! [X20] : (k2_enumset1(sK0,sK0,sK0,sK1) != X20 | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X20),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X20),X20)) ) | spl5_1),
% 2.77/0.79    inference(superposition,[],[f74,f53])).
% 2.77/0.79  fof(f53,plain,(
% 2.77/0.79    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.77/0.79    inference(definition_unfolding,[],[f35,f30])).
% 2.77/0.79  fof(f35,plain,(
% 2.77/0.79    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.77/0.79    inference(cnf_transformation,[],[f17])).
% 2.77/0.79  fof(f287,plain,(
% 2.77/0.79    spl5_8 | spl5_20 | spl5_2),
% 2.77/0.79    inference(avatar_split_clause,[],[f281,f77,f284,f179])).
% 2.77/0.79  fof(f281,plain,(
% 2.77/0.79    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_2),
% 2.77/0.79    inference(equality_resolution,[],[f119])).
% 2.77/0.79  fof(f119,plain,(
% 2.77/0.79    ( ! [X19] : (k2_enumset1(sK1,sK1,sK1,sK1) != X19 | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X19),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X19),X19)) ) | spl5_2),
% 2.77/0.79    inference(superposition,[],[f79,f53])).
% 2.77/0.79  fof(f276,plain,(
% 2.77/0.79    spl5_6 | spl5_19 | spl5_3),
% 2.77/0.79    inference(avatar_split_clause,[],[f270,f82,f273,f164])).
% 2.77/0.79  fof(f270,plain,(
% 2.77/0.79    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_3),
% 2.77/0.79    inference(equality_resolution,[],[f118])).
% 2.77/0.79  fof(f118,plain,(
% 2.77/0.79    ( ! [X18] : (k2_enumset1(sK0,sK0,sK0,sK0) != X18 | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X18),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X18),X18)) ) | spl5_3),
% 2.77/0.79    inference(superposition,[],[f84,f53])).
% 2.77/0.79  fof(f219,plain,(
% 2.77/0.79    spl5_13 | spl5_14 | ~spl5_12),
% 2.77/0.79    inference(avatar_split_clause,[],[f209,f205,f216,f212])).
% 2.77/0.79  fof(f212,plain,(
% 2.77/0.79    spl5_13 <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)),
% 2.77/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.77/0.79  fof(f216,plain,(
% 2.77/0.79    spl5_14 <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)),
% 2.77/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.77/0.79  fof(f205,plain,(
% 2.77/0.79    spl5_12 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))),
% 2.77/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.77/0.79  fof(f209,plain,(
% 2.77/0.79    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | ~spl5_12),
% 2.77/0.79    inference(resolution,[],[f207,f70])).
% 2.77/0.79  fof(f207,plain,(
% 2.77/0.79    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl5_12),
% 2.77/0.79    inference(avatar_component_clause,[],[f205])).
% 2.77/0.79  fof(f208,plain,(
% 2.77/0.79    spl5_12 | spl5_4),
% 2.77/0.79    inference(avatar_split_clause,[],[f203,f87,f205])).
% 2.77/0.79  % (20125)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.77/0.79  fof(f87,plain,(
% 2.77/0.79    spl5_4 <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 2.77/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.77/0.79  fof(f203,plain,(
% 2.77/0.79    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | spl5_4),
% 2.77/0.79    inference(subsumption_resolution,[],[f202,f91])).
% 2.77/0.79  fof(f91,plain,(
% 2.77/0.79    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 2.77/0.79    inference(superposition,[],[f64,f50])).
% 2.77/0.79  fof(f50,plain,(
% 2.77/0.79    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.77/0.79    inference(definition_unfolding,[],[f27,f30])).
% 2.77/0.79  fof(f27,plain,(
% 2.77/0.79    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.77/0.79    inference(cnf_transformation,[],[f3])).
% 2.77/0.79  fof(f3,axiom,(
% 2.77/0.79    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.77/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.77/0.79  fof(f64,plain,(
% 2.77/0.79    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.77/0.79    inference(equality_resolution,[],[f55])).
% 2.77/0.79  fof(f55,plain,(
% 2.77/0.79    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.77/0.79    inference(definition_unfolding,[],[f33,f30])).
% 2.77/0.79  fof(f33,plain,(
% 2.77/0.79    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.77/0.79    inference(cnf_transformation,[],[f17])).
% 2.77/0.79  fof(f202,plain,(
% 2.77/0.79    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl5_4),
% 2.77/0.79    inference(equality_resolution,[],[f121])).
% 2.77/0.79  fof(f121,plain,(
% 2.77/0.79    ( ! [X21] : (k1_xboole_0 != X21 | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X21),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X21),X21)) ) | spl5_4),
% 2.77/0.79    inference(superposition,[],[f89,f53])).
% 2.77/0.79  fof(f89,plain,(
% 2.77/0.79    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) | spl5_4),
% 2.77/0.79    inference(avatar_component_clause,[],[f87])).
% 2.77/0.79  fof(f186,plain,(
% 2.77/0.79    spl5_8 | ~spl5_9 | spl5_2),
% 2.77/0.79    inference(avatar_split_clause,[],[f176,f77,f183,f179])).
% 2.77/0.79  fof(f176,plain,(
% 2.77/0.79    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_2),
% 2.77/0.79    inference(equality_resolution,[],[f105])).
% 2.77/0.79  fof(f105,plain,(
% 2.77/0.79    ( ! [X15] : (k2_enumset1(sK1,sK1,sK1,sK1) != X15 | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X15),sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X15),X15)) ) | spl5_2),
% 2.77/0.79    inference(superposition,[],[f79,f52])).
% 2.77/0.79  fof(f52,plain,(
% 2.77/0.79    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.77/0.79    inference(definition_unfolding,[],[f36,f30])).
% 2.77/0.79  fof(f36,plain,(
% 2.77/0.79    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.77/0.79    inference(cnf_transformation,[],[f17])).
% 2.77/0.79  fof(f171,plain,(
% 2.77/0.79    spl5_6 | ~spl5_7 | spl5_3),
% 2.77/0.79    inference(avatar_split_clause,[],[f161,f82,f168,f164])).
% 2.77/0.79  fof(f161,plain,(
% 2.77/0.79    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_3),
% 2.77/0.79    inference(equality_resolution,[],[f104])).
% 2.77/0.79  fof(f104,plain,(
% 2.77/0.79    ( ! [X14] : (k2_enumset1(sK0,sK0,sK0,sK0) != X14 | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X14),sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X14),X14)) ) | spl5_3),
% 2.77/0.79    inference(superposition,[],[f84,f52])).
% 2.77/0.79  fof(f128,plain,(
% 2.77/0.79    ~spl5_5 | spl5_4),
% 2.77/0.79    inference(avatar_split_clause,[],[f123,f87,f125])).
% 2.77/0.79  fof(f125,plain,(
% 2.77/0.79    spl5_5 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)),
% 2.77/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.77/0.79  fof(f123,plain,(
% 2.77/0.79    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | spl5_4),
% 2.77/0.79    inference(subsumption_resolution,[],[f122,f91])).
% 2.77/0.79  fof(f122,plain,(
% 2.77/0.79    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl5_4),
% 2.77/0.79    inference(equality_resolution,[],[f107])).
% 2.77/0.79  fof(f107,plain,(
% 2.77/0.79    ( ! [X17] : (k1_xboole_0 != X17 | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X17),sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X17),X17)) ) | spl5_4),
% 2.77/0.79    inference(superposition,[],[f89,f52])).
% 2.77/0.79  fof(f90,plain,(
% 2.77/0.79    ~spl5_4),
% 2.77/0.79    inference(avatar_split_clause,[],[f49,f87])).
% 2.77/0.79  fof(f49,plain,(
% 2.77/0.79    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 2.77/0.79    inference(definition_unfolding,[],[f23,f30,f44])).
% 2.77/0.79  fof(f23,plain,(
% 2.77/0.79    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.77/0.79    inference(cnf_transformation,[],[f12])).
% 2.77/0.79  fof(f12,plain,(
% 2.77/0.79    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.77/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 2.77/0.79  fof(f11,plain,(
% 2.77/0.79    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) => (k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.77/0.79    introduced(choice_axiom,[])).
% 2.77/0.79  fof(f10,plain,(
% 2.77/0.79    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 2.77/0.79    inference(ennf_transformation,[],[f9])).
% 2.77/0.79  fof(f9,negated_conjecture,(
% 2.77/0.79    ~! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 2.77/0.79    inference(negated_conjecture,[],[f8])).
% 2.77/0.79  fof(f8,conjecture,(
% 2.77/0.79    ! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 2.77/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_zfmisc_1)).
% 2.77/0.79  fof(f85,plain,(
% 2.77/0.79    ~spl5_3),
% 2.77/0.79    inference(avatar_split_clause,[],[f48,f82])).
% 2.77/0.79  fof(f48,plain,(
% 2.77/0.79    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 2.77/0.79    inference(definition_unfolding,[],[f24,f30,f44,f45])).
% 2.77/0.79  fof(f45,plain,(
% 2.77/0.79    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.77/0.79    inference(definition_unfolding,[],[f28,f44])).
% 2.77/0.79  fof(f28,plain,(
% 2.77/0.79    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.77/0.79    inference(cnf_transformation,[],[f5])).
% 2.77/0.79  fof(f5,axiom,(
% 2.77/0.79    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.77/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.77/0.79  fof(f24,plain,(
% 2.77/0.79    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)),
% 2.77/0.79    inference(cnf_transformation,[],[f12])).
% 2.77/0.79  fof(f80,plain,(
% 2.77/0.79    ~spl5_2),
% 2.77/0.79    inference(avatar_split_clause,[],[f47,f77])).
% 2.77/0.79  fof(f47,plain,(
% 2.77/0.79    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK1,sK1,sK1,sK1)),
% 2.77/0.79    inference(definition_unfolding,[],[f25,f30,f44,f45])).
% 2.77/0.79  fof(f25,plain,(
% 2.77/0.79    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)),
% 2.77/0.79    inference(cnf_transformation,[],[f12])).
% 2.77/0.79  fof(f75,plain,(
% 2.77/0.79    ~spl5_1),
% 2.77/0.79    inference(avatar_split_clause,[],[f46,f72])).
% 2.77/0.79  fof(f46,plain,(
% 2.77/0.79    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 2.77/0.79    inference(definition_unfolding,[],[f26,f44,f30,f44])).
% 2.77/0.79  fof(f26,plain,(
% 2.77/0.79    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.77/0.79    inference(cnf_transformation,[],[f12])).
% 2.77/0.79  % SZS output end Proof for theBenchmark
% 2.77/0.79  % (20114)------------------------------
% 2.77/0.79  % (20114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.77/0.79  % (20114)Termination reason: Refutation
% 2.77/0.79  
% 2.77/0.79  % (20114)Memory used [KB]: 11385
% 2.77/0.79  % (20114)Time elapsed: 0.185 s
% 2.77/0.79  % (20114)------------------------------
% 2.77/0.79  % (20114)------------------------------
% 2.77/0.80  % (20016)Success in time 0.43 s
%------------------------------------------------------------------------------
