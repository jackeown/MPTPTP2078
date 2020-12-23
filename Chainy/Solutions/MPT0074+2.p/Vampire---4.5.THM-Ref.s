%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0074+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  76 expanded)
%              Number of leaves         :   11 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :  111 ( 225 expanded)
%              Number of equality atoms :   15 (  38 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f716,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f351,f356,f361,f366,f418,f703,f714])).

fof(f714,plain,
    ( ~ spl14_2
    | spl14_8
    | ~ spl14_12 ),
    inference(avatar_contradiction_clause,[],[f713])).

fof(f713,plain,
    ( $false
    | ~ spl14_2
    | spl14_8
    | ~ spl14_12 ),
    inference(subsumption_resolution,[],[f708,f508])).

fof(f508,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | ~ spl14_2
    | spl14_8 ),
    inference(unit_resulting_resolution,[],[f355,f417,f231])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f130])).

fof(f130,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f105])).

fof(f105,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f417,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | spl14_8 ),
    inference(avatar_component_clause,[],[f415])).

fof(f415,plain,
    ( spl14_8
  <=> r1_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f355,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl14_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f708,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl14_12 ),
    inference(unit_resulting_resolution,[],[f702,f234])).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f702,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f700])).

fof(f700,plain,
    ( spl14_12
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f703,plain,
    ( spl14_12
    | ~ spl14_1
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f453,f358,f348,f700])).

fof(f348,plain,
    ( spl14_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f358,plain,
    ( spl14_3
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f453,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl14_1
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f350,f360,f231])).

fof(f360,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f358])).

fof(f350,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f348])).

fof(f418,plain,
    ( ~ spl14_8
    | spl14_4 ),
    inference(avatar_split_clause,[],[f381,f363,f415])).

fof(f363,plain,
    ( spl14_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f381,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | spl14_4 ),
    inference(unit_resulting_resolution,[],[f365,f241])).

fof(f241,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f135])).

fof(f135,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f108])).

fof(f108,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f365,plain,
    ( k1_xboole_0 != sK0
    | spl14_4 ),
    inference(avatar_component_clause,[],[f363])).

fof(f366,plain,(
    ~ spl14_4 ),
    inference(avatar_split_clause,[],[f212,f363])).

fof(f212,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f171])).

fof(f171,plain,
    ( k1_xboole_0 != sK0
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f123,f170])).

fof(f170,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X0
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
   => ( k1_xboole_0 != sK0
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f123,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f122])).

fof(f122,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f110])).

fof(f110,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f109])).

fof(f109,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f361,plain,(
    spl14_3 ),
    inference(avatar_split_clause,[],[f211,f358])).

fof(f211,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f171])).

fof(f356,plain,(
    spl14_2 ),
    inference(avatar_split_clause,[],[f210,f353])).

fof(f210,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f171])).

fof(f351,plain,(
    spl14_1 ),
    inference(avatar_split_clause,[],[f209,f348])).

fof(f209,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f171])).
%------------------------------------------------------------------------------
