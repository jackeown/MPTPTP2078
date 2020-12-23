%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0332+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 (  61 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   95 ( 158 expanded)
%              Number of equality atoms :   25 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f23,f28,f32,f36,f42,f51,f76])).

fof(f76,plain,
    ( spl3_3
    | spl3_6
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | spl3_3
    | spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f69,f41])).

fof(f41,plain,
    ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_6
  <=> sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f69,plain,
    ( sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f50,f27])).

fof(f27,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f50,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | sK2 = k4_xboole_0(sK2,k2_tarski(X0,sK1)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_7
  <=> ! [X0] :
        ( r2_hidden(X0,sK2)
        | sK2 = k4_xboole_0(sK2,k2_tarski(X0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f51,plain,
    ( spl3_7
    | spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f43,f34,f20,f49])).

fof(f20,plain,
    ( spl3_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f34,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f43,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | sK2 = k4_xboole_0(sK2,k2_tarski(X0,sK1)) )
    | spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f35,f22])).

fof(f22,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f35,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f34])).

fof(f42,plain,
    ( ~ spl3_6
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f37,f30,f15,f39])).

fof(f15,plain,
    ( spl3_1
  <=> sK2 = k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f30,plain,
    ( spl3_4
  <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f37,plain,
    ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | spl3_1
    | ~ spl3_4 ),
    inference(superposition,[],[f17,f31])).

fof(f31,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f30])).

fof(f17,plain,
    ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f36,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f13,f34])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f32,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f12,f30])).

fof(f12,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f28,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f9,f25])).

fof(f9,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

fof(f23,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f10,f20])).

fof(f10,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f18,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f11,f15])).

fof(f11,plain,(
    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
