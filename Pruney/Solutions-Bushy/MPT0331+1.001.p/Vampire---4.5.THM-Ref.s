%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0331+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:46 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   51 (  76 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :  138 ( 221 expanded)
%              Number of equality atoms :   22 (  40 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f33,f37,f45,f49,f59,f65,f78,f152])).

fof(f152,plain,
    ( spl3_1
    | spl3_2
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl3_1
    | spl3_2
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f149,f22])).

fof(f22,plain,
    ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl3_1
  <=> sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f149,plain,
    ( sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | spl3_2
    | ~ spl3_12 ),
    inference(resolution,[],[f77,f27])).

fof(f27,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f77,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK2)
        | sK2 = k4_xboole_0(sK2,k2_tarski(sK0,X1)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_12
  <=> ! [X1] :
        ( r2_hidden(X1,sK2)
        | sK2 = k4_xboole_0(sK2,k2_tarski(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f78,plain,
    ( spl3_12
    | spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f67,f63,f30,f76])).

fof(f30,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f63,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,X1)
        | r2_hidden(X2,X1)
        | k4_xboole_0(X1,k2_tarski(X0,X2)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f67,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK2)
        | sK2 = k4_xboole_0(sK2,k2_tarski(sK0,X1)) )
    | spl3_3
    | ~ spl3_10 ),
    inference(resolution,[],[f64,f32])).

fof(f32,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,X1)
        | r2_hidden(X2,X1)
        | k4_xboole_0(X1,k2_tarski(X0,X2)) = X1 )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f63])).

fof(f65,plain,
    ( spl3_10
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f60,f57,f43,f63])).

fof(f43,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f57,plain,
    ( spl3_9
  <=> ! [X3,X5,X4] :
        ( r2_hidden(X3,X4)
        | r2_hidden(X5,X4)
        | r1_xboole_0(X4,k2_tarski(X5,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f60,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,X1)
        | r2_hidden(X2,X1)
        | k4_xboole_0(X1,k2_tarski(X0,X2)) = X1 )
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(resolution,[],[f58,f44])).

fof(f44,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f58,plain,
    ( ! [X4,X5,X3] :
        ( r1_xboole_0(X4,k2_tarski(X5,X3))
        | r2_hidden(X5,X4)
        | r2_hidden(X3,X4) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f51,f47,f35,f57])).

fof(f35,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f47,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f51,plain,
    ( ! [X4,X5,X3] :
        ( r2_hidden(X3,X4)
        | r2_hidden(X5,X4)
        | r1_xboole_0(X4,k2_tarski(X5,X3)) )
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f48,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f47])).

fof(f49,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f18,f47])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l168_zfmisc_1)).

fof(f45,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f16,f43])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f37,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f33,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f12,f30])).

fof(f12,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f28,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f13,f25])).

fof(f13,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f14,f20])).

fof(f14,plain,(
    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
