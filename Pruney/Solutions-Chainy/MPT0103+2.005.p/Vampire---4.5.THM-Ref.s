%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 131 expanded)
%              Number of leaves         :   24 (  62 expanded)
%              Depth                    :    7
%              Number of atoms          :  244 ( 401 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f434,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f42,f47,f59,f63,f67,f71,f83,f99,f181,f193,f276,f350,f389,f412,f433])).

fof(f433,plain,
    ( spl4_3
    | ~ spl4_6
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f423,f410,f57,f44])).

fof(f44,plain,
    ( spl4_3
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f57,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | r2_hidden(sK3(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f410,plain,
    ( spl4_49
  <=> ! [X0] : ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),k4_xboole_0(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f423,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))
    | ~ spl4_6
    | ~ spl4_49 ),
    inference(resolution,[],[f411,f58])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X0)
        | r1_tarski(X0,X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f411,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),k4_xboole_0(sK0,X0))
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f410])).

fof(f412,plain,
    ( spl4_49
    | ~ spl4_1
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f398,f387,f36,f410])).

fof(f36,plain,
    ( spl4_1
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f387,plain,
    ( spl4_47
  <=> ! [X5] :
        ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),X5)
        | ~ r1_tarski(X5,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f398,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),k4_xboole_0(sK0,X0))
    | ~ spl4_1
    | ~ spl4_47 ),
    inference(resolution,[],[f388,f37])).

fof(f37,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f388,plain,
    ( ! [X5] :
        ( ~ r1_tarski(X5,sK0)
        | ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),X5) )
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f387])).

fof(f389,plain,
    ( spl4_47
    | ~ spl4_9
    | spl4_43 ),
    inference(avatar_split_clause,[],[f355,f347,f69,f387])).

fof(f69,plain,
    ( spl4_9
  <=> ! [X1,X3,X0] :
        ( r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f347,plain,
    ( spl4_43
  <=> r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f355,plain,
    ( ! [X5] :
        ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),X5)
        | ~ r1_tarski(X5,sK0) )
    | ~ spl4_9
    | spl4_43 ),
    inference(resolution,[],[f349,f70])).

fof(f70,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f349,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),sK0)
    | spl4_43 ),
    inference(avatar_component_clause,[],[f347])).

fof(f350,plain,
    ( spl4_27
    | ~ spl4_43
    | spl4_3
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f281,f274,f44,f347,f190])).

fof(f190,plain,
    ( spl4_27
  <=> r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f274,plain,
    ( spl4_36
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK3(X0,k5_xboole_0(X1,X2)),X2)
        | ~ r2_hidden(sK3(X0,k5_xboole_0(X1,X2)),X1)
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f281,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),sK1)
    | spl4_3
    | ~ spl4_36 ),
    inference(resolution,[],[f275,f46])).

fof(f46,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f275,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r2_hidden(sK3(X0,k5_xboole_0(X1,X2)),X1)
        | r2_hidden(sK3(X0,k5_xboole_0(X1,X2)),X2) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f274])).

fof(f276,plain,
    ( spl4_36
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f119,f97,f61,f274])).

fof(f61,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f97,plain,
    ( spl4_14
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | r2_hidden(X0,X2)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f119,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK3(X0,k5_xboole_0(X1,X2)),X2)
        | ~ r2_hidden(sK3(X0,k5_xboole_0(X1,X2)),X1)
        | r1_tarski(X0,k5_xboole_0(X1,X2)) )
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(resolution,[],[f98,f62])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(X0,X1),X1)
        | r1_tarski(X0,X1) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f98,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | r2_hidden(X0,X2)
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f97])).

fof(f193,plain,
    ( ~ spl4_27
    | spl4_3
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f186,f179,f44,f190])).

fof(f179,plain,
    ( spl4_25
  <=> ! [X7,X8,X6] :
        ( ~ r2_hidden(sK3(k4_xboole_0(X6,X7),X8),X7)
        | r1_tarski(k4_xboole_0(X6,X7),X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f186,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),sK1)
    | spl4_3
    | ~ spl4_25 ),
    inference(resolution,[],[f180,f46])).

fof(f180,plain,
    ( ! [X6,X8,X7] :
        ( r1_tarski(k4_xboole_0(X6,X7),X8)
        | ~ r2_hidden(sK3(k4_xboole_0(X6,X7),X8),X7) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f179])).

fof(f181,plain,
    ( spl4_25
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f90,f81,f57,f179])).

fof(f81,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f90,plain,
    ( ! [X6,X8,X7] :
        ( ~ r2_hidden(sK3(k4_xboole_0(X6,X7),X8),X7)
        | r1_tarski(k4_xboole_0(X6,X7),X8) )
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(resolution,[],[f82,f58])).

fof(f82,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k4_xboole_0(X2,X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f81])).

fof(f99,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f33,f97])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f83,plain,
    ( spl4_11
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f74,f65,f40,f81])).

fof(f40,plain,
    ( spl4_2
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f65,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) )
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(resolution,[],[f66,f41])).

fof(f41,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f66,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f71,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f28,f69])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
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

fof(f67,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f27,f65])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f63,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f29,f57])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1] : ~ r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))
   => ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] : ~ r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

fof(f42,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f24,f40])).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f38,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f23,f36])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:56:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (21060)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.45  % (21060)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f434,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f38,f42,f47,f59,f63,f67,f71,f83,f99,f181,f193,f276,f350,f389,f412,f433])).
% 0.21/0.45  fof(f433,plain,(
% 0.21/0.45    spl4_3 | ~spl4_6 | ~spl4_49),
% 0.21/0.45    inference(avatar_split_clause,[],[f423,f410,f57,f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    spl4_3 <=> r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    spl4_6 <=> ! [X1,X0] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.45  fof(f410,plain,(
% 0.21/0.45    spl4_49 <=> ! [X0] : ~r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),k4_xboole_0(sK0,X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.21/0.45  fof(f423,plain,(
% 0.21/0.45    r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) | (~spl4_6 | ~spl4_49)),
% 0.21/0.45    inference(resolution,[],[f411,f58])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) ) | ~spl4_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f57])).
% 0.21/0.45  fof(f411,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),k4_xboole_0(sK0,X0))) ) | ~spl4_49),
% 0.21/0.45    inference(avatar_component_clause,[],[f410])).
% 0.21/0.45  fof(f412,plain,(
% 0.21/0.45    spl4_49 | ~spl4_1 | ~spl4_47),
% 0.21/0.45    inference(avatar_split_clause,[],[f398,f387,f36,f410])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    spl4_1 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.45  fof(f387,plain,(
% 0.21/0.45    spl4_47 <=> ! [X5] : (~r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),X5) | ~r1_tarski(X5,sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.21/0.45  fof(f398,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),k4_xboole_0(sK0,X0))) ) | (~spl4_1 | ~spl4_47)),
% 0.21/0.45    inference(resolution,[],[f388,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl4_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f36])).
% 0.21/0.45  fof(f388,plain,(
% 0.21/0.45    ( ! [X5] : (~r1_tarski(X5,sK0) | ~r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),X5)) ) | ~spl4_47),
% 0.21/0.45    inference(avatar_component_clause,[],[f387])).
% 0.21/0.45  fof(f389,plain,(
% 0.21/0.45    spl4_47 | ~spl4_9 | spl4_43),
% 0.21/0.45    inference(avatar_split_clause,[],[f355,f347,f69,f387])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    spl4_9 <=> ! [X1,X3,X0] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.45  fof(f347,plain,(
% 0.21/0.45    spl4_43 <=> r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.21/0.45  fof(f355,plain,(
% 0.21/0.45    ( ! [X5] : (~r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),X5) | ~r1_tarski(X5,sK0)) ) | (~spl4_9 | spl4_43)),
% 0.21/0.45    inference(resolution,[],[f349,f70])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) ) | ~spl4_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f69])).
% 0.21/0.45  fof(f349,plain,(
% 0.21/0.45    ~r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),sK0) | spl4_43),
% 0.21/0.45    inference(avatar_component_clause,[],[f347])).
% 0.21/0.45  fof(f350,plain,(
% 0.21/0.45    spl4_27 | ~spl4_43 | spl4_3 | ~spl4_36),
% 0.21/0.45    inference(avatar_split_clause,[],[f281,f274,f44,f347,f190])).
% 0.21/0.45  fof(f190,plain,(
% 0.21/0.45    spl4_27 <=> r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.45  fof(f274,plain,(
% 0.21/0.45    spl4_36 <=> ! [X1,X0,X2] : (r2_hidden(sK3(X0,k5_xboole_0(X1,X2)),X2) | ~r2_hidden(sK3(X0,k5_xboole_0(X1,X2)),X1) | r1_tarski(X0,k5_xboole_0(X1,X2)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.45  fof(f281,plain,(
% 0.21/0.45    ~r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),sK1) | (spl4_3 | ~spl4_36)),
% 0.21/0.45    inference(resolution,[],[f275,f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ~r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) | spl4_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f44])).
% 0.21/0.45  fof(f275,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(sK3(X0,k5_xboole_0(X1,X2)),X1) | r2_hidden(sK3(X0,k5_xboole_0(X1,X2)),X2)) ) | ~spl4_36),
% 0.21/0.45    inference(avatar_component_clause,[],[f274])).
% 0.21/0.45  fof(f276,plain,(
% 0.21/0.45    spl4_36 | ~spl4_7 | ~spl4_14),
% 0.21/0.45    inference(avatar_split_clause,[],[f119,f97,f61,f274])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    spl4_7 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    spl4_14 <=> ! [X1,X0,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.45  fof(f119,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,k5_xboole_0(X1,X2)),X2) | ~r2_hidden(sK3(X0,k5_xboole_0(X1,X2)),X1) | r1_tarski(X0,k5_xboole_0(X1,X2))) ) | (~spl4_7 | ~spl4_14)),
% 0.21/0.45    inference(resolution,[],[f98,f62])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) ) | ~spl4_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f61])).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) ) | ~spl4_14),
% 0.21/0.45    inference(avatar_component_clause,[],[f97])).
% 0.21/0.45  fof(f193,plain,(
% 0.21/0.45    ~spl4_27 | spl4_3 | ~spl4_25),
% 0.21/0.45    inference(avatar_split_clause,[],[f186,f179,f44,f190])).
% 0.21/0.45  fof(f179,plain,(
% 0.21/0.45    spl4_25 <=> ! [X7,X8,X6] : (~r2_hidden(sK3(k4_xboole_0(X6,X7),X8),X7) | r1_tarski(k4_xboole_0(X6,X7),X8))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.45  fof(f186,plain,(
% 0.21/0.45    ~r2_hidden(sK3(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),sK1) | (spl4_3 | ~spl4_25)),
% 0.21/0.45    inference(resolution,[],[f180,f46])).
% 0.21/0.45  fof(f180,plain,(
% 0.21/0.45    ( ! [X6,X8,X7] : (r1_tarski(k4_xboole_0(X6,X7),X8) | ~r2_hidden(sK3(k4_xboole_0(X6,X7),X8),X7)) ) | ~spl4_25),
% 0.21/0.45    inference(avatar_component_clause,[],[f179])).
% 0.21/0.45  fof(f181,plain,(
% 0.21/0.45    spl4_25 | ~spl4_6 | ~spl4_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f90,f81,f57,f179])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    spl4_11 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    ( ! [X6,X8,X7] : (~r2_hidden(sK3(k4_xboole_0(X6,X7),X8),X7) | r1_tarski(k4_xboole_0(X6,X7),X8)) ) | (~spl4_6 | ~spl4_11)),
% 0.21/0.45    inference(resolution,[],[f82,f58])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X2,X1)) | ~r2_hidden(X0,X1)) ) | ~spl4_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f81])).
% 0.21/0.45  fof(f99,plain,(
% 0.21/0.45    spl4_14),
% 0.21/0.45    inference(avatar_split_clause,[],[f33,f97])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.21/0.45    inference(nnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    spl4_11 | ~spl4_2 | ~spl4_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f74,f65,f40,f81])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    spl4_2 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl4_8 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X2,X1))) ) | (~spl4_2 | ~spl4_8)),
% 0.21/0.45    inference(resolution,[],[f66,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl4_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f40])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) ) | ~spl4_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f65])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    spl4_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f28,f69])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(rectify,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    spl4_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f27,f65])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(rectify,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    spl4_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f30,f61])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    spl4_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f29,f57])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ~spl4_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f22,f44])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ~r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ~r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ? [X0,X1] : ~r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) => ~r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0,X1] : ~r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.45    inference(negated_conjecture,[],[f6])).
% 0.21/0.45  fof(f6,conjecture,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    spl4_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f40])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    spl4_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f23,f36])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (21060)------------------------------
% 0.21/0.45  % (21060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (21060)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (21060)Memory used [KB]: 5628
% 0.21/0.45  % (21060)Time elapsed: 0.017 s
% 0.21/0.45  % (21060)------------------------------
% 0.21/0.45  % (21060)------------------------------
% 0.21/0.45  % (21043)Success in time 0.078 s
%------------------------------------------------------------------------------
