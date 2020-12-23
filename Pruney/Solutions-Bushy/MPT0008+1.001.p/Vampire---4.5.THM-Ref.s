%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0008+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:10 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 101 expanded)
%              Number of leaves         :   14 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :  162 ( 332 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f33,f37,f41,f45,f56,f61,f67,f73,f77])).

fof(f77,plain,
    ( ~ spl4_2
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f74,f71,f20,f25])).

fof(f25,plain,
    ( spl4_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f20,plain,
    ( spl4_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f71,plain,
    ( spl4_11
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f74,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(resolution,[],[f72,f22])).

fof(f22,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ r1_tarski(X0,sK2) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f71])).

fof(f73,plain,
    ( spl4_3
    | spl4_11
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f68,f65,f35,f71,f30])).

fof(f30,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f35,plain,
    ( spl4_4
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | r2_hidden(sK3(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f65,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r2_hidden(sK3(sK0,sK2),X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(sK0,X0)
        | r1_tarski(sK0,sK2) )
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(resolution,[],[f66,f36])).

fof(f36,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X0)
        | r1_tarski(X0,X1) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(sK0,sK2),X1)
        | ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(X1,X0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f65])).

fof(f67,plain,
    ( spl4_10
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f63,f59,f43,f65])).

fof(f43,plain,
    ( spl4_6
  <=> ! [X1,X3,X0] :
        ( r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f59,plain,
    ( spl4_9
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r2_hidden(sK3(sK0,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r2_hidden(sK3(sK0,sK2),X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(resolution,[],[f60,f44])).

fof(f44,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK0,sK2),X0)
        | ~ r1_tarski(X0,sK2) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f59])).

fof(f61,plain,
    ( spl4_9
    | spl4_3
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f57,f54,f30,f59])).

fof(f54,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK3(X0,X1),X2)
        | ~ r1_tarski(X2,X1)
        | r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f57,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r2_hidden(sK3(sK0,sK2),X0) )
    | spl4_3
    | ~ spl4_8 ),
    inference(resolution,[],[f55,f32])).

fof(f32,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f55,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ r1_tarski(X2,X1)
        | ~ r2_hidden(sK3(X0,X1),X2) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f56,plain,
    ( spl4_8
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f48,f43,f39,f54])).

fof(f39,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f48,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK3(X0,X1),X2)
        | ~ r1_tarski(X2,X1)
        | r1_tarski(X0,X1) )
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f44,f40])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(X0,X1),X1)
        | r1_tarski(X0,X1) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f45,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f16,f43])).

fof(f16,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f41,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f15,f30])).

fof(f15,plain,(
    ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ~ r1_tarski(sK0,sK2)
    & r1_tarski(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X2)
        & r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK0,sK2)
      & r1_tarski(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X2)
      & r1_tarski(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X2)
      & r1_tarski(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_tarski(X0,X2) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f28,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f14,f25])).

fof(f14,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f23,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f13,f20])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
