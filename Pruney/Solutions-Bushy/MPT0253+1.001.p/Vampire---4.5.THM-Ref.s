%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0253+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:37 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   43 (  66 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :  113 ( 184 expanded)
%              Number of equality atoms :   16 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f33,f37,f41,f59,f94,f104])).

fof(f104,plain,
    ( spl3_1
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl3_1
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f102,f22])).

fof(f22,plain,
    ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl3_1
  <=> sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f102,plain,
    ( sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(resolution,[],[f93,f36])).

fof(f36,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f93,plain,
    ( r1_tarski(k2_tarski(sK0,sK2),sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_14
  <=> r1_tarski(k2_tarski(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f94,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f88,f57,f25,f91])).

fof(f25,plain,
    ( spl3_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f57,plain,
    ( spl3_9
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r1_tarski(k2_tarski(sK0,X1),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f88,plain,
    ( r1_tarski(k2_tarski(sK0,sK2),sK1)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f58,f27])).

fof(f27,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f58,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r1_tarski(k2_tarski(sK0,X1),sK1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f51,f39,f30,f57])).

fof(f30,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f39,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f51,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r1_tarski(k2_tarski(sK0,X1),sK1) )
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f40,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X2)
        | ~ r2_hidden(X1,X2)
        | r1_tarski(k2_tarski(X0,X1),X2) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f41,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f37,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f33,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f12,f30])).

fof(f12,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f28,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f13,f25])).

fof(f13,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f14,f20])).

fof(f14,plain,(
    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
