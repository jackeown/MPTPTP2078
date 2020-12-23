%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0387+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  45 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   74 ( 105 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f23,f27,f31,f36,f39])).

fof(f39,plain,
    ( spl1_1
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(avatar_contradiction_clause,[],[f38])).

fof(f38,plain,
    ( $false
    | spl1_1
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(subsumption_resolution,[],[f37,f17])).

fof(f17,plain,
    ( k1_xboole_0 != k1_setfam_1(sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f15,plain,
    ( spl1_1
  <=> k1_xboole_0 = k1_setfam_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f37,plain,
    ( k1_xboole_0 = k1_setfam_1(sK0)
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(resolution,[],[f35,f22])).

fof(f22,plain,
    ( r2_hidden(k1_xboole_0,sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl1_2
  <=> r2_hidden(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f35,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,X0)
        | k1_xboole_0 = k1_setfam_1(X0) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl1_5
  <=> ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,X0)
        | k1_xboole_0 = k1_setfam_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f36,plain,
    ( spl1_5
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f32,f29,f25,f34])).

fof(f25,plain,
    ( spl1_3
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f29,plain,
    ( spl1_4
  <=> ! [X1,X0] :
        ( r1_tarski(k1_setfam_1(X1),X0)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f32,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,X0)
        | k1_xboole_0 = k1_setfam_1(X0) )
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(resolution,[],[f30,f26])).

fof(f26,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f30,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_setfam_1(X1),X0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f29])).

fof(f31,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f13,f29])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f27,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f12,f25])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f23,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f10,f20])).

fof(f10,plain,(
    r2_hidden(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( k1_xboole_0 != k1_setfam_1(sK0)
    & r2_hidden(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f8])).

fof(f8,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k1_setfam_1(X0)
        & r2_hidden(k1_xboole_0,X0) )
   => ( k1_xboole_0 != k1_setfam_1(sK0)
      & r2_hidden(k1_xboole_0,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_setfam_1(X0)
      & r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k1_setfam_1(X0) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_xboole_0 = k1_setfam_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).

fof(f18,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f11,f15])).

fof(f11,plain,(
    k1_xboole_0 != k1_setfam_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
