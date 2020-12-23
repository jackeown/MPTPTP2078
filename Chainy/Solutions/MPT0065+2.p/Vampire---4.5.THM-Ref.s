%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0065+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  53 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   95 ( 147 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f619,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f324,f329,f334,f562,f617,f618])).

fof(f618,plain,
    ( sK1 != sK2
    | r2_xboole_0(sK0,sK2)
    | ~ r2_xboole_0(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f617,plain,
    ( spl12_1
    | ~ spl12_3
    | ~ spl12_15 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | spl12_1
    | ~ spl12_3
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f577,f561])).

fof(f561,plain,
    ( r2_xboole_0(sK1,sK2)
    | ~ spl12_15 ),
    inference(avatar_component_clause,[],[f559])).

fof(f559,plain,
    ( spl12_15
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f577,plain,
    ( ~ r2_xboole_0(sK1,sK2)
    | spl12_1
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f323,f333,f233])).

fof(f233,plain,(
    ! [X2,X0,X1] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f146])).

fof(f146,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f145])).

fof(f145,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f97])).

fof(f97,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_xboole_1)).

fof(f333,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl12_3
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f323,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl12_1
  <=> r2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f562,plain,
    ( spl12_15
    | spl12_13
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f441,f326,f546,f559])).

fof(f546,plain,
    ( spl12_13
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f326,plain,
    ( spl12_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f441,plain,
    ( sK1 = sK2
    | r2_xboole_0(sK1,sK2)
    | ~ spl12_2 ),
    inference(resolution,[],[f328,f239])).

fof(f239,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f169])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f328,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f326])).

fof(f334,plain,(
    spl12_3 ),
    inference(avatar_split_clause,[],[f196,f331])).

fof(f196,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f159])).

fof(f159,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r1_tarski(sK1,sK2)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f113,f158])).

fof(f158,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r1_tarski(sK1,sK2)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f113,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f112])).

fof(f112,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f100])).

fof(f100,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f99])).

fof(f99,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f329,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f197,f326])).

fof(f197,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f159])).

fof(f324,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f198,f321])).

fof(f198,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f159])).
%------------------------------------------------------------------------------
