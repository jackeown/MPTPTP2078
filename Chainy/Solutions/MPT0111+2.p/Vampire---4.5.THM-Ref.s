%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0111+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 133 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  180 ( 560 expanded)
%              Number of equality atoms :   25 ( 112 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f450,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f390,f397,f399,f416,f434,f449])).

fof(f449,plain,
    ( ~ spl13_1
    | spl13_2 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | ~ spl13_1
    | spl13_2 ),
    inference(subsumption_resolution,[],[f445,f419])).

fof(f419,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl13_2 ),
    inference(resolution,[],[f389,f269])).

fof(f269,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f219])).

fof(f219,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f218])).

fof(f218,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f389,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | spl13_2 ),
    inference(avatar_component_clause,[],[f387])).

fof(f387,plain,
    ( spl13_2
  <=> r3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f445,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl13_1 ),
    inference(resolution,[],[f384,f280])).

fof(f280,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f223])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f222])).

fof(f222,plain,(
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

fof(f384,plain,
    ( r2_xboole_0(sK1,sK0)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f383])).

fof(f383,plain,
    ( spl13_1
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f434,plain,
    ( spl13_2
    | ~ spl13_3 ),
    inference(avatar_contradiction_clause,[],[f433])).

fof(f433,plain,
    ( $false
    | spl13_2
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f430,f418])).

fof(f418,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl13_2 ),
    inference(resolution,[],[f389,f268])).

fof(f268,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f219])).

fof(f430,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl13_3 ),
    inference(resolution,[],[f395,f280])).

fof(f395,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl13_3
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f416,plain,
    ( spl13_1
    | ~ spl13_2
    | spl13_3 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | spl13_1
    | ~ spl13_2
    | spl13_3 ),
    inference(subsumption_resolution,[],[f414,f408])).

fof(f408,plain,
    ( r1_tarski(sK0,sK1)
    | spl13_1
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f407,f405])).

% (9688)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
fof(f405,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl13_1 ),
    inference(subsumption_resolution,[],[f400,f392])).

fof(f392,plain,(
    sK0 != sK1 ),
    inference(subsumption_resolution,[],[f391,f271])).

fof(f271,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f161])).

fof(f161,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(rectify,[],[f46])).

fof(f46,axiom,(
    ! [X0,X1] : r3_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).

fof(f391,plain,
    ( ~ r3_xboole_0(sK0,sK0)
    | sK0 != sK1 ),
    inference(inner_rewriting,[],[f265])).

fof(f265,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | sK0 != sK1 ),
    inference(cnf_transformation,[],[f217])).

fof(f217,plain,
    ( ( ~ r3_xboole_0(sK0,sK1)
      | ( ~ r2_xboole_0(sK1,sK0)
        & sK0 != sK1
        & ~ r2_xboole_0(sK0,sK1) ) )
    & ( r3_xboole_0(sK0,sK1)
      | r2_xboole_0(sK1,sK0)
      | sK0 = sK1
      | r2_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f215,f216])).

fof(f216,plain,
    ( ? [X0,X1] :
        ( ( ~ r3_xboole_0(X0,X1)
          | ( ~ r2_xboole_0(X1,X0)
            & X0 != X1
            & ~ r2_xboole_0(X0,X1) ) )
        & ( r3_xboole_0(X0,X1)
          | r2_xboole_0(X1,X0)
          | X0 = X1
          | r2_xboole_0(X0,X1) ) )
   => ( ( ~ r3_xboole_0(sK0,sK1)
        | ( ~ r2_xboole_0(sK1,sK0)
          & sK0 != sK1
          & ~ r2_xboole_0(sK0,sK1) ) )
      & ( r3_xboole_0(sK0,sK1)
        | r2_xboole_0(sK1,sK0)
        | sK0 = sK1
        | r2_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f215,plain,(
    ? [X0,X1] :
      ( ( ~ r3_xboole_0(X0,X1)
        | ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) ) )
      & ( r3_xboole_0(X0,X1)
        | r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f214])).

fof(f214,plain,(
    ? [X0,X1] :
      ( ( ~ r3_xboole_0(X0,X1)
        | ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) ) )
      & ( r3_xboole_0(X0,X1)
        | r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f165])).

fof(f165,plain,(
    ? [X0,X1] :
      ( ( r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    <~> r3_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f53])).

fof(f53,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( ~ r2_xboole_0(X1,X0)
            & X0 != X1
            & ~ r2_xboole_0(X0,X1) )
      <=> r3_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f52])).

fof(f52,conjecture,(
    ! [X0,X1] :
      ( ~ ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) )
    <=> r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_xboole_1)).

fof(f400,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,sK0)
    | spl13_1 ),
    inference(resolution,[],[f385,f282])).

fof(f282,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f223])).

fof(f385,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | spl13_1 ),
    inference(avatar_component_clause,[],[f383])).

fof(f407,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1)
    | ~ spl13_2 ),
    inference(resolution,[],[f388,f267])).

fof(f267,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | r1_tarski(X0,X1)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f219])).

fof(f388,plain,
    ( r3_xboole_0(sK0,sK1)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f387])).

fof(f414,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl13_3 ),
    inference(subsumption_resolution,[],[f409,f392])).

fof(f409,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK0,sK1)
    | spl13_3 ),
    inference(resolution,[],[f396,f282])).

fof(f396,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | spl13_3 ),
    inference(avatar_component_clause,[],[f394])).

fof(f399,plain,
    ( spl13_3
    | spl13_1
    | spl13_2 ),
    inference(avatar_split_clause,[],[f398,f387,f383,f394])).

fof(f398,plain,
    ( r3_xboole_0(sK0,sK1)
    | r2_xboole_0(sK1,sK0)
    | r2_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f263,f392])).

fof(f263,plain,
    ( r3_xboole_0(sK0,sK1)
    | r2_xboole_0(sK1,sK0)
    | sK0 = sK1
    | r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f217])).

fof(f397,plain,
    ( ~ spl13_3
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f264,f387,f394])).

fof(f264,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f217])).

fof(f390,plain,
    ( ~ spl13_1
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f266,f387,f383])).

fof(f266,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f217])).
%------------------------------------------------------------------------------
