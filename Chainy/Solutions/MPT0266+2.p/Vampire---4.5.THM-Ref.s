%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0266+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  44 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   69 (  93 expanded)
%              Number of equality atoms :   14 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f690,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f591,f595,f652,f663,f689])).

fof(f689,plain,
    ( spl11_1
    | ~ spl11_7 ),
    inference(avatar_contradiction_clause,[],[f688])).

fof(f688,plain,
    ( $false
    | spl11_1
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f681,f590])).

fof(f590,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f589])).

fof(f589,plain,
    ( spl11_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f681,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl11_7 ),
    inference(resolution,[],[f462,f662])).

fof(f662,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f661])).

fof(f661,plain,
    ( spl11_7
  <=> r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f462,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f418])).

fof(f418,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f417])).

fof(f417,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f339])).

fof(f339,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f663,plain,
    ( spl11_7
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f655,f647,f661])).

fof(f647,plain,
    ( spl11_5
  <=> k2_tarski(sK0,sK1) = k3_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f655,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl11_5 ),
    inference(superposition,[],[f553,f648])).

fof(f648,plain,
    ( k2_tarski(sK0,sK1) = k3_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f647])).

fof(f553,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f652,plain,
    ( spl11_5
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f642,f593,f647])).

fof(f593,plain,
    ( spl11_2
  <=> k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f642,plain,
    ( k2_tarski(sK0,sK1) = k3_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ spl11_2 ),
    inference(superposition,[],[f594,f552])).

fof(f552,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f594,plain,
    ( k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f593])).

fof(f595,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f455,f593])).

fof(f455,plain,(
    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f414])).

fof(f414,plain,
    ( ~ r2_hidden(sK0,sK2)
    & k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f368,f413])).

fof(f413,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f368,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f363])).

fof(f363,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f362])).

fof(f362,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

fof(f591,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f456,f589])).

fof(f456,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f414])).
%------------------------------------------------------------------------------
