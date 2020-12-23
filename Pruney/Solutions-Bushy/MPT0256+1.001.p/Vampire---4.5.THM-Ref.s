%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0256+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   23 (  31 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  67 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f15,f20,f24,f27])).

fof(f27,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f26])).

fof(f26,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f25,f19])).

fof(f19,plain,
    ( k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl2_2
  <=> k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f25,plain,
    ( k1_tarski(sK1) != k3_xboole_0(sK0,k1_tarski(sK1))
    | spl2_1
    | ~ spl2_3 ),
    inference(resolution,[],[f23,f14])).

fof(f14,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f12])).

fof(f12,plain,
    ( spl2_1
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f23,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,X0)
        | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( r2_hidden(X1,X0)
        | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f24,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f10,f22])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(f20,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f8,f17])).

fof(f8,plain,(
    k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,
    ( ~ r2_hidden(sK1,sK0)
    & k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f6])).

fof(f6,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) )
   => ( ~ r2_hidden(sK1,sK0)
      & k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
       => r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(f15,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f9,f12])).

fof(f9,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
