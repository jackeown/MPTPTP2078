%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0285+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   20 (  27 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  54 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f586,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f563,f567,f585])).

fof(f585,plain,
    ( spl12_1
    | ~ spl12_2 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f580,f566])).

fof(f566,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f565])).

fof(f565,plain,
    ( spl12_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f580,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl12_1 ),
    inference(resolution,[],[f486,f562])).

fof(f562,plain,
    ( ~ r1_tarski(sK0,k3_tarski(sK1))
    | spl12_1 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl12_1
  <=> r1_tarski(sK0,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f486,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f401])).

fof(f401,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f308])).

fof(f308,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f567,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f462,f565])).

fof(f462,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f418])).

fof(f418,plain,
    ( ~ r1_tarski(sK0,k3_tarski(sK1))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f386,f417])).

fof(f417,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k3_tarski(X1))
        & r2_hidden(X0,X1) )
   => ( ~ r1_tarski(sK0,k3_tarski(sK1))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f386,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f384])).

fof(f384,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f383])).

fof(f383,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(f563,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f463,f561])).

fof(f463,plain,(
    ~ r1_tarski(sK0,k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f418])).
%------------------------------------------------------------------------------
