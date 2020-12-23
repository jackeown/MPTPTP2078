%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0429+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :   10 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 108 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f862,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f800,f830,f840,f861])).

fof(f861,plain,(
    spl13_6 ),
    inference(avatar_contradiction_clause,[],[f860])).

fof(f860,plain,
    ( $false
    | spl13_6 ),
    inference(subsumption_resolution,[],[f857,f782])).

fof(f782,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f857,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl13_6 ),
    inference(resolution,[],[f784,f839])).

fof(f839,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl13_6 ),
    inference(avatar_component_clause,[],[f838])).

fof(f838,plain,
    ( spl13_6
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f784,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f733])).

fof(f733,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f692])).

fof(f692,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK7(X0,X1),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r1_tarski(sK7(X0,X1),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f690,f691])).

fof(f691,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK7(X0,X1),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( r1_tarski(sK7(X0,X1),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f690,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f689])).

fof(f689,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f840,plain,
    ( ~ spl13_6
    | spl13_5 ),
    inference(avatar_split_clause,[],[f834,f828,f838])).

fof(f828,plain,
    ( spl13_5
  <=> r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f834,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl13_5 ),
    inference(resolution,[],[f740,f829])).

fof(f829,plain,
    ( ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0))
    | spl13_5 ),
    inference(avatar_component_clause,[],[f828])).

fof(f740,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f693])).

fof(f693,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f395])).

fof(f395,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f830,plain,
    ( ~ spl13_5
    | spl13_1 ),
    inference(avatar_split_clause,[],[f824,f798,f828])).

fof(f798,plain,
    ( spl13_1
  <=> m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f824,plain,
    ( ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0))
    | spl13_1 ),
    inference(resolution,[],[f714,f799])).

fof(f799,plain,
    ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f798])).

fof(f714,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f672])).

fof(f672,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f607])).

fof(f607,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f800,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f711,f798])).

fof(f711,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f671])).

fof(f671,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f635,f670])).

fof(f670,plain,
    ( ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))
   => ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(choice_axiom,[])).

fof(f635,plain,(
    ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(ennf_transformation,[],[f630])).

fof(f630,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(negated_conjecture,[],[f629])).

fof(f629,conjecture,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).
%------------------------------------------------------------------------------
