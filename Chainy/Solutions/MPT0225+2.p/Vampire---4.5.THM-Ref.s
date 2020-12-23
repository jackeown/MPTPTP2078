%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0225+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:18 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 239 expanded)
%              Number of leaves         :    8 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :   83 ( 485 expanded)
%              Number of equality atoms :   59 ( 411 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1022,plain,(
    $false ),
    inference(global_subsumption,[],[f1018,f1021])).

fof(f1021,plain,(
    r2_hidden(sK17,k2_enumset1(sK17,sK17,sK17,sK17)) ),
    inference(subsumption_resolution,[],[f929,f921])).

fof(f921,plain,(
    k2_enumset1(sK17,sK17,sK17,sK17) = k4_xboole_0(k2_enumset1(sK17,sK17,sK17,sK17),k2_enumset1(sK17,sK17,sK17,sK17)) ),
    inference(forward_demodulation,[],[f920,f919])).

fof(f919,plain,(
    sK17 = sK18 ),
    inference(subsumption_resolution,[],[f917,f819])).

fof(f819,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f575,f580,f580])).

fof(f580,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f267])).

fof(f267,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f575,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f343])).

fof(f343,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f303])).

fof(f303,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f917,plain,
    ( sK17 = sK18
    | ~ r1_xboole_0(k2_enumset1(sK17,sK17,sK17,sK17),k2_enumset1(sK18,sK18,sK18,sK18)) ),
    inference(trivial_inequality_removal,[],[f916])).

fof(f916,plain,
    ( k2_enumset1(sK17,sK17,sK17,sK17) != k2_enumset1(sK17,sK17,sK17,sK17)
    | sK17 = sK18
    | ~ r1_xboole_0(k2_enumset1(sK17,sK17,sK17,sK17),k2_enumset1(sK18,sK18,sK18,sK18)) ),
    inference(superposition,[],[f798,f553])).

fof(f553,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f441])).

fof(f441,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f153])).

fof(f153,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

% (6845)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
fof(f798,plain,
    ( k2_enumset1(sK17,sK17,sK17,sK17) != k4_xboole_0(k2_enumset1(sK17,sK17,sK17,sK17),k2_enumset1(sK18,sK18,sK18,sK18))
    | sK17 = sK18 ),
    inference(definition_unfolding,[],[f528,f580,f580,f580])).

fof(f528,plain,
    ( sK17 = sK18
    | k1_tarski(sK17) != k4_xboole_0(k1_tarski(sK17),k1_tarski(sK18)) ),
    inference(cnf_transformation,[],[f440])).

fof(f440,plain,
    ( ( sK17 = sK18
      | k1_tarski(sK17) != k4_xboole_0(k1_tarski(sK17),k1_tarski(sK18)) )
    & ( sK17 != sK18
      | k1_tarski(sK17) = k4_xboole_0(k1_tarski(sK17),k1_tarski(sK18)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18])],[f438,f439])).

fof(f439,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
        & ( X0 != X1
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) )
   => ( ( sK17 = sK18
        | k1_tarski(sK17) != k4_xboole_0(k1_tarski(sK17),k1_tarski(sK18)) )
      & ( sK17 != sK18
        | k1_tarski(sK17) = k4_xboole_0(k1_tarski(sK17),k1_tarski(sK18)) ) ) ),
    introduced(choice_axiom,[])).

fof(f438,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
      & ( X0 != X1
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f317])).

fof(f317,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f308])).

fof(f308,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f307])).

fof(f307,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f920,plain,(
    k2_enumset1(sK17,sK17,sK17,sK17) = k4_xboole_0(k2_enumset1(sK17,sK17,sK17,sK17),k2_enumset1(sK18,sK18,sK18,sK18)) ),
    inference(global_subsumption,[],[f919,f799])).

fof(f799,plain,
    ( sK17 != sK18
    | k2_enumset1(sK17,sK17,sK17,sK17) = k4_xboole_0(k2_enumset1(sK17,sK17,sK17,sK17),k2_enumset1(sK18,sK18,sK18,sK18)) ),
    inference(definition_unfolding,[],[f527,f580,f580,f580])).

fof(f527,plain,
    ( sK17 != sK18
    | k1_tarski(sK17) = k4_xboole_0(k1_tarski(sK17),k1_tarski(sK18)) ),
    inference(cnf_transformation,[],[f440])).

fof(f929,plain,
    ( k2_enumset1(sK17,sK17,sK17,sK17) != k4_xboole_0(k2_enumset1(sK17,sK17,sK17,sK17),k2_enumset1(sK17,sK17,sK17,sK17))
    | r2_hidden(sK17,k2_enumset1(sK17,sK17,sK17,sK17)) ),
    inference(superposition,[],[f876,f921])).

fof(f876,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(X0,k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)))
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f761,f580,f563,f580])).

fof(f563,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f761,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f401])).

fof(f401,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f294])).

fof(f294,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(f1018,plain,(
    ~ r2_hidden(sK17,k2_enumset1(sK17,sK17,sK17,sK17)) ),
    inference(trivial_inequality_removal,[],[f927])).

fof(f927,plain,
    ( k2_enumset1(sK17,sK17,sK17,sK17) != k2_enumset1(sK17,sK17,sK17,sK17)
    | ~ r2_hidden(sK17,k2_enumset1(sK17,sK17,sK17,sK17)) ),
    inference(superposition,[],[f873,f921])).

fof(f873,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f748,f580,f580])).

fof(f748,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f508])).

fof(f508,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f296])).

fof(f296,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
%------------------------------------------------------------------------------
