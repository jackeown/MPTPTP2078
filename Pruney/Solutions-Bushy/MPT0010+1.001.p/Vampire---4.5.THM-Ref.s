%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0010+1.001 : TPTP v7.4.0. Released v7.4.0.
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
% Statistics : Number of formulae       :   16 (  21 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  50 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    $false ),
    inference(global_subsumption,[],[f11,f19])).

fof(f19,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f18,f12])).

fof(f12,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f18,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(resolution,[],[f10,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f8])).

% (12169)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (12151)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% (12161)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f8,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f10,plain,(
    r1_tarski(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,
    ( k1_xboole_0 != sK0
    & r1_tarski(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).

fof(f6,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_tarski(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK0
      & r1_tarski(sK0,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( r1_tarski(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f11,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
