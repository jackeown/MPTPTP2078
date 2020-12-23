%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0280+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:21 EST 2020

% Result     : Theorem 1.16s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :    9 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 (  86 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f963,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f790,f936,f959])).

fof(f959,plain,(
    spl14_1 ),
    inference(avatar_contradiction_clause,[],[f958])).

fof(f958,plain,
    ( $false
    | spl14_1 ),
    inference(subsumption_resolution,[],[f939,f539])).

fof(f539,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f149])).

fof(f149,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f939,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1))
    | spl14_1 ),
    inference(resolution,[],[f785,f550])).

fof(f550,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f397])).

fof(f397,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f375])).

fof(f375,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f785,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
    | spl14_1 ),
    inference(avatar_component_clause,[],[f783])).

fof(f783,plain,
    ( spl14_1
  <=> r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f936,plain,(
    spl14_2 ),
    inference(avatar_contradiction_clause,[],[f935])).

fof(f935,plain,
    ( $false
    | spl14_2 ),
    inference(subsumption_resolution,[],[f917,f710])).

fof(f710,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f533])).

fof(f533,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f450])).

fof(f450,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f449])).

fof(f449,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f917,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl14_2 ),
    inference(resolution,[],[f806,f532])).

fof(f532,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f393])).

fof(f393,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f806,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK0,sK1))
    | spl14_2 ),
    inference(resolution,[],[f789,f550])).

fof(f789,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
    | spl14_2 ),
    inference(avatar_component_clause,[],[f787])).

fof(f787,plain,
    ( spl14_2
  <=> r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f790,plain,
    ( ~ spl14_1
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f754,f787,f783])).

fof(f754,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f523,f528])).

fof(f528,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f388])).

fof(f388,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f387])).

fof(f387,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f161])).

fof(f161,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f523,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f446])).

fof(f446,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f382,f445])).

fof(f445,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f382,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f378])).

fof(f378,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f377])).

fof(f377,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_zfmisc_1)).
%------------------------------------------------------------------------------
