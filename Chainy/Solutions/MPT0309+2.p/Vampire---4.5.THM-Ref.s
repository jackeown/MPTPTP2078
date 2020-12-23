%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0309+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:23 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   30 (  40 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  62 expanded)
%              Number of equality atoms :   26 (  38 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f981,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f452,f532,f620,f967])).

fof(f967,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f966])).

fof(f966,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f965,f433])).

fof(f433,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f329])).

fof(f329,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f965,plain,
    ( k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK2,sK3)),k2_zfmisc_1(sK1,k2_xboole_0(sK2,sK3)))
    | spl4_9 ),
    inference(forward_demodulation,[],[f930,f434])).

fof(f434,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f329])).

fof(f930,plain,
    ( k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK2,sK3)),k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3)))
    | spl4_9 ),
    inference(superposition,[],[f619,f501])).

fof(f501,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X2,k2_xboole_0(X3,X4)) = k2_xboole_0(k2_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f443,f445])).

fof(f445,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f443,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f619,plain,
    ( k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK0,k2_xboole_0(sK2,sK3))),k2_zfmisc_1(sK1,sK3))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f618])).

fof(f618,plain,
    ( spl4_9
  <=> k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) = k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK0,k2_xboole_0(sK2,sK3))),k2_zfmisc_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f620,plain,
    ( ~ spl4_9
    | spl4_4 ),
    inference(avatar_split_clause,[],[f601,f530,f618])).

fof(f530,plain,
    ( spl4_4
  <=> k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) = k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3))),k2_zfmisc_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f601,plain,
    ( k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK0,k2_xboole_0(sK2,sK3))),k2_zfmisc_1(sK1,sK3))
    | spl4_4 ),
    inference(backward_demodulation,[],[f531,f434])).

fof(f531,plain,
    ( k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3))),k2_zfmisc_1(sK1,sK3))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f530])).

fof(f532,plain,
    ( ~ spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f528,f450,f530])).

fof(f450,plain,
    ( spl4_1
  <=> k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f528,plain,
    ( k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3))),k2_zfmisc_1(sK1,sK3))
    | spl4_1 ),
    inference(forward_demodulation,[],[f451,f445])).

fof(f451,plain,
    ( k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f450])).

fof(f452,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f427,f450])).

fof(f427,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f424])).

fof(f424,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f414,f423])).

fof(f423,plain,
    ( ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3))
   => k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK3)) ),
    introduced(choice_axiom,[])).

fof(f414,plain,(
    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3)) ),
    inference(ennf_transformation,[],[f331])).

fof(f331,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3)) ),
    inference(negated_conjecture,[],[f330])).

fof(f330,conjecture,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_zfmisc_1)).
%------------------------------------------------------------------------------
