%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:09 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   44 (  92 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 169 expanded)
%              Number of equality atoms :   26 (  74 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f80,f86])).

fof(f86,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f77,f18])).

fof(f18,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f77,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_4
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f80,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f73,f17])).

fof(f17,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f78,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f69,f75,f71])).

fof(f69,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f59,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f59,plain,(
    ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK2),sK1) ),
    inference(trivial_inequality_removal,[],[f56])).

fof(f56,plain,
    ( sK1 != sK1
    | ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK2),sK1) ),
    inference(superposition,[],[f31,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f34,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f23,f30,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f21,f29])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f31,plain,(
    sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK2),k2_enumset1(sK0,sK0,sK0,sK2),k2_enumset1(sK0,sK0,sK0,sK2),sK1)) ),
    inference(definition_unfolding,[],[f19,f30,f29])).

fof(f19,plain,(
    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:13:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.42  % (6306)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.14/0.42  % (6306)Refutation found. Thanks to Tanya!
% 0.14/0.42  % SZS status Theorem for theBenchmark
% 0.14/0.42  % SZS output start Proof for theBenchmark
% 0.14/0.42  fof(f87,plain,(
% 0.14/0.42    $false),
% 0.14/0.42    inference(avatar_sat_refutation,[],[f78,f80,f86])).
% 0.14/0.42  fof(f86,plain,(
% 0.14/0.42    spl3_4),
% 0.14/0.42    inference(avatar_contradiction_clause,[],[f85])).
% 0.14/0.42  fof(f85,plain,(
% 0.14/0.42    $false | spl3_4),
% 0.14/0.42    inference(resolution,[],[f77,f18])).
% 0.14/0.42  fof(f18,plain,(
% 0.14/0.42    r2_hidden(sK2,sK1)),
% 0.14/0.42    inference(cnf_transformation,[],[f14])).
% 0.14/0.42  fof(f14,plain,(
% 0.14/0.42    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 0.14/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 0.14/0.42  fof(f13,plain,(
% 0.14/0.42    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 0.14/0.42    introduced(choice_axiom,[])).
% 0.14/0.42  fof(f11,plain,(
% 0.14/0.42    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 0.14/0.42    inference(flattening,[],[f10])).
% 0.14/0.42  fof(f10,plain,(
% 0.14/0.42    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 0.14/0.42    inference(ennf_transformation,[],[f9])).
% 0.14/0.42  fof(f9,negated_conjecture,(
% 0.14/0.42    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 0.14/0.42    inference(negated_conjecture,[],[f8])).
% 0.14/0.42  fof(f8,conjecture,(
% 0.14/0.42    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 0.14/0.42  fof(f77,plain,(
% 0.14/0.42    ~r2_hidden(sK2,sK1) | spl3_4),
% 0.14/0.42    inference(avatar_component_clause,[],[f75])).
% 0.14/0.42  fof(f75,plain,(
% 0.14/0.42    spl3_4 <=> r2_hidden(sK2,sK1)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.14/0.42  fof(f80,plain,(
% 0.14/0.42    spl3_3),
% 0.14/0.42    inference(avatar_contradiction_clause,[],[f79])).
% 0.14/0.42  fof(f79,plain,(
% 0.14/0.42    $false | spl3_3),
% 0.14/0.42    inference(resolution,[],[f73,f17])).
% 0.14/0.42  fof(f17,plain,(
% 0.14/0.42    r2_hidden(sK0,sK1)),
% 0.14/0.42    inference(cnf_transformation,[],[f14])).
% 0.14/0.42  fof(f73,plain,(
% 0.14/0.42    ~r2_hidden(sK0,sK1) | spl3_3),
% 0.14/0.42    inference(avatar_component_clause,[],[f71])).
% 0.14/0.42  fof(f71,plain,(
% 0.14/0.42    spl3_3 <=> r2_hidden(sK0,sK1)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.14/0.42  fof(f78,plain,(
% 0.14/0.42    ~spl3_3 | ~spl3_4),
% 0.14/0.42    inference(avatar_split_clause,[],[f69,f75,f71])).
% 0.14/0.42  fof(f69,plain,(
% 0.14/0.42    ~r2_hidden(sK2,sK1) | ~r2_hidden(sK0,sK1)),
% 0.14/0.42    inference(resolution,[],[f59,f35])).
% 0.14/0.42  fof(f35,plain,(
% 0.14/0.42    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.14/0.42    inference(definition_unfolding,[],[f28,f29])).
% 0.14/0.42  fof(f29,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.14/0.42    inference(definition_unfolding,[],[f22,f25])).
% 0.14/0.42  fof(f25,plain,(
% 0.14/0.42    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f5])).
% 0.14/0.42  fof(f5,axiom,(
% 0.14/0.42    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.14/0.42  fof(f22,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f4])).
% 0.14/0.42  fof(f4,axiom,(
% 0.14/0.42    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.14/0.42  fof(f28,plain,(
% 0.14/0.42    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f16])).
% 0.14/0.42  fof(f16,plain,(
% 0.14/0.42    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.14/0.42    inference(flattening,[],[f15])).
% 0.14/0.42  fof(f15,plain,(
% 0.14/0.42    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.14/0.42    inference(nnf_transformation,[],[f7])).
% 0.14/0.42  fof(f7,axiom,(
% 0.14/0.42    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.14/0.42  fof(f59,plain,(
% 0.14/0.42    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK2),sK1)),
% 0.14/0.42    inference(trivial_inequality_removal,[],[f56])).
% 0.14/0.42  fof(f56,plain,(
% 0.14/0.42    sK1 != sK1 | ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK2),sK1)),
% 0.14/0.42    inference(superposition,[],[f31,f40])).
% 0.14/0.42  fof(f40,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.14/0.42    inference(backward_demodulation,[],[f34,f33])).
% 0.14/0.42  fof(f33,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 0.14/0.42    inference(definition_unfolding,[],[f23,f30,f30])).
% 0.14/0.42  fof(f30,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.14/0.42    inference(definition_unfolding,[],[f21,f29])).
% 0.14/0.42  fof(f21,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.14/0.42    inference(cnf_transformation,[],[f6])).
% 0.14/0.42  fof(f6,axiom,(
% 0.14/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.14/0.42  fof(f23,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.14/0.42    inference(cnf_transformation,[],[f2])).
% 0.14/0.42  fof(f2,axiom,(
% 0.14/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.14/0.42  fof(f34,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 0.14/0.42    inference(definition_unfolding,[],[f24,f30])).
% 0.14/0.42  fof(f24,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f12])).
% 0.14/0.42  fof(f12,plain,(
% 0.14/0.42    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.14/0.42    inference(ennf_transformation,[],[f3])).
% 0.14/0.42  fof(f3,axiom,(
% 0.14/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.14/0.42  fof(f31,plain,(
% 0.14/0.42    sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK2),k2_enumset1(sK0,sK0,sK0,sK2),k2_enumset1(sK0,sK0,sK0,sK2),sK1))),
% 0.14/0.42    inference(definition_unfolding,[],[f19,f30,f29])).
% 0.14/0.42  fof(f19,plain,(
% 0.14/0.42    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.14/0.42    inference(cnf_transformation,[],[f14])).
% 0.14/0.42  % SZS output end Proof for theBenchmark
% 0.14/0.42  % (6306)------------------------------
% 0.14/0.42  % (6306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.42  % (6306)Termination reason: Refutation
% 0.14/0.42  
% 0.14/0.42  % (6306)Memory used [KB]: 6140
% 0.14/0.42  % (6306)Time elapsed: 0.006 s
% 0.14/0.42  % (6306)------------------------------
% 0.14/0.42  % (6306)------------------------------
% 0.14/0.43  % (6301)Success in time 0.062 s
%------------------------------------------------------------------------------
