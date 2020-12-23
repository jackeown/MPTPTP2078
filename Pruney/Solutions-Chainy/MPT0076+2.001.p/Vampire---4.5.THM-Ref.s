%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  56 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 125 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f84,f86])).

fof(f86,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | ~ spl2_1 ),
    inference(resolution,[],[f77,f15])).

fof(f15,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( r1_xboole_0(sK1,sK0)
    & r1_tarski(sK1,sK0)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( r1_xboole_0(X1,X0)
        & r1_tarski(X1,X0)
        & ~ v1_xboole_0(X1) )
   => ( r1_xboole_0(sK1,sK0)
      & r1_tarski(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X1,X0)
      & r1_tarski(X1,X0)
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X1,X0)
      & r1_tarski(X1,X0)
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ~ ( r1_xboole_0(X1,X0)
            & r1_tarski(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f77,plain,
    ( v1_xboole_0(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl2_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f84,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl2_2 ),
    inference(resolution,[],[f81,f16])).

fof(f16,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f81,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl2_2
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f82,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f73,f79,f75])).

fof(f73,plain,
    ( ~ r1_tarski(sK1,sK0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f68,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ r1_tarski(X0,sK0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f23,f17])).

fof(f17,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f68,plain,(
    ! [X6] : r1_tarski(X6,X6) ),
    inference(superposition,[],[f25,f55])).

fof(f55,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(superposition,[],[f38,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f38,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2 ),
    inference(superposition,[],[f24,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f18,f19])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:52:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (19700)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.41  % (19700)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f87,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f82,f84,f86])).
% 0.21/0.41  fof(f86,plain,(
% 0.21/0.41    ~spl2_1),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f85])).
% 0.21/0.41  fof(f85,plain,(
% 0.21/0.41    $false | ~spl2_1),
% 0.21/0.41    inference(resolution,[],[f77,f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ~v1_xboole_0(sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    r1_xboole_0(sK1,sK0) & r1_tarski(sK1,sK0) & ~v1_xboole_0(sK1)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ? [X0,X1] : (r1_xboole_0(X1,X0) & r1_tarski(X1,X0) & ~v1_xboole_0(X1)) => (r1_xboole_0(sK1,sK0) & r1_tarski(sK1,sK0) & ~v1_xboole_0(sK1))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ? [X0,X1] : (r1_xboole_0(X1,X0) & r1_tarski(X1,X0) & ~v1_xboole_0(X1))),
% 0.21/0.41    inference(flattening,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ? [X0,X1] : ((r1_xboole_0(X1,X0) & r1_tarski(X1,X0)) & ~v1_xboole_0(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.41    inference(negated_conjecture,[],[f7])).
% 0.21/0.41  fof(f7,conjecture,(
% 0.21/0.41    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.41  fof(f77,plain,(
% 0.21/0.41    v1_xboole_0(sK1) | ~spl2_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f75])).
% 0.21/0.41  fof(f75,plain,(
% 0.21/0.41    spl2_1 <=> v1_xboole_0(sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.41  fof(f84,plain,(
% 0.21/0.41    spl2_2),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f83])).
% 0.21/0.41  fof(f83,plain,(
% 0.21/0.41    $false | spl2_2),
% 0.21/0.41    inference(resolution,[],[f81,f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    r1_tarski(sK1,sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f14])).
% 0.21/0.41  fof(f81,plain,(
% 0.21/0.41    ~r1_tarski(sK1,sK0) | spl2_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f79])).
% 0.21/0.41  fof(f79,plain,(
% 0.21/0.41    spl2_2 <=> r1_tarski(sK1,sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.41  fof(f82,plain,(
% 0.21/0.41    spl2_1 | ~spl2_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f73,f79,f75])).
% 0.21/0.41  fof(f73,plain,(
% 0.21/0.41    ~r1_tarski(sK1,sK0) | v1_xboole_0(sK1)),
% 0.21/0.41    inference(resolution,[],[f68,f37])).
% 0.21/0.41  fof(f37,plain,(
% 0.21/0.41    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(X0,sK0) | v1_xboole_0(X0)) )),
% 0.21/0.41    inference(resolution,[],[f23,f17])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    r1_xboole_0(sK1,sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f14])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2))),
% 0.21/0.41    inference(flattening,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0,X1,X2] : ((~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0)) | v1_xboole_0(X2))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).
% 0.21/0.41  fof(f68,plain,(
% 0.21/0.41    ( ! [X6] : (r1_tarski(X6,X6)) )),
% 0.21/0.41    inference(superposition,[],[f25,f55])).
% 0.21/0.41  fof(f55,plain,(
% 0.21/0.41    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) )),
% 0.21/0.41    inference(superposition,[],[f38,f20])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.41  fof(f38,plain,(
% 0.21/0.41    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) )),
% 0.21/0.41    inference(superposition,[],[f24,f19])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.41    inference(definition_unfolding,[],[f22,f21])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.41    inference(cnf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.21/0.41    inference(superposition,[],[f18,f19])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,axiom,(
% 0.21/0.41    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (19700)------------------------------
% 0.21/0.41  % (19700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (19700)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (19700)Memory used [KB]: 6140
% 0.21/0.41  % (19700)Time elapsed: 0.029 s
% 0.21/0.41  % (19700)------------------------------
% 0.21/0.41  % (19700)------------------------------
% 0.21/0.41  % (19695)Success in time 0.061 s
%------------------------------------------------------------------------------
