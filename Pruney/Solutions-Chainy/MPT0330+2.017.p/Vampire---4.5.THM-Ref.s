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
% DateTime   : Thu Dec  3 12:43:01 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 340 expanded)
%              Number of leaves         :   14 ( 109 expanded)
%              Depth                    :   17
%              Number of atoms          :  133 ( 470 expanded)
%              Number of equality atoms :   24 ( 248 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f574,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f443,f447,f573])).

fof(f573,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f572])).

fof(f572,plain,
    ( $false
    | spl6_2 ),
    inference(resolution,[],[f568,f72])).

fof(f72,plain,(
    ! [X4,X3] : r1_tarski(X3,k3_tarski(k3_enumset1(X4,X4,X4,X4,X3))) ),
    inference(superposition,[],[f40,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f26,f38,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f30,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f25,f38])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f568,plain,
    ( ~ r1_tarski(sK5,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))
    | spl6_2 ),
    inference(resolution,[],[f549,f442])).

fof(f442,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f440])).

fof(f440,plain,
    ( spl6_2
  <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f549,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(X0,X0,X0,X0,sK4)),X1))
      | ~ r1_tarski(sK5,X1) ) ),
    inference(superposition,[],[f531,f41])).

fof(f531,plain,(
    ! [X2,X3] :
      ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,X2)),X3))
      | ~ r1_tarski(sK5,X3) ) ),
    inference(resolution,[],[f515,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f515,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,X3)),sK5),X4)
      | r1_tarski(sK1,X4) ) ),
    inference(superposition,[],[f43,f67])).

fof(f67,plain,(
    ! [X0] : k2_zfmisc_1(k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,X0)),sK5) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,X0)),sK5))) ),
    inference(resolution,[],[f63,f40])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4,X0)
      | k2_zfmisc_1(X0,sK5) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k2_zfmisc_1(X0,sK5))) ) ),
    inference(resolution,[],[f58,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f58,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k2_zfmisc_1(X0,sK5))
      | ~ r1_tarski(sK4,X0) ) ),
    inference(resolution,[],[f54,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),X1)
      | r1_tarski(sK1,X1) ) ),
    inference(superposition,[],[f43,f46])).

fof(f46,plain,(
    k2_zfmisc_1(sK4,sK5) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k2_zfmisc_1(sK4,sK5))) ),
    inference(resolution,[],[f42,f23])).

fof(f23,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f447,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | spl6_1 ),
    inference(resolution,[],[f444,f40])).

fof(f444,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)))
    | spl6_1 ),
    inference(resolution,[],[f438,f381])).

fof(f381,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK0,k2_zfmisc_1(X0,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X1))))
      | ~ r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f366,f31])).

fof(f366,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X3))),X4)
      | r1_tarski(sK0,X4) ) ),
    inference(superposition,[],[f43,f66])).

fof(f66,plain,(
    ! [X0] : k2_zfmisc_1(sK2,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X0))) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k2_zfmisc_1(sK2,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X0))))) ),
    inference(resolution,[],[f62,f40])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK3,X0)
      | k2_zfmisc_1(sK2,X0) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k2_zfmisc_1(sK2,X0))) ) ),
    inference(resolution,[],[f56,f42])).

fof(f56,plain,(
    ! [X1] :
      ( r1_tarski(sK0,k2_zfmisc_1(sK2,X1))
      | ~ r1_tarski(sK3,X1) ) ),
    inference(resolution,[],[f53,f32])).

fof(f53,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0)
      | r1_tarski(sK0,X0) ) ),
    inference(superposition,[],[f43,f45])).

fof(f45,plain,(
    k2_zfmisc_1(sK2,sK3) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k2_zfmisc_1(sK2,sK3))) ),
    inference(resolution,[],[f42,f22])).

fof(f22,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f438,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl6_1
  <=> r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f443,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f180,f440,f436])).

fof(f180,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    inference(resolution,[],[f39,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f39,plain,(
    ~ r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    inference(definition_unfolding,[],[f24,f38,f38,f38])).

fof(f24,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.40  % (26983)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.45  % (26974)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.46  % (26970)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.46  % (26976)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.46  % (26973)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.47  % (26977)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.47  % (26984)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.48  % (26979)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.48  % (26971)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.48  % (26982)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.48  % (26980)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.48  % (26972)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.49  % (26986)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.49  % (26978)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.50  % (26975)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.50  % (26985)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.50  % (26981)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.51  % (26987)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.51  % (26972)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f574,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(avatar_sat_refutation,[],[f443,f447,f573])).
% 0.19/0.51  fof(f573,plain,(
% 0.19/0.51    spl6_2),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f572])).
% 0.19/0.51  fof(f572,plain,(
% 0.19/0.51    $false | spl6_2),
% 0.19/0.51    inference(resolution,[],[f568,f72])).
% 0.19/0.51  fof(f72,plain,(
% 0.19/0.51    ( ! [X4,X3] : (r1_tarski(X3,k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)))) )),
% 0.19/0.51    inference(superposition,[],[f40,f41])).
% 0.19/0.51  fof(f41,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 0.19/0.51    inference(definition_unfolding,[],[f26,f38,f38])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.19/0.51    inference(definition_unfolding,[],[f27,f37])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f28,f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f30,f35])).
% 0.19/0.51  fof(f35,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,axiom,(
% 0.19/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.19/0.51    inference(definition_unfolding,[],[f25,f38])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.19/0.51  fof(f568,plain,(
% 0.19/0.51    ~r1_tarski(sK5,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))) | spl6_2),
% 0.19/0.51    inference(resolution,[],[f549,f442])).
% 0.19/0.51  fof(f442,plain,(
% 0.19/0.51    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) | spl6_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f440])).
% 0.19/0.51  fof(f440,plain,(
% 0.19/0.51    spl6_2 <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.19/0.51  fof(f549,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(X0,X0,X0,X0,sK4)),X1)) | ~r1_tarski(sK5,X1)) )),
% 0.19/0.51    inference(superposition,[],[f531,f41])).
% 0.19/0.51  fof(f531,plain,(
% 0.19/0.51    ( ! [X2,X3] : (r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,X2)),X3)) | ~r1_tarski(sK5,X3)) )),
% 0.19/0.51    inference(resolution,[],[f515,f32])).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.19/0.51  fof(f515,plain,(
% 0.19/0.51    ( ! [X4,X3] : (~r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,X3)),sK5),X4) | r1_tarski(sK1,X4)) )),
% 0.19/0.51    inference(superposition,[],[f43,f67])).
% 0.19/0.51  fof(f67,plain,(
% 0.19/0.51    ( ! [X0] : (k2_zfmisc_1(k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,X0)),sK5) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,X0)),sK5)))) )),
% 0.19/0.51    inference(resolution,[],[f63,f40])).
% 0.19/0.51  fof(f63,plain,(
% 0.19/0.51    ( ! [X0] : (~r1_tarski(sK4,X0) | k2_zfmisc_1(X0,sK5) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k2_zfmisc_1(X0,sK5)))) )),
% 0.19/0.51    inference(resolution,[],[f58,f42])).
% 0.19/0.51  fof(f42,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1) )),
% 0.19/0.51    inference(definition_unfolding,[],[f29,f38])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.51  fof(f58,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tarski(sK1,k2_zfmisc_1(X0,sK5)) | ~r1_tarski(sK4,X0)) )),
% 0.19/0.51    inference(resolution,[],[f54,f31])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f54,plain,(
% 0.19/0.51    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(sK4,sK5),X1) | r1_tarski(sK1,X1)) )),
% 0.19/0.51    inference(superposition,[],[f43,f46])).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    k2_zfmisc_1(sK4,sK5) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k2_zfmisc_1(sK4,sK5)))),
% 0.19/0.51    inference(resolution,[],[f42,f23])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.19/0.51    inference(cnf_transformation,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f14,plain,(
% 0.19/0.51    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 0.19/0.51    inference(flattening,[],[f13])).
% 0.19/0.51  fof(f13,plain,(
% 0.19/0.51    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 0.19/0.51    inference(ennf_transformation,[],[f12])).
% 0.19/0.51  fof(f12,negated_conjecture,(
% 0.19/0.51    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.19/0.51    inference(negated_conjecture,[],[f11])).
% 0.19/0.51  fof(f11,conjecture,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 0.19/0.51  fof(f43,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f33,f38])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.19/0.51    inference(ennf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.19/0.51  fof(f447,plain,(
% 0.19/0.51    spl6_1),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f446])).
% 0.19/0.51  fof(f446,plain,(
% 0.19/0.51    $false | spl6_1),
% 0.19/0.51    inference(resolution,[],[f444,f40])).
% 0.19/0.51  fof(f444,plain,(
% 0.19/0.51    ~r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4))) | spl6_1),
% 0.19/0.51    inference(resolution,[],[f438,f381])).
% 0.19/0.51  fof(f381,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(sK0,k2_zfmisc_1(X0,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X1)))) | ~r1_tarski(sK2,X0)) )),
% 0.19/0.51    inference(resolution,[],[f366,f31])).
% 0.19/0.51  fof(f366,plain,(
% 0.19/0.51    ( ! [X4,X3] : (~r1_tarski(k2_zfmisc_1(sK2,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X3))),X4) | r1_tarski(sK0,X4)) )),
% 0.19/0.51    inference(superposition,[],[f43,f66])).
% 0.19/0.51  fof(f66,plain,(
% 0.19/0.51    ( ! [X0] : (k2_zfmisc_1(sK2,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X0))) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k2_zfmisc_1(sK2,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X0)))))) )),
% 0.19/0.51    inference(resolution,[],[f62,f40])).
% 0.19/0.51  fof(f62,plain,(
% 0.19/0.51    ( ! [X0] : (~r1_tarski(sK3,X0) | k2_zfmisc_1(sK2,X0) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k2_zfmisc_1(sK2,X0)))) )),
% 0.19/0.51    inference(resolution,[],[f56,f42])).
% 0.19/0.51  fof(f56,plain,(
% 0.19/0.51    ( ! [X1] : (r1_tarski(sK0,k2_zfmisc_1(sK2,X1)) | ~r1_tarski(sK3,X1)) )),
% 0.19/0.51    inference(resolution,[],[f53,f32])).
% 0.19/0.51  fof(f53,plain,(
% 0.19/0.51    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),X0) | r1_tarski(sK0,X0)) )),
% 0.19/0.51    inference(superposition,[],[f43,f45])).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    k2_zfmisc_1(sK2,sK3) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k2_zfmisc_1(sK2,sK3)))),
% 0.19/0.51    inference(resolution,[],[f42,f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.19/0.51    inference(cnf_transformation,[],[f21])).
% 0.19/0.51  fof(f438,plain,(
% 0.19/0.51    ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) | spl6_1),
% 0.19/0.51    inference(avatar_component_clause,[],[f436])).
% 0.19/0.51  fof(f436,plain,(
% 0.19/0.51    spl6_1 <=> r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.19/0.51  fof(f443,plain,(
% 0.19/0.51    ~spl6_1 | ~spl6_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f180,f440,f436])).
% 0.19/0.51  fof(f180,plain,(
% 0.19/0.51    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) | ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))),
% 0.19/0.51    inference(resolution,[],[f39,f44])).
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f34,f38])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.19/0.51    inference(flattening,[],[f18])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.19/0.51    inference(ennf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    ~r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))),
% 0.19/0.51    inference(definition_unfolding,[],[f24,f38,f38,f38])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 0.19/0.51    inference(cnf_transformation,[],[f21])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (26972)------------------------------
% 0.19/0.51  % (26972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (26972)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (26972)Memory used [KB]: 6652
% 0.19/0.51  % (26972)Time elapsed: 0.099 s
% 0.19/0.51  % (26972)------------------------------
% 0.19/0.51  % (26972)------------------------------
% 0.19/0.51  % (26969)Success in time 0.164 s
%------------------------------------------------------------------------------
