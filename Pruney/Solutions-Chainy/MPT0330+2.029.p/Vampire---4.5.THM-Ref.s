%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 203 expanded)
%              Number of leaves         :   16 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  163 ( 385 expanded)
%              Number of equality atoms :   17 ( 100 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f607,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f161,f485,f564,f568,f606])).

fof(f606,plain,(
    spl6_43 ),
    inference(avatar_contradiction_clause,[],[f605])).

fof(f605,plain,
    ( $false
    | spl6_43 ),
    inference(subsumption_resolution,[],[f604,f48])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f604,plain,
    ( ~ r1_tarski(sK5,sK5)
    | spl6_43 ),
    inference(resolution,[],[f563,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f563,plain,
    ( ~ r1_tarski(sK5,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))
    | spl6_43 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl6_43
  <=> r1_tarski(sK5,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f568,plain,(
    spl6_42 ),
    inference(avatar_contradiction_clause,[],[f567])).

fof(f567,plain,
    ( $false
    | spl6_42 ),
    inference(subsumption_resolution,[],[f566,f48])).

fof(f566,plain,
    ( ~ r1_tarski(sK4,sK4)
    | spl6_42 ),
    inference(resolution,[],[f559,f46])).

fof(f559,plain,
    ( ~ r1_tarski(sK4,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)))
    | spl6_42 ),
    inference(avatar_component_clause,[],[f557])).

fof(f557,plain,
    ( spl6_42
  <=> r1_tarski(sK4,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f564,plain,
    ( ~ spl6_42
    | ~ spl6_43
    | spl6_12 ),
    inference(avatar_split_clause,[],[f555,f158,f561,f557])).

fof(f158,plain,
    ( spl6_12
  <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f555,plain,
    ( ~ r1_tarski(sK5,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))
    | ~ r1_tarski(sK4,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)))
    | spl6_12 ),
    inference(resolution,[],[f160,f209])).

fof(f209,plain,(
    ! [X26,X25] :
      ( r1_tarski(sK1,k2_zfmisc_1(X25,X26))
      | ~ r1_tarski(sK5,X26)
      | ~ r1_tarski(sK4,X25) ) ),
    inference(resolution,[],[f124,f175])).

fof(f175,plain,(
    ! [X21] :
      ( r1_tarski(sK1,k2_zfmisc_1(X21,sK5))
      | ~ r1_tarski(sK4,X21) ) ),
    inference(resolution,[],[f100,f26])).

% (9583)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
fof(f26,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

% (9581)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f100,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r1_tarski(X5,k2_zfmisc_1(X3,X6))
      | r1_tarski(X5,k2_zfmisc_1(X4,X6))
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f36,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f124,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r1_tarski(X8,k2_zfmisc_1(X9,X6))
      | r1_tarski(X8,k2_zfmisc_1(X9,X7))
      | ~ r1_tarski(X6,X7) ) ),
    inference(resolution,[],[f37,f38])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f160,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f158])).

fof(f485,plain,(
    spl6_11 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | spl6_11 ),
    inference(subsumption_resolution,[],[f483,f45])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f483,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)))
    | spl6_11 ),
    inference(subsumption_resolution,[],[f475,f45])).

fof(f475,plain,
    ( ~ r1_tarski(sK3,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))
    | ~ r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)))
    | spl6_11 ),
    inference(resolution,[],[f206,f156])).

fof(f156,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_11
  <=> r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f206,plain,(
    ! [X21,X22] :
      ( r1_tarski(sK0,k2_zfmisc_1(X21,X22))
      | ~ r1_tarski(sK3,X22)
      | ~ r1_tarski(sK2,X21) ) ),
    inference(resolution,[],[f124,f174])).

fof(f174,plain,(
    ! [X20] :
      ( r1_tarski(sK0,k2_zfmisc_1(X20,sK3))
      | ~ r1_tarski(sK2,X20) ) ),
    inference(resolution,[],[f100,f25])).

fof(f25,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f161,plain,
    ( ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f152,f158,f154])).

fof(f152,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    inference(resolution,[],[f44,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f44,plain,(
    ~ r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    inference(definition_unfolding,[],[f27,f43,f43,f43])).

fof(f27,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:16:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (9587)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (9567)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (9588)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (9580)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (9571)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (9574)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (9575)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.57  % (9570)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.57  % (9586)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.58  % (9565)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.58  % (9579)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.58  % (9568)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.59  % (9589)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.59  % (9566)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.60  % (9593)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.60  % (9571)Refutation found. Thanks to Tanya!
% 0.21/0.60  % SZS status Theorem for theBenchmark
% 0.21/0.60  % (9569)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.60  % SZS output start Proof for theBenchmark
% 0.21/0.60  fof(f607,plain,(
% 0.21/0.60    $false),
% 0.21/0.60    inference(avatar_sat_refutation,[],[f161,f485,f564,f568,f606])).
% 0.21/0.60  fof(f606,plain,(
% 0.21/0.60    spl6_43),
% 0.21/0.60    inference(avatar_contradiction_clause,[],[f605])).
% 0.21/0.60  fof(f605,plain,(
% 0.21/0.60    $false | spl6_43),
% 0.21/0.60    inference(subsumption_resolution,[],[f604,f48])).
% 0.21/0.60  fof(f48,plain,(
% 0.21/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.60    inference(equality_resolution,[],[f32])).
% 0.21/0.60  fof(f32,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.60    inference(cnf_transformation,[],[f24])).
% 0.21/0.60  fof(f24,plain,(
% 0.21/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.60    inference(flattening,[],[f23])).
% 0.21/0.60  fof(f23,plain,(
% 0.21/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.60    inference(nnf_transformation,[],[f1])).
% 0.21/0.60  fof(f1,axiom,(
% 0.21/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.60  fof(f604,plain,(
% 0.21/0.60    ~r1_tarski(sK5,sK5) | spl6_43),
% 0.21/0.60    inference(resolution,[],[f563,f46])).
% 0.21/0.60  fof(f46,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(definition_unfolding,[],[f35,f43])).
% 0.21/0.60  fof(f43,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.21/0.60    inference(definition_unfolding,[],[f29,f42])).
% 0.21/0.60  fof(f42,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.60    inference(definition_unfolding,[],[f30,f41])).
% 0.21/0.60  fof(f41,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.60    inference(definition_unfolding,[],[f34,f40])).
% 0.21/0.60  fof(f40,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f8])).
% 0.21/0.60  fof(f8,axiom,(
% 0.21/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.60  fof(f34,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f7])).
% 0.21/0.60  fof(f7,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.60  fof(f30,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f6])).
% 0.21/0.60  fof(f6,axiom,(
% 0.21/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f9])).
% 0.21/0.60  fof(f9,axiom,(
% 0.21/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.60  fof(f35,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f15])).
% 0.21/0.60  fof(f15,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f2])).
% 0.21/0.60  fof(f2,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.60  fof(f563,plain,(
% 0.21/0.60    ~r1_tarski(sK5,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))) | spl6_43),
% 0.21/0.60    inference(avatar_component_clause,[],[f561])).
% 0.21/0.60  fof(f561,plain,(
% 0.21/0.60    spl6_43 <=> r1_tarski(sK5,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.21/0.60  fof(f568,plain,(
% 0.21/0.60    spl6_42),
% 0.21/0.60    inference(avatar_contradiction_clause,[],[f567])).
% 0.21/0.60  fof(f567,plain,(
% 0.21/0.60    $false | spl6_42),
% 0.21/0.60    inference(subsumption_resolution,[],[f566,f48])).
% 0.21/0.60  fof(f566,plain,(
% 0.21/0.60    ~r1_tarski(sK4,sK4) | spl6_42),
% 0.21/0.60    inference(resolution,[],[f559,f46])).
% 0.21/0.60  fof(f559,plain,(
% 0.21/0.60    ~r1_tarski(sK4,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4))) | spl6_42),
% 0.21/0.60    inference(avatar_component_clause,[],[f557])).
% 0.21/0.60  fof(f557,plain,(
% 0.21/0.60    spl6_42 <=> r1_tarski(sK4,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.21/0.60  fof(f564,plain,(
% 0.21/0.60    ~spl6_42 | ~spl6_43 | spl6_12),
% 0.21/0.60    inference(avatar_split_clause,[],[f555,f158,f561,f557])).
% 0.21/0.60  fof(f158,plain,(
% 0.21/0.60    spl6_12 <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.60  fof(f555,plain,(
% 0.21/0.60    ~r1_tarski(sK5,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))) | ~r1_tarski(sK4,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4))) | spl6_12),
% 0.21/0.60    inference(resolution,[],[f160,f209])).
% 0.21/0.60  fof(f209,plain,(
% 0.21/0.60    ( ! [X26,X25] : (r1_tarski(sK1,k2_zfmisc_1(X25,X26)) | ~r1_tarski(sK5,X26) | ~r1_tarski(sK4,X25)) )),
% 0.21/0.60    inference(resolution,[],[f124,f175])).
% 0.21/0.60  fof(f175,plain,(
% 0.21/0.60    ( ! [X21] : (r1_tarski(sK1,k2_zfmisc_1(X21,sK5)) | ~r1_tarski(sK4,X21)) )),
% 0.21/0.60    inference(resolution,[],[f100,f26])).
% 0.21/0.60  % (9583)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.60  fof(f26,plain,(
% 0.21/0.60    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.21/0.60    inference(cnf_transformation,[],[f22])).
% 0.21/0.60  fof(f22,plain,(
% 0.21/0.60    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f21])).
% 0.21/0.60  fof(f21,plain,(
% 0.21/0.60    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  % (9581)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.60  fof(f14,plain,(
% 0.21/0.60    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 0.21/0.60    inference(flattening,[],[f13])).
% 0.21/0.60  fof(f13,plain,(
% 0.21/0.60    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 0.21/0.60    inference(ennf_transformation,[],[f12])).
% 0.21/0.60  fof(f12,negated_conjecture,(
% 0.21/0.60    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.21/0.60    inference(negated_conjecture,[],[f11])).
% 0.21/0.60  fof(f11,conjecture,(
% 0.21/0.60    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 0.21/0.60  fof(f100,plain,(
% 0.21/0.60    ( ! [X6,X4,X5,X3] : (~r1_tarski(X5,k2_zfmisc_1(X3,X6)) | r1_tarski(X5,k2_zfmisc_1(X4,X6)) | ~r1_tarski(X3,X4)) )),
% 0.21/0.60    inference(resolution,[],[f36,f38])).
% 0.21/0.60  fof(f38,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f18])).
% 0.21/0.60  fof(f18,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.60    inference(flattening,[],[f17])).
% 0.21/0.60  fof(f17,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.60    inference(ennf_transformation,[],[f3])).
% 0.21/0.60  fof(f3,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.60  fof(f36,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f16])).
% 0.21/0.60  fof(f16,plain,(
% 0.21/0.60    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f10])).
% 0.21/0.60  fof(f10,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.21/0.60  fof(f124,plain,(
% 0.21/0.60    ( ! [X6,X8,X7,X9] : (~r1_tarski(X8,k2_zfmisc_1(X9,X6)) | r1_tarski(X8,k2_zfmisc_1(X9,X7)) | ~r1_tarski(X6,X7)) )),
% 0.21/0.60    inference(resolution,[],[f37,f38])).
% 0.21/0.60  fof(f37,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f16])).
% 0.21/0.60  fof(f160,plain,(
% 0.21/0.60    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) | spl6_12),
% 0.21/0.60    inference(avatar_component_clause,[],[f158])).
% 0.21/0.60  fof(f485,plain,(
% 0.21/0.60    spl6_11),
% 0.21/0.60    inference(avatar_contradiction_clause,[],[f484])).
% 0.21/0.60  fof(f484,plain,(
% 0.21/0.60    $false | spl6_11),
% 0.21/0.60    inference(subsumption_resolution,[],[f483,f45])).
% 0.21/0.60  fof(f45,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.21/0.60    inference(definition_unfolding,[],[f28,f43])).
% 0.21/0.60  fof(f28,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f4])).
% 0.21/0.60  fof(f4,axiom,(
% 0.21/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.60  fof(f483,plain,(
% 0.21/0.60    ~r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4))) | spl6_11),
% 0.21/0.60    inference(subsumption_resolution,[],[f475,f45])).
% 0.21/0.60  fof(f475,plain,(
% 0.21/0.60    ~r1_tarski(sK3,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))) | ~r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4))) | spl6_11),
% 0.21/0.60    inference(resolution,[],[f206,f156])).
% 0.21/0.60  fof(f156,plain,(
% 0.21/0.60    ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) | spl6_11),
% 0.21/0.60    inference(avatar_component_clause,[],[f154])).
% 0.21/0.60  fof(f154,plain,(
% 0.21/0.60    spl6_11 <=> r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.60  fof(f206,plain,(
% 0.21/0.60    ( ! [X21,X22] : (r1_tarski(sK0,k2_zfmisc_1(X21,X22)) | ~r1_tarski(sK3,X22) | ~r1_tarski(sK2,X21)) )),
% 0.21/0.60    inference(resolution,[],[f124,f174])).
% 0.21/0.61  fof(f174,plain,(
% 0.21/0.61    ( ! [X20] : (r1_tarski(sK0,k2_zfmisc_1(X20,sK3)) | ~r1_tarski(sK2,X20)) )),
% 0.21/0.61    inference(resolution,[],[f100,f25])).
% 0.21/0.61  fof(f25,plain,(
% 0.21/0.61    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.21/0.61    inference(cnf_transformation,[],[f22])).
% 0.21/0.61  fof(f161,plain,(
% 0.21/0.61    ~spl6_11 | ~spl6_12),
% 0.21/0.61    inference(avatar_split_clause,[],[f152,f158,f154])).
% 0.21/0.61  fof(f152,plain,(
% 0.21/0.61    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) | ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))),
% 0.21/0.61    inference(resolution,[],[f44,f47])).
% 0.21/0.61  fof(f47,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.61    inference(definition_unfolding,[],[f39,f43])).
% 0.21/0.61  fof(f39,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f20])).
% 0.21/0.61  fof(f20,plain,(
% 0.21/0.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.61    inference(flattening,[],[f19])).
% 0.21/0.61  fof(f19,plain,(
% 0.21/0.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.61    inference(ennf_transformation,[],[f5])).
% 0.21/0.61  fof(f5,axiom,(
% 0.21/0.61    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.61  fof(f44,plain,(
% 0.21/0.61    ~r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))),
% 0.21/0.61    inference(definition_unfolding,[],[f27,f43,f43,f43])).
% 0.21/0.61  fof(f27,plain,(
% 0.21/0.61    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 0.21/0.61    inference(cnf_transformation,[],[f22])).
% 0.21/0.61  % SZS output end Proof for theBenchmark
% 0.21/0.61  % (9571)------------------------------
% 0.21/0.61  % (9571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (9571)Termination reason: Refutation
% 0.21/0.61  
% 0.21/0.61  % (9571)Memory used [KB]: 11129
% 0.21/0.61  % (9571)Time elapsed: 0.163 s
% 0.21/0.61  % (9571)------------------------------
% 0.21/0.61  % (9571)------------------------------
% 1.74/0.61  % (9564)Success in time 0.245 s
%------------------------------------------------------------------------------
