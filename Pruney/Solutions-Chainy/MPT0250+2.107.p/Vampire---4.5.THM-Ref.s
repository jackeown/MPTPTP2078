%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 174 expanded)
%              Number of leaves         :   18 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 242 expanded)
%              Number of equality atoms :   26 ( 123 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f66,f79,f85,f89])).

fof(f89,plain,
    ( spl2_1
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl2_1
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f86,f53])).

fof(f53,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f86,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(resolution,[],[f84,f65])).

fof(f65,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
        | r2_hidden(X0,X2) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl2_4
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,X2)
        | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f84,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_8
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f85,plain,
    ( spl2_8
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f80,f76,f56,f82])).

fof(f56,plain,
    ( spl2_2
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2)
        | r1_tarski(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f76,plain,
    ( spl2_7
  <=> r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f80,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(resolution,[],[f78,f57])).

fof(f57,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2)
        | r1_tarski(X0,X2) )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f78,plain,
    ( r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f79,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f48,f76])).

fof(f48,plain,(
    r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(backward_demodulation,[],[f42,f43])).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f23,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f26,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f32,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f42,plain,(
    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) ),
    inference(definition_unfolding,[],[f20,f40,f41])).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f39])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f66,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f47,f64])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f28,f39])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f58,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f49,f56])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(forward_demodulation,[],[f44,f43])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f27,f40])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f54,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:00:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.41  % (24312)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.41  % (24312)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f92,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f54,f58,f66,f79,f85,f89])).
% 0.20/0.41  fof(f89,plain,(
% 0.20/0.41    spl2_1 | ~spl2_4 | ~spl2_8),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f88])).
% 0.20/0.41  fof(f88,plain,(
% 0.20/0.41    $false | (spl2_1 | ~spl2_4 | ~spl2_8)),
% 0.20/0.41    inference(subsumption_resolution,[],[f86,f53])).
% 0.20/0.41  fof(f53,plain,(
% 0.20/0.41    ~r2_hidden(sK0,sK1) | spl2_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f51])).
% 0.20/0.41  fof(f51,plain,(
% 0.20/0.41    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.41  fof(f86,plain,(
% 0.20/0.41    r2_hidden(sK0,sK1) | (~spl2_4 | ~spl2_8)),
% 0.20/0.41    inference(resolution,[],[f84,f65])).
% 0.20/0.41  fof(f65,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) ) | ~spl2_4),
% 0.20/0.41    inference(avatar_component_clause,[],[f64])).
% 0.20/0.41  fof(f64,plain,(
% 0.20/0.41    spl2_4 <=> ! [X1,X0,X2] : (r2_hidden(X0,X2) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.41  fof(f84,plain,(
% 0.20/0.41    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | ~spl2_8),
% 0.20/0.41    inference(avatar_component_clause,[],[f82])).
% 0.20/0.41  fof(f82,plain,(
% 0.20/0.41    spl2_8 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.41  fof(f85,plain,(
% 0.20/0.41    spl2_8 | ~spl2_2 | ~spl2_7),
% 0.20/0.41    inference(avatar_split_clause,[],[f80,f76,f56,f82])).
% 0.20/0.41  fof(f56,plain,(
% 0.20/0.41    spl2_2 <=> ! [X1,X0,X2] : (~r1_tarski(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) | r1_tarski(X0,X2))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.41  fof(f76,plain,(
% 0.20/0.41    spl2_7 <=> r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.41  fof(f80,plain,(
% 0.20/0.41    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | (~spl2_2 | ~spl2_7)),
% 0.20/0.41    inference(resolution,[],[f78,f57])).
% 0.20/0.41  fof(f57,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~r1_tarski(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) | r1_tarski(X0,X2)) ) | ~spl2_2),
% 0.20/0.41    inference(avatar_component_clause,[],[f56])).
% 0.20/0.41  fof(f78,plain,(
% 0.20/0.41    r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | ~spl2_7),
% 0.20/0.41    inference(avatar_component_clause,[],[f76])).
% 0.20/0.41  fof(f79,plain,(
% 0.20/0.41    spl2_7),
% 0.20/0.41    inference(avatar_split_clause,[],[f48,f76])).
% 0.20/0.41  fof(f48,plain,(
% 0.20/0.41    r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 0.20/0.41    inference(backward_demodulation,[],[f42,f43])).
% 0.20/0.41  fof(f43,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.41    inference(definition_unfolding,[],[f25,f40])).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.41    inference(definition_unfolding,[],[f23,f39])).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f24,f38])).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f26,f37])).
% 0.20/0.41  fof(f37,plain,(
% 0.20/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f31,f36])).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f32,f35])).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f33,f34])).
% 0.20/0.41  fof(f34,plain,(
% 0.20/0.41    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f9])).
% 0.20/0.41  fof(f9,axiom,(
% 0.20/0.41    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f8])).
% 0.20/0.41  fof(f8,axiom,(
% 0.20/0.41    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f7])).
% 0.20/0.41  fof(f7,axiom,(
% 0.20/0.41    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.41  fof(f31,plain,(
% 0.20/0.41    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,axiom,(
% 0.20/0.41    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.41  fof(f24,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,axiom,(
% 0.20/0.41    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.41  fof(f42,plain,(
% 0.20/0.41    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1)),
% 0.20/0.41    inference(definition_unfolding,[],[f20,f40,f41])).
% 0.20/0.41  fof(f41,plain,(
% 0.20/0.41    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f22,f39])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.20/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f13])).
% 0.20/0.41  fof(f13,negated_conjecture,(
% 0.20/0.41    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.20/0.41    inference(negated_conjecture,[],[f12])).
% 0.20/0.41  fof(f12,conjecture,(
% 0.20/0.41    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 0.20/0.41  fof(f66,plain,(
% 0.20/0.41    spl2_4),
% 0.20/0.41    inference(avatar_split_clause,[],[f47,f64])).
% 0.20/0.41  fof(f47,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f28,f39])).
% 0.20/0.41  fof(f28,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f19])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.41    inference(flattening,[],[f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.41    inference(nnf_transformation,[],[f11])).
% 0.20/0.41  fof(f11,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.41  fof(f58,plain,(
% 0.20/0.41    spl2_2),
% 0.20/0.41    inference(avatar_split_clause,[],[f49,f56])).
% 0.20/0.41  fof(f49,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~r1_tarski(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) | r1_tarski(X0,X2)) )),
% 0.20/0.41    inference(forward_demodulation,[],[f44,f43])).
% 0.20/0.41  fof(f44,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f27,f40])).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.41  fof(f54,plain,(
% 0.20/0.41    ~spl2_1),
% 0.20/0.41    inference(avatar_split_clause,[],[f21,f51])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    ~r2_hidden(sK0,sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (24312)------------------------------
% 0.20/0.41  % (24312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (24312)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (24312)Memory used [KB]: 6140
% 0.20/0.41  % (24312)Time elapsed: 0.006 s
% 0.20/0.41  % (24312)------------------------------
% 0.20/0.41  % (24312)------------------------------
% 0.20/0.41  % (24304)Success in time 0.068 s
%------------------------------------------------------------------------------
