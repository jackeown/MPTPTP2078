%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 141 expanded)
%              Number of leaves         :   14 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  128 ( 305 expanded)
%              Number of equality atoms :   11 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f562,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f325,f479,f535,f539,f561])).

fof(f561,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f558])).

fof(f558,plain,
    ( $false
    | spl4_10 ),
    inference(resolution,[],[f557,f21])).

fof(f21,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
    & r1_xboole_0(sK2,sK3)
    & r1_xboole_0(sK1,sK3)
    & r1_xboole_0(sK0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
        & r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
   => ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
      & r1_xboole_0(sK2,sK3)
      & r1_xboole_0(sK1,sK3)
      & r1_xboole_0(sK0,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          & r1_xboole_0(X1,X3)
          & r1_xboole_0(X0,X3) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).

fof(f557,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | spl4_10 ),
    inference(resolution,[],[f534,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f534,plain,
    ( ~ r1_xboole_0(sK3,sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f532])).

fof(f532,plain,
    ( spl4_10
  <=> r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f539,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f536])).

fof(f536,plain,
    ( $false
    | spl4_9 ),
    inference(resolution,[],[f530,f22])).

fof(f22,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f530,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f528])).

fof(f528,plain,
    ( spl4_9
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f535,plain,
    ( ~ spl4_9
    | ~ spl4_10
    | spl4_8 ),
    inference(avatar_split_clause,[],[f526,f476,f532,f528])).

fof(f476,plain,
    ( spl4_8
  <=> r1_xboole_0(k2_xboole_0(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f526,plain,
    ( ~ r1_xboole_0(sK3,sK1)
    | ~ r1_xboole_0(sK2,sK3)
    | spl4_8 ),
    inference(resolution,[],[f478,f434])).

fof(f434,plain,(
    ! [X6,X8,X7] :
      ( r1_xboole_0(k2_xboole_0(X6,X7),X8)
      | ~ r1_xboole_0(X8,X6)
      | ~ r1_xboole_0(X7,X8) ) ),
    inference(resolution,[],[f87,f49])).

fof(f49,plain,(
    ! [X6,X4,X5] :
      ( r1_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X6)
      | ~ r1_xboole_0(X4,X6) ) ),
    inference(superposition,[],[f37,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f25,f26,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k4_xboole_0(X0,X2),X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f31,f24])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f87,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X6)),X4)
      | r1_xboole_0(k2_xboole_0(X5,X6),X4)
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f47,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f26,f26])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f33,f32])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f478,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK2),sK3)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f476])).

fof(f479,plain,
    ( ~ spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f458,f271,f476])).

fof(f271,plain,
    ( spl4_3
  <=> r1_xboole_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f458,plain,
    ( ~ r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(k2_xboole_0(sK1,sK2),sK3) ),
    inference(resolution,[],[f434,f41])).

fof(f41,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK3) ),
    inference(backward_demodulation,[],[f23,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f23,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f325,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | spl4_3 ),
    inference(resolution,[],[f276,f20])).

fof(f20,plain,(
    r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f276,plain,
    ( ~ r1_xboole_0(sK0,sK3)
    | spl4_3 ),
    inference(resolution,[],[f273,f27])).

fof(f273,plain,
    ( ~ r1_xboole_0(sK3,sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:09:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (8716)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (8726)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.45  % (8716)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f562,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f325,f479,f535,f539,f561])).
% 0.21/0.45  fof(f561,plain,(
% 0.21/0.45    spl4_10),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f558])).
% 0.21/0.45  fof(f558,plain,(
% 0.21/0.45    $false | spl4_10),
% 0.21/0.45    inference(resolution,[],[f557,f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    r1_xboole_0(sK1,sK3)),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => (~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3))),
% 0.21/0.45    inference(flattening,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & (r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 0.21/0.45    inference(negated_conjecture,[],[f9])).
% 0.21/0.45  fof(f9,conjecture,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).
% 0.21/0.45  fof(f557,plain,(
% 0.21/0.45    ~r1_xboole_0(sK1,sK3) | spl4_10),
% 0.21/0.45    inference(resolution,[],[f534,f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.45  fof(f534,plain,(
% 0.21/0.45    ~r1_xboole_0(sK3,sK1) | spl4_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f532])).
% 0.21/0.45  fof(f532,plain,(
% 0.21/0.45    spl4_10 <=> r1_xboole_0(sK3,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.45  fof(f539,plain,(
% 0.21/0.45    spl4_9),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f536])).
% 0.21/0.45  fof(f536,plain,(
% 0.21/0.45    $false | spl4_9),
% 0.21/0.45    inference(resolution,[],[f530,f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    r1_xboole_0(sK2,sK3)),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f530,plain,(
% 0.21/0.45    ~r1_xboole_0(sK2,sK3) | spl4_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f528])).
% 0.21/0.45  fof(f528,plain,(
% 0.21/0.45    spl4_9 <=> r1_xboole_0(sK2,sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.45  fof(f535,plain,(
% 0.21/0.45    ~spl4_9 | ~spl4_10 | spl4_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f526,f476,f532,f528])).
% 0.21/0.45  fof(f476,plain,(
% 0.21/0.45    spl4_8 <=> r1_xboole_0(k2_xboole_0(sK1,sK2),sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.45  fof(f526,plain,(
% 0.21/0.45    ~r1_xboole_0(sK3,sK1) | ~r1_xboole_0(sK2,sK3) | spl4_8),
% 0.21/0.45    inference(resolution,[],[f478,f434])).
% 0.21/0.45  fof(f434,plain,(
% 0.21/0.45    ( ! [X6,X8,X7] : (r1_xboole_0(k2_xboole_0(X6,X7),X8) | ~r1_xboole_0(X8,X6) | ~r1_xboole_0(X7,X8)) )),
% 0.21/0.45    inference(resolution,[],[f87,f49])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ( ! [X6,X4,X5] : (r1_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X6) | ~r1_xboole_0(X4,X6)) )),
% 0.21/0.45    inference(superposition,[],[f37,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f25,f26,f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X2),X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(resolution,[],[f31,f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    ( ! [X6,X4,X5] : (~r1_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X6)),X4) | r1_xboole_0(k2_xboole_0(X5,X6),X4) | ~r1_xboole_0(X4,X5)) )),
% 0.21/0.45    inference(superposition,[],[f47,f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f30,f26,f26])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(superposition,[],[f33,f32])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f28,f26])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.21/0.45  fof(f478,plain,(
% 0.21/0.45    ~r1_xboole_0(k2_xboole_0(sK1,sK2),sK3) | spl4_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f476])).
% 0.21/0.45  fof(f479,plain,(
% 0.21/0.45    ~spl4_8 | ~spl4_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f458,f271,f476])).
% 0.21/0.45  fof(f271,plain,(
% 0.21/0.45    spl4_3 <=> r1_xboole_0(sK3,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.45  fof(f458,plain,(
% 0.21/0.45    ~r1_xboole_0(sK3,sK0) | ~r1_xboole_0(k2_xboole_0(sK1,sK2),sK3)),
% 0.21/0.45    inference(resolution,[],[f434,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ~r1_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK3)),
% 0.21/0.45    inference(backward_demodulation,[],[f23,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f325,plain,(
% 0.21/0.45    spl4_3),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f322])).
% 0.21/0.45  fof(f322,plain,(
% 0.21/0.45    $false | spl4_3),
% 0.21/0.45    inference(resolution,[],[f276,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK3)),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f276,plain,(
% 0.21/0.45    ~r1_xboole_0(sK0,sK3) | spl4_3),
% 0.21/0.45    inference(resolution,[],[f273,f27])).
% 0.21/0.45  fof(f273,plain,(
% 0.21/0.45    ~r1_xboole_0(sK3,sK0) | spl4_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f271])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (8716)------------------------------
% 0.21/0.45  % (8716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (8716)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (8716)Memory used [KB]: 6524
% 0.21/0.45  % (8716)Time elapsed: 0.025 s
% 0.21/0.45  % (8716)------------------------------
% 0.21/0.45  % (8716)------------------------------
% 0.21/0.45  % (8707)Success in time 0.09 s
%------------------------------------------------------------------------------
