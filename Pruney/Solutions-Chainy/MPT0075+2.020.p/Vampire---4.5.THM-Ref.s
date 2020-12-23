%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 106 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  168 ( 280 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f259,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f73,f93,f117,f250,f257,f258])).

fof(f258,plain,
    ( k1_xboole_0 != sK2
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f257,plain,
    ( spl5_30
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f251,f248,f254])).

fof(f254,plain,
    ( spl5_30
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f248,plain,
    ( spl5_29
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f251,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f249,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f249,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f248])).

fof(f250,plain,
    ( spl5_29
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f242,f114,f90,f248])).

fof(f90,plain,
    ( spl5_8
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f114,plain,
    ( spl5_11
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f242,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f241,f31])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f241,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k1_xboole_0))
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f235,f92])).

fof(f92,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f235,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f116,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f116,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f117,plain,
    ( spl5_11
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f102,f70,f58,f114])).

fof(f58,plain,
    ( spl5_4
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f70,plain,
    ( spl5_6
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f102,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f60,f72,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f72,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f60,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f93,plain,
    ( spl5_8
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f82,f53,f90])).

fof(f53,plain,
    ( spl5_3
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f82,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f55,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f55,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f73,plain,
    ( spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f67,f63,f70])).

fof(f63,plain,
    ( spl5_5
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f67,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f65,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f65,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f66,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( r1_xboole_0(sK0,sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK2,sK0)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X2,X0)
        & ~ v1_xboole_0(X2) )
   => ( r1_xboole_0(sK0,sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK2,sK0)
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ~ ( r1_xboole_0(X0,X1)
            & r1_tarski(X2,X1)
            & r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f61,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f27,f53])).

fof(f27,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f30,f48])).

fof(f48,plain,
    ( spl5_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f46,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f26,f43])).

fof(f43,plain,
    ( spl5_1
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f26,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (20338)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.42  % (20338)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f259,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f73,f93,f117,f250,f257,f258])).
% 0.21/0.42  fof(f258,plain,(
% 0.21/0.42    k1_xboole_0 != sK2 | v1_xboole_0(sK2) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.42  fof(f257,plain,(
% 0.21/0.42    spl5_30 | ~spl5_29),
% 0.21/0.42    inference(avatar_split_clause,[],[f251,f248,f254])).
% 0.21/0.42  fof(f254,plain,(
% 0.21/0.42    spl5_30 <=> k1_xboole_0 = sK2),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.42  fof(f248,plain,(
% 0.21/0.42    spl5_29 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.42  fof(f251,plain,(
% 0.21/0.42    k1_xboole_0 = sK2 | ~spl5_29),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f249,f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.42  fof(f249,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl5_29),
% 0.21/0.42    inference(avatar_component_clause,[],[f248])).
% 0.21/0.42  fof(f250,plain,(
% 0.21/0.42    spl5_29 | ~spl5_8 | ~spl5_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f242,f114,f90,f248])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    spl5_8 <=> k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    spl5_11 <=> r1_xboole_0(sK2,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.42  fof(f242,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | (~spl5_8 | ~spl5_11)),
% 0.21/0.42    inference(forward_demodulation,[],[f241,f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.42  fof(f241,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k1_xboole_0))) ) | (~spl5_8 | ~spl5_11)),
% 0.21/0.42    inference(forward_demodulation,[],[f235,f92])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    k1_xboole_0 = k4_xboole_0(sK2,sK0) | ~spl5_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f90])).
% 0.21/0.42  fof(f235,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))) ) | ~spl5_11),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f116,f40])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(definition_unfolding,[],[f35,f33])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(rectify,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.42  fof(f116,plain,(
% 0.21/0.42    r1_xboole_0(sK2,sK0) | ~spl5_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f114])).
% 0.21/0.42  fof(f117,plain,(
% 0.21/0.42    spl5_11 | ~spl5_4 | ~spl5_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f102,f70,f58,f114])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl5_4 <=> r1_tarski(sK2,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    spl5_6 <=> r1_xboole_0(sK1,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    r1_xboole_0(sK2,sK0) | (~spl5_4 | ~spl5_6)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f60,f72,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(flattening,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    r1_xboole_0(sK1,sK0) | ~spl5_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f70])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    r1_tarski(sK2,sK1) | ~spl5_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f58])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    spl5_8 | ~spl5_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f82,f53,f90])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    spl5_3 <=> r1_tarski(sK2,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    k1_xboole_0 = k4_xboole_0(sK2,sK0) | ~spl5_3),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f55,f38])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.42    inference(nnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    r1_tarski(sK2,sK0) | ~spl5_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f53])).
% 0.21/0.42  fof(f73,plain,(
% 0.21/0.42    spl5_6 | ~spl5_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f67,f63,f70])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl5_5 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    r1_xboole_0(sK1,sK0) | ~spl5_5),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f65,f36])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK1) | ~spl5_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f63])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl5_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f29,f63])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK2,sK0) & ~v1_xboole_0(sK2)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2)) => (r1_xboole_0(sK0,sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK2,sK0) & ~v1_xboole_0(sK2))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2))),
% 0.21/0.42    inference(flattening,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ? [X0,X1,X2] : ((r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)) & ~v1_xboole_0(X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.21/0.42    inference(negated_conjecture,[],[f9])).
% 0.21/0.42  fof(f9,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    spl5_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f28,f58])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    r1_tarski(sK2,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f20])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl5_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f27,f53])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    r1_tarski(sK2,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f20])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl5_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f30,f48])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    spl5_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ~spl5_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f26,f43])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    spl5_1 <=> v1_xboole_0(sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ~v1_xboole_0(sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f20])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (20338)------------------------------
% 0.21/0.42  % (20338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (20338)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (20338)Memory used [KB]: 10746
% 0.21/0.42  % (20338)Time elapsed: 0.032 s
% 0.21/0.42  % (20338)------------------------------
% 0.21/0.42  % (20338)------------------------------
% 0.21/0.42  % (20320)Success in time 0.074 s
%------------------------------------------------------------------------------
