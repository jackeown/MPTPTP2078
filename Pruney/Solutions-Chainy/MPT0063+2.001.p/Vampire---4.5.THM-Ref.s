%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 133 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :    7
%              Number of atoms          :  176 ( 326 expanded)
%              Number of equality atoms :   41 (  77 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f40,f44,f50,f70,f74,f80,f102,f126,f160,f180,f187,f188])).

fof(f188,plain,
    ( sK0 != sK2
    | r2_xboole_0(sK2,sK1)
    | ~ r2_xboole_0(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f187,plain,
    ( spl3_1
    | spl3_19
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f181,f178,f185,f34])).

fof(f34,plain,
    ( spl3_1
  <=> r2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f185,plain,
    ( spl3_19
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f178,plain,
    ( spl3_18
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f181,plain,
    ( sK0 = sK2
    | r2_xboole_0(sK0,sK2)
    | ~ spl3_18 ),
    inference(resolution,[],[f179,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f179,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f178])).

fof(f180,plain,
    ( spl3_18
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f170,f158,f178])).

fof(f158,plain,
    ( spl3_14
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f170,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_14 ),
    inference(trivial_inequality_removal,[],[f169])).

fof(f169,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK2)
    | ~ spl3_14 ),
    inference(superposition,[],[f29,f159])).

fof(f159,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f158])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f160,plain,
    ( spl3_14
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f153,f121,f78,f158])).

fof(f78,plain,
    ( spl3_8
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f121,plain,
    ( spl3_13
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f153,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(resolution,[],[f149,f79])).

fof(f79,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f149,plain,
    ( ! [X13] :
        ( ~ r1_tarski(sK1,X13)
        | k1_xboole_0 = k4_xboole_0(sK0,X13) )
    | ~ spl3_13 ),
    inference(superposition,[],[f64,f122])).

fof(f122,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | k1_xboole_0 = k4_xboole_0(X0,X2) ) ),
    inference(resolution,[],[f31,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f126,plain,
    ( spl3_13
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f119,f100,f121])).

fof(f100,plain,
    ( spl3_11
  <=> sK1 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f119,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f23,f101])).

fof(f101,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f100])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f102,plain,
    ( spl3_11
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f98,f72,f100])).

fof(f72,plain,
    ( spl3_7
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f98,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f90,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f90,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_7 ),
    inference(superposition,[],[f24,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f80,plain,
    ( spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f76,f68,f78])).

fof(f68,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f76,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_6 ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK2)
    | ~ spl3_6 ),
    inference(superposition,[],[f29,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f74,plain,
    ( spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f66,f42,f72])).

fof(f42,plain,
    ( spl3_3
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f66,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f63,f43])).

fof(f43,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f30,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f65,f38,f68])).

fof(f38,plain,
    ( spl3_2
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f65,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f63,f39])).

fof(f39,plain,
    ( r2_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f50,plain,
    ( ~ spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f45,f38,f48])).

fof(f48,plain,
    ( spl3_4
  <=> r2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f45,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f25,f39])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f44,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f42])).

fof(f19,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r2_xboole_0(sK1,sK2)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r2_xboole_0(X1,X2)
        & r2_xboole_0(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r2_xboole_0(sK1,sK2)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_xboole_0(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_xboole_1)).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f38])).

fof(f20,plain,(
    r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f34])).

fof(f21,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:03:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (2381)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.44  % (2381)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f189,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f36,f40,f44,f50,f70,f74,f80,f102,f126,f160,f180,f187,f188])).
% 0.22/0.44  fof(f188,plain,(
% 0.22/0.44    sK0 != sK2 | r2_xboole_0(sK2,sK1) | ~r2_xboole_0(sK0,sK1)),
% 0.22/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.44  fof(f187,plain,(
% 0.22/0.44    spl3_1 | spl3_19 | ~spl3_18),
% 0.22/0.44    inference(avatar_split_clause,[],[f181,f178,f185,f34])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    spl3_1 <=> r2_xboole_0(sK0,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f185,plain,(
% 0.22/0.44    spl3_19 <=> sK0 = sK2),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.44  fof(f178,plain,(
% 0.22/0.44    spl3_18 <=> r1_tarski(sK0,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.44  fof(f181,plain,(
% 0.22/0.44    sK0 = sK2 | r2_xboole_0(sK0,sK2) | ~spl3_18),
% 0.22/0.44    inference(resolution,[],[f179,f28])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.44    inference(flattening,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.44    inference(nnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.44  fof(f179,plain,(
% 0.22/0.44    r1_tarski(sK0,sK2) | ~spl3_18),
% 0.22/0.44    inference(avatar_component_clause,[],[f178])).
% 0.22/0.44  fof(f180,plain,(
% 0.22/0.44    spl3_18 | ~spl3_14),
% 0.22/0.44    inference(avatar_split_clause,[],[f170,f158,f178])).
% 0.22/0.44  fof(f158,plain,(
% 0.22/0.44    spl3_14 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.44  fof(f170,plain,(
% 0.22/0.44    r1_tarski(sK0,sK2) | ~spl3_14),
% 0.22/0.44    inference(trivial_inequality_removal,[],[f169])).
% 0.22/0.44  fof(f169,plain,(
% 0.22/0.44    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK2) | ~spl3_14),
% 0.22/0.44    inference(superposition,[],[f29,f159])).
% 0.22/0.44  fof(f159,plain,(
% 0.22/0.44    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl3_14),
% 0.22/0.44    inference(avatar_component_clause,[],[f158])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.44    inference(nnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.44  fof(f160,plain,(
% 0.22/0.44    spl3_14 | ~spl3_8 | ~spl3_13),
% 0.22/0.44    inference(avatar_split_clause,[],[f153,f121,f78,f158])).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    spl3_8 <=> r1_tarski(sK1,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.44  fof(f121,plain,(
% 0.22/0.44    spl3_13 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.44  fof(f153,plain,(
% 0.22/0.44    k1_xboole_0 = k4_xboole_0(sK0,sK2) | (~spl3_8 | ~spl3_13)),
% 0.22/0.44    inference(resolution,[],[f149,f79])).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    r1_tarski(sK1,sK2) | ~spl3_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f78])).
% 0.22/0.44  fof(f149,plain,(
% 0.22/0.44    ( ! [X13] : (~r1_tarski(sK1,X13) | k1_xboole_0 = k4_xboole_0(sK0,X13)) ) | ~spl3_13),
% 0.22/0.44    inference(superposition,[],[f64,f122])).
% 0.22/0.44  fof(f122,plain,(
% 0.22/0.44    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_13),
% 0.22/0.44    inference(avatar_component_clause,[],[f121])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | k1_xboole_0 = k4_xboole_0(X0,X2)) )),
% 0.22/0.44    inference(resolution,[],[f31,f30])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.44  fof(f126,plain,(
% 0.22/0.44    spl3_13 | ~spl3_11),
% 0.22/0.44    inference(avatar_split_clause,[],[f119,f100,f121])).
% 0.22/0.44  fof(f100,plain,(
% 0.22/0.44    spl3_11 <=> sK1 = k2_xboole_0(sK1,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.44  fof(f119,plain,(
% 0.22/0.44    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_11),
% 0.22/0.44    inference(superposition,[],[f23,f101])).
% 0.22/0.44  fof(f101,plain,(
% 0.22/0.44    sK1 = k2_xboole_0(sK1,sK0) | ~spl3_11),
% 0.22/0.44    inference(avatar_component_clause,[],[f100])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.44  fof(f102,plain,(
% 0.22/0.44    spl3_11 | ~spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f98,f72,f100])).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    spl3_7 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.44  fof(f98,plain,(
% 0.22/0.44    sK1 = k2_xboole_0(sK1,sK0) | ~spl3_7),
% 0.22/0.44    inference(forward_demodulation,[],[f90,f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.44  fof(f90,plain,(
% 0.22/0.44    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) | ~spl3_7),
% 0.22/0.44    inference(superposition,[],[f24,f73])).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f72])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    spl3_8 | ~spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f76,f68,f78])).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    r1_tarski(sK1,sK2) | ~spl3_6),
% 0.22/0.44    inference(trivial_inequality_removal,[],[f75])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK2) | ~spl3_6),
% 0.22/0.44    inference(superposition,[],[f29,f69])).
% 0.22/0.44  fof(f69,plain,(
% 0.22/0.44    k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~spl3_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f68])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    spl3_7 | ~spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f66,f42,f72])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    spl3_3 <=> r2_xboole_0(sK0,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.44    inference(resolution,[],[f63,f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    r2_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f42])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.44    inference(resolution,[],[f30,f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    spl3_6 | ~spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f65,f38,f68])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    spl3_2 <=> r2_xboole_0(sK1,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~spl3_2),
% 0.22/0.44    inference(resolution,[],[f63,f39])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    r2_xboole_0(sK1,sK2) | ~spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f38])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    ~spl3_4 | ~spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f45,f38,f48])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    spl3_4 <=> r2_xboole_0(sK2,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    ~r2_xboole_0(sK2,sK1) | ~spl3_2),
% 0.22/0.44    inference(resolution,[],[f25,f39])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f19,f42])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    r2_xboole_0(sK0,sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r2_xboole_0(sK0,sK1)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)) => (~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r2_xboole_0(sK0,sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1))),
% 0.22/0.44    inference(flattening,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.44    inference(negated_conjecture,[],[f8])).
% 0.22/0.44  fof(f8,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_xboole_1)).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f20,f38])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    r2_xboole_0(sK1,sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ~spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f34])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ~r2_xboole_0(sK0,sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (2381)------------------------------
% 0.22/0.44  % (2381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (2381)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (2381)Memory used [KB]: 10746
% 0.22/0.44  % (2381)Time elapsed: 0.015 s
% 0.22/0.44  % (2381)------------------------------
% 0.22/0.44  % (2381)------------------------------
% 0.22/0.45  % (2369)Success in time 0.086 s
%------------------------------------------------------------------------------
