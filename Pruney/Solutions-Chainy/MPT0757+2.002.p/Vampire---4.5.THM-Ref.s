%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 114 expanded)
%              Number of leaves         :   14 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  183 ( 442 expanded)
%              Number of equality atoms :   18 (  61 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f38,f42,f46,f50,f71,f89,f97])).

fof(f97,plain,
    ( spl2_3
    | spl2_2
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f91,f66,f36,f40])).

fof(f40,plain,
    ( spl2_3
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f36,plain,
    ( spl2_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f66,plain,
    ( spl2_7
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f91,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK0,sK1)
    | ~ spl2_7 ),
    inference(resolution,[],[f67,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f67,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f89,plain,
    ( spl2_1
    | spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f81,f69,f36,f32])).

fof(f32,plain,
    ( spl2_1
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f69,plain,
    ( spl2_8
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f81,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK1,sK0)
    | ~ spl2_8 ),
    inference(resolution,[],[f70,f30])).

fof(f70,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,
    ( spl2_7
    | spl2_8
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f59,f48,f44,f69,f66])).

fof(f44,plain,
    ( spl2_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f48,plain,
    ( spl2_5
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f59,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1)
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(resolution,[],[f56,f49])).

fof(f49,plain,
    ( v3_ordinal1(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f56,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r1_tarski(sK1,X0)
        | r1_tarski(X0,sK1) )
    | ~ spl2_4 ),
    inference(resolution,[],[f55,f45])).

fof(f45,plain,
    ( v3_ordinal1(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f53,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f28,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f52,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f50,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f21,f48])).

fof(f21,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    & sK0 != sK1
    & ~ r2_xboole_0(sK0,sK1)
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_xboole_0(X1,X0)
            & X0 != X1
            & ~ r2_xboole_0(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ r2_xboole_0(X1,sK0)
          & sK0 != X1
          & ~ r2_xboole_0(sK0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ~ r2_xboole_0(X1,sK0)
        & sK0 != X1
        & ~ r2_xboole_0(sK0,X1)
        & v3_ordinal1(X1) )
   => ( ~ r2_xboole_0(sK1,sK0)
      & sK0 != sK1
      & ~ r2_xboole_0(sK0,sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ~ ( ~ r2_xboole_0(X1,X0)
                & X0 != X1
                & ~ r2_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).

fof(f46,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f23,f40])).

fof(f23,plain,(
    ~ r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f24,f36])).

fof(f24,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f25,f32])).

fof(f25,plain,(
    ~ r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:10:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (24987)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (24987)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f98,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f34,f38,f42,f46,f50,f71,f89,f97])).
% 0.22/0.47  fof(f97,plain,(
% 0.22/0.47    spl2_3 | spl2_2 | ~spl2_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f91,f66,f36,f40])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    spl2_3 <=> r2_xboole_0(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    spl2_2 <=> sK0 = sK1),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    spl2_7 <=> r1_tarski(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    sK0 = sK1 | r2_xboole_0(sK0,sK1) | ~spl2_7),
% 0.22/0.47    inference(resolution,[],[f67,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.22/0.47    inference(unused_predicate_definition_removal,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    r1_tarski(sK0,sK1) | ~spl2_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f66])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    spl2_1 | spl2_2 | ~spl2_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f81,f69,f36,f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    spl2_1 <=> r2_xboole_0(sK1,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    spl2_8 <=> r1_tarski(sK1,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    sK0 = sK1 | r2_xboole_0(sK1,sK0) | ~spl2_8),
% 0.22/0.47    inference(resolution,[],[f70,f30])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    r1_tarski(sK1,sK0) | ~spl2_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f69])).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    spl2_7 | spl2_8 | ~spl2_4 | ~spl2_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f59,f48,f44,f69,f66])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    spl2_4 <=> v3_ordinal1(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    spl2_5 <=> v3_ordinal1(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    r1_tarski(sK1,sK0) | r1_tarski(sK0,sK1) | (~spl2_4 | ~spl2_5)),
% 0.22/0.47    inference(resolution,[],[f56,f49])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    v3_ordinal1(sK0) | ~spl2_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f48])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    ( ! [X0] : (~v3_ordinal1(X0) | r1_tarski(sK1,X0) | r1_tarski(X0,sK1)) ) | ~spl2_4),
% 0.22/0.47    inference(resolution,[],[f55,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    v3_ordinal1(sK1) | ~spl2_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f44])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v3_ordinal1(X0) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | r1_tarski(X1,X0)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f54])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v3_ordinal1(X0) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X1,X0)) )),
% 0.22/0.47    inference(resolution,[],[f53,f52])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f51])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.47    inference(resolution,[],[f28,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.47    inference(flattening,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.47    inference(flattening,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v3_ordinal1(X1) | r1_tarski(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.22/0.47    inference(resolution,[],[f52,f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    spl2_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f21,f48])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    v3_ordinal1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    (~r2_xboole_0(sK1,sK0) & sK0 != sK1 & ~r2_xboole_0(sK0,sK1) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (~r2_xboole_0(X1,sK0) & sK0 != X1 & ~r2_xboole_0(sK0,X1) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ? [X1] : (~r2_xboole_0(X1,sK0) & sK0 != X1 & ~r2_xboole_0(sK0,X1) & v3_ordinal1(X1)) => (~r2_xboole_0(sK1,sK0) & sK0 != sK1 & ~r2_xboole_0(sK0,sK1) & v3_ordinal1(sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.47    inference(flattening,[],[f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.22/0.47    inference(negated_conjecture,[],[f5])).
% 0.22/0.47  fof(f5,conjecture,(
% 0.22/0.47    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    spl2_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f22,f44])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    v3_ordinal1(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ~spl2_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f23,f40])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ~r2_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ~spl2_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f24,f36])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    sK0 != sK1),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ~spl2_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f25,f32])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ~r2_xboole_0(sK1,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (24987)------------------------------
% 0.22/0.47  % (24987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (24987)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (24987)Memory used [KB]: 10618
% 0.22/0.47  % (24987)Time elapsed: 0.053 s
% 0.22/0.47  % (24987)------------------------------
% 0.22/0.47  % (24987)------------------------------
% 0.22/0.47  % (24978)Success in time 0.115 s
%------------------------------------------------------------------------------
