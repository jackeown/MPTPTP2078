%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 (  99 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :  159 ( 269 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f62,f72,f76,f89,f106,f126])).

fof(f126,plain,
    ( ~ spl2_1
    | spl2_10 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | ~ spl2_1
    | spl2_10 ),
    inference(unit_resulting_resolution,[],[f35,f35,f30,f105,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f105,plain,
    ( ~ r1_ordinal1(sK0,sK0)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_10
  <=> r1_ordinal1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f30,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f35,plain,
    ( v3_ordinal1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f106,plain,
    ( ~ spl2_10
    | spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f91,f85,f43,f103])).

fof(f43,plain,
    ( spl2_3
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f85,plain,
    ( spl2_8
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f91,plain,
    ( ~ r1_ordinal1(sK0,sK0)
    | spl2_3
    | ~ spl2_8 ),
    inference(backward_demodulation,[],[f45,f87])).

fof(f87,plain,
    ( sK0 = sK1
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f45,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f89,plain,
    ( ~ spl2_4
    | spl2_8
    | spl2_2
    | ~ spl2_1
    | spl2_7 ),
    inference(avatar_split_clause,[],[f83,f69,f33,f38,f85,f48])).

fof(f48,plain,
    ( spl2_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f38,plain,
    ( spl2_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f69,plain,
    ( spl2_7
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f83,plain,
    ( ~ v3_ordinal1(sK0)
    | r2_hidden(sK1,sK0)
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | spl2_7 ),
    inference(resolution,[],[f23,f71])).

fof(f71,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f76,plain,
    ( ~ spl2_4
    | spl2_6 ),
    inference(avatar_split_clause,[],[f74,f65,f48])).

fof(f65,plain,
    ( spl2_6
  <=> v1_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f74,plain,
    ( ~ v3_ordinal1(sK1)
    | spl2_6 ),
    inference(resolution,[],[f67,f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f67,plain,
    ( ~ v1_ordinal1(sK1)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f72,plain,
    ( ~ spl2_6
    | ~ spl2_7
    | spl2_5 ),
    inference(avatar_split_clause,[],[f63,f59,f69,f65])).

fof(f59,plain,
    ( spl2_5
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f63,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v1_ordinal1(sK1)
    | spl2_5 ),
    inference(resolution,[],[f61,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f61,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f62,plain,
    ( ~ spl2_1
    | ~ spl2_5
    | ~ spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f57,f43,f48,f59,f33])).

fof(f57,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | spl2_3 ),
    inference(resolution,[],[f25,f45])).

fof(f51,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f18,f48])).

fof(f18,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r1_ordinal1(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r1_ordinal1(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
              | r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f46,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    ~ r1_ordinal1(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f20,f38])).

fof(f20,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f21,f33])).

fof(f21,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:18:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (11752)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.47  % (11744)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.48  % (11744)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f62,f72,f76,f89,f106,f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ~spl2_1 | spl2_10),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f123])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    $false | (~spl2_1 | spl2_10)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f35,f35,f30,f105,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ~r1_ordinal1(sK0,sK0) | spl2_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f103])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl2_10 <=> r1_ordinal1(sK0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    v3_ordinal1(sK0) | ~spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    spl2_1 <=> v3_ordinal1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ~spl2_10 | spl2_3 | ~spl2_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f91,f85,f43,f103])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl2_3 <=> r1_ordinal1(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl2_8 <=> sK0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ~r1_ordinal1(sK0,sK0) | (spl2_3 | ~spl2_8)),
% 0.21/0.48    inference(backward_demodulation,[],[f45,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    sK0 = sK1 | ~spl2_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f85])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ~r1_ordinal1(sK0,sK1) | spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f43])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ~spl2_4 | spl2_8 | spl2_2 | ~spl2_1 | spl2_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f83,f69,f33,f38,f85,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl2_4 <=> v3_ordinal1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    spl2_2 <=> r2_hidden(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl2_7 <=> r2_hidden(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ~v3_ordinal1(sK0) | r2_hidden(sK1,sK0) | sK0 = sK1 | ~v3_ordinal1(sK1) | spl2_7),
% 0.21/0.48    inference(resolution,[],[f23,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ~r2_hidden(sK0,sK1) | spl2_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f69])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | ~v3_ordinal1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ~spl2_4 | spl2_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f74,f65,f48])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl2_6 <=> v1_ordinal1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ~v3_ordinal1(sK1) | spl2_6),
% 0.21/0.48    inference(resolution,[],[f67,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~v1_ordinal1(sK1) | spl2_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f65])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ~spl2_6 | ~spl2_7 | spl2_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f63,f59,f69,f65])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl2_5 <=> r1_tarski(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ~r2_hidden(sK0,sK1) | ~v1_ordinal1(sK1) | spl2_5),
% 0.21/0.48    inference(resolution,[],[f61,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) | spl2_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f59])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ~spl2_1 | ~spl2_5 | ~spl2_4 | spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f57,f43,f48,f59,f33])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ~v3_ordinal1(sK1) | ~r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | spl2_3),
% 0.21/0.48    inference(resolution,[],[f25,f45])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f48])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    v3_ordinal1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~r2_hidden(X1,X0) & ~r1_ordinal1(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~r2_hidden(X1,X0) & ~r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ~spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f43])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ~r1_ordinal1(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ~spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f38])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ~r2_hidden(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f33])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    v3_ordinal1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (11744)------------------------------
% 0.21/0.48  % (11744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (11744)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (11744)Memory used [KB]: 6140
% 0.21/0.48  % (11744)Time elapsed: 0.069 s
% 0.21/0.48  % (11744)------------------------------
% 0.21/0.48  % (11744)------------------------------
% 0.21/0.48  % (11728)Success in time 0.124 s
%------------------------------------------------------------------------------
