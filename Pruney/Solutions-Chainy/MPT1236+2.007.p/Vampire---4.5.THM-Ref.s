%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 (  99 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :    6
%              Number of atoms          :  158 ( 235 expanded)
%              Number of equality atoms :   29 (  48 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f36,f40,f44,f48,f52,f58,f64,f70,f77,f84,f101])).

fof(f101,plain,
    ( spl1_10
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl1_10
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f95,f69])).

fof(f69,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0)
    | spl1_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl1_10
  <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f95,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(resolution,[],[f83,f76])).

fof(f76,plain,
    ( v1_xboole_0(k1_tops_1(sK0,k1_xboole_0))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl1_11
  <=> v1_xboole_0(k1_tops_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl1_12
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f84,plain,
    ( spl1_12
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f78,f50,f33,f82])).

fof(f33,plain,
    ( spl1_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f50,plain,
    ( spl1_7
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | X0 = X1
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f78,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(resolution,[],[f51,f35])).

fof(f35,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | X0 = X1
        | ~ v1_xboole_0(X0) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f77,plain,
    ( spl1_11
    | ~ spl1_2
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f72,f61,f46,f28,f74])).

fof(f28,plain,
    ( spl1_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f46,plain,
    ( spl1_6
  <=> ! [X0] :
        ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f61,plain,
    ( spl1_9
  <=> k1_xboole_0 = k1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f72,plain,
    ( v1_xboole_0(k1_tops_1(sK0,k1_xboole_0))
    | ~ spl1_2
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f71,f30])).

fof(f30,plain,
    ( l1_pre_topc(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f71,plain,
    ( v1_xboole_0(k1_tops_1(sK0,k1_xboole_0))
    | ~ l1_pre_topc(sK0)
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(superposition,[],[f47,f63])).

fof(f63,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f47,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f70,plain,
    ( ~ spl1_10
    | spl1_1
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f65,f61,f23,f67])).

fof(f23,plain,
    ( spl1_1
  <=> k1_struct_0(sK0) = k1_tops_1(sK0,k1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f65,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0)
    | spl1_1
    | ~ spl1_9 ),
    inference(backward_demodulation,[],[f25,f63])).

fof(f25,plain,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f64,plain,
    ( spl1_9
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f59,f55,f38,f61])).

fof(f38,plain,
    ( spl1_4
  <=> ! [X0] :
        ( k1_xboole_0 = k1_struct_0(X0)
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f55,plain,
    ( spl1_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f59,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(resolution,[],[f39,f57])).

fof(f57,plain,
    ( l1_struct_0(sK0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f39,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k1_xboole_0 = k1_struct_0(X0) )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f58,plain,
    ( spl1_8
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f53,f42,f28,f55])).

fof(f42,plain,
    ( spl1_5
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f53,plain,
    ( l1_struct_0(sK0)
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(resolution,[],[f43,f30])).

fof(f43,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f52,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f48,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_tops_1)).

fof(f44,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f19,f42])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f40,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

fof(f36,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f31,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f15,f28])).

fof(f15,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
        & l1_pre_topc(X0) )
   => ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).

fof(f26,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f16,f23])).

fof(f16,plain,(
    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:44:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (21987)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.42  % (21987)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f102,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f26,f31,f36,f40,f44,f48,f52,f58,f64,f70,f77,f84,f101])).
% 0.22/0.42  fof(f101,plain,(
% 0.22/0.42    spl1_10 | ~spl1_11 | ~spl1_12),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f100])).
% 0.22/0.42  fof(f100,plain,(
% 0.22/0.42    $false | (spl1_10 | ~spl1_11 | ~spl1_12)),
% 0.22/0.42    inference(subsumption_resolution,[],[f95,f69])).
% 0.22/0.42  fof(f69,plain,(
% 0.22/0.42    k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0) | spl1_10),
% 0.22/0.42    inference(avatar_component_clause,[],[f67])).
% 0.22/0.42  fof(f67,plain,(
% 0.22/0.42    spl1_10 <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.42  fof(f95,plain,(
% 0.22/0.42    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | (~spl1_11 | ~spl1_12)),
% 0.22/0.42    inference(resolution,[],[f83,f76])).
% 0.22/0.42  fof(f76,plain,(
% 0.22/0.42    v1_xboole_0(k1_tops_1(sK0,k1_xboole_0)) | ~spl1_11),
% 0.22/0.42    inference(avatar_component_clause,[],[f74])).
% 0.22/0.42  fof(f74,plain,(
% 0.22/0.42    spl1_11 <=> v1_xboole_0(k1_tops_1(sK0,k1_xboole_0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.22/0.42  fof(f83,plain,(
% 0.22/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl1_12),
% 0.22/0.42    inference(avatar_component_clause,[],[f82])).
% 0.22/0.42  fof(f82,plain,(
% 0.22/0.42    spl1_12 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.22/0.42  fof(f84,plain,(
% 0.22/0.42    spl1_12 | ~spl1_3 | ~spl1_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f78,f50,f33,f82])).
% 0.22/0.42  fof(f33,plain,(
% 0.22/0.42    spl1_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    spl1_7 <=> ! [X1,X0] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.42  fof(f78,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | (~spl1_3 | ~spl1_7)),
% 0.22/0.42    inference(resolution,[],[f51,f35])).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    v1_xboole_0(k1_xboole_0) | ~spl1_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f33])).
% 0.22/0.42  fof(f51,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) ) | ~spl1_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f50])).
% 0.22/0.42  fof(f77,plain,(
% 0.22/0.42    spl1_11 | ~spl1_2 | ~spl1_6 | ~spl1_9),
% 0.22/0.42    inference(avatar_split_clause,[],[f72,f61,f46,f28,f74])).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    spl1_2 <=> l1_pre_topc(sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    spl1_6 <=> ! [X0] : (v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.42  fof(f61,plain,(
% 0.22/0.42    spl1_9 <=> k1_xboole_0 = k1_struct_0(sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.42  fof(f72,plain,(
% 0.22/0.42    v1_xboole_0(k1_tops_1(sK0,k1_xboole_0)) | (~spl1_2 | ~spl1_6 | ~spl1_9)),
% 0.22/0.42    inference(subsumption_resolution,[],[f71,f30])).
% 0.22/0.42  fof(f30,plain,(
% 0.22/0.42    l1_pre_topc(sK0) | ~spl1_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f28])).
% 0.22/0.42  fof(f71,plain,(
% 0.22/0.42    v1_xboole_0(k1_tops_1(sK0,k1_xboole_0)) | ~l1_pre_topc(sK0) | (~spl1_6 | ~spl1_9)),
% 0.22/0.42    inference(superposition,[],[f47,f63])).
% 0.22/0.42  fof(f63,plain,(
% 0.22/0.42    k1_xboole_0 = k1_struct_0(sK0) | ~spl1_9),
% 0.22/0.42    inference(avatar_component_clause,[],[f61])).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    ( ! [X0] : (v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl1_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f46])).
% 0.22/0.42  fof(f70,plain,(
% 0.22/0.42    ~spl1_10 | spl1_1 | ~spl1_9),
% 0.22/0.42    inference(avatar_split_clause,[],[f65,f61,f23,f67])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    spl1_1 <=> k1_struct_0(sK0) = k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.42  fof(f65,plain,(
% 0.22/0.42    k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0) | (spl1_1 | ~spl1_9)),
% 0.22/0.42    inference(backward_demodulation,[],[f25,f63])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) | spl1_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f23])).
% 0.22/0.42  fof(f64,plain,(
% 0.22/0.42    spl1_9 | ~spl1_4 | ~spl1_8),
% 0.22/0.42    inference(avatar_split_clause,[],[f59,f55,f38,f61])).
% 0.22/0.42  fof(f38,plain,(
% 0.22/0.42    spl1_4 <=> ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.42  fof(f55,plain,(
% 0.22/0.42    spl1_8 <=> l1_struct_0(sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.42  fof(f59,plain,(
% 0.22/0.42    k1_xboole_0 = k1_struct_0(sK0) | (~spl1_4 | ~spl1_8)),
% 0.22/0.42    inference(resolution,[],[f39,f57])).
% 0.22/0.42  fof(f57,plain,(
% 0.22/0.42    l1_struct_0(sK0) | ~spl1_8),
% 0.22/0.42    inference(avatar_component_clause,[],[f55])).
% 0.22/0.42  fof(f39,plain,(
% 0.22/0.42    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) ) | ~spl1_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f38])).
% 0.22/0.42  fof(f58,plain,(
% 0.22/0.42    spl1_8 | ~spl1_2 | ~spl1_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f53,f42,f28,f55])).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    spl1_5 <=> ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.42  fof(f53,plain,(
% 0.22/0.42    l1_struct_0(sK0) | (~spl1_2 | ~spl1_5)),
% 0.22/0.42    inference(resolution,[],[f43,f30])).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) ) | ~spl1_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f42])).
% 0.22/0.42  fof(f52,plain,(
% 0.22/0.42    spl1_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f21,f50])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    spl1_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f20,f46])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0] : (v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ! [X0] : (v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    ! [X0] : (l1_pre_topc(X0) => v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_tops_1)).
% 0.22/0.42  fof(f44,plain,(
% 0.22/0.42    spl1_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f19,f42])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.42  fof(f40,plain,(
% 0.22/0.42    spl1_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f18,f38])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    spl1_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f17,f33])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    v1_xboole_0(k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    v1_xboole_0(k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.42  fof(f31,plain,(
% 0.22/0.42    spl1_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f15,f28])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    l1_pre_topc(sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) & l1_pre_topc(sK0)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ? [X0] : (k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0)) & l1_pre_topc(X0)) => (k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) & l1_pre_topc(sK0))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ? [X0] : (k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0)) & l1_pre_topc(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,negated_conjecture,(
% 0.22/0.42    ~! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 0.22/0.42    inference(negated_conjecture,[],[f6])).
% 0.22/0.42  fof(f6,conjecture,(
% 0.22/0.42    ! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    ~spl1_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f16,f23])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (21987)------------------------------
% 0.22/0.42  % (21987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (21987)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (21987)Memory used [KB]: 6140
% 0.22/0.42  % (21987)Time elapsed: 0.004 s
% 0.22/0.42  % (21987)------------------------------
% 0.22/0.42  % (21987)------------------------------
% 0.22/0.42  % (21976)Success in time 0.062 s
%------------------------------------------------------------------------------
