%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 (  84 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :  136 ( 223 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f34,f38,f42,f46,f52,f63,f75,f83])).

fof(f83,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f81,f33])).

fof(f33,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

% (31563)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f81,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_4
    | spl3_11 ),
    inference(resolution,[],[f74,f37])).

fof(f37,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f74,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_11
  <=> v1_relat_1(k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f75,plain,
    ( ~ spl3_11
    | spl3_1
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f70,f60,f40,f21,f72])).

fof(f21,plain,
    ( spl3_1
  <=> r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f40,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_tarski(k8_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f60,plain,
    ( spl3_9
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f70,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | spl3_1
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f68,f23])).

fof(f23,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f68,plain,
    ( r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(superposition,[],[f41,f62])).

fof(f62,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f60])).

fof(f41,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k8_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f63,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f57,f50,f31,f60])).

fof(f50,plain,
    ( spl3_7
  <=> ! [X0] :
        ( k8_relat_1(sK0,k8_relat_1(sK1,X0)) = k8_relat_1(sK0,X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f57,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f51,f33])).

fof(f51,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k8_relat_1(sK0,k8_relat_1(sK1,X0)) = k8_relat_1(sK0,X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f52,plain,
    ( spl3_7
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f47,f44,f26,f50])).

fof(f26,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f44,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f47,plain,
    ( ! [X0] :
        ( k8_relat_1(sK0,k8_relat_1(sK1,X0)) = k8_relat_1(sK0,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f45,f28])).

fof(f28,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f45,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
        | ~ v1_relat_1(X2) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f44])).

fof(f46,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_relat_1)).

fof(f42,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

fof(f38,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f34,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f14,f31])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).

fof(f29,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f16,f21])).

fof(f16,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 13:31:11 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.44  % (31564)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.44  % (31567)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.44  % (31567)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f84,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f24,f29,f34,f38,f42,f46,f52,f63,f75,f83])).
% 0.22/0.44  fof(f83,plain,(
% 0.22/0.44    ~spl3_3 | ~spl3_4 | spl3_11),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f82])).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    $false | (~spl3_3 | ~spl3_4 | spl3_11)),
% 0.22/0.44    inference(subsumption_resolution,[],[f81,f33])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    v1_relat_1(sK2) | ~spl3_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    spl3_3 <=> v1_relat_1(sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.44  % (31563)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  fof(f81,plain,(
% 0.22/0.44    ~v1_relat_1(sK2) | (~spl3_4 | spl3_11)),
% 0.22/0.44    inference(resolution,[],[f74,f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | ~spl3_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f36])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    spl3_4 <=> ! [X1,X0] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    ~v1_relat_1(k8_relat_1(sK1,sK2)) | spl3_11),
% 0.22/0.44    inference(avatar_component_clause,[],[f72])).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    spl3_11 <=> v1_relat_1(k8_relat_1(sK1,sK2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    ~spl3_11 | spl3_1 | ~spl3_5 | ~spl3_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f70,f60,f40,f21,f72])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    spl3_1 <=> r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    spl3_5 <=> ! [X1,X0] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    spl3_9 <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    ~v1_relat_1(k8_relat_1(sK1,sK2)) | (spl3_1 | ~spl3_5 | ~spl3_9)),
% 0.22/0.44    inference(subsumption_resolution,[],[f68,f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) | spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f21])).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) | ~v1_relat_1(k8_relat_1(sK1,sK2)) | (~spl3_5 | ~spl3_9)),
% 0.22/0.44    inference(superposition,[],[f41,f62])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) | ~spl3_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f60])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) ) | ~spl3_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f40])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    spl3_9 | ~spl3_3 | ~spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f57,f50,f31,f60])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    spl3_7 <=> ! [X0] : (k8_relat_1(sK0,k8_relat_1(sK1,X0)) = k8_relat_1(sK0,X0) | ~v1_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) | (~spl3_3 | ~spl3_7)),
% 0.22/0.44    inference(resolution,[],[f51,f33])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(sK0,k8_relat_1(sK1,X0)) = k8_relat_1(sK0,X0)) ) | ~spl3_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f50])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    spl3_7 | ~spl3_2 | ~spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f47,f44,f26,f50])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    spl3_6 <=> ! [X1,X0,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    ( ! [X0] : (k8_relat_1(sK0,k8_relat_1(sK1,X0)) = k8_relat_1(sK0,X0) | ~v1_relat_1(X0)) ) | (~spl3_2 | ~spl3_6)),
% 0.22/0.44    inference(resolution,[],[f45,f28])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f26])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) | ~v1_relat_1(X2)) ) | ~spl3_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f44])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f19,f44])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.44    inference(flattening,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0,X1,X2] : ((k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_relat_1)).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    spl3_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f18,f40])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f17,f36])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f14,f31])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    v1_relat_1(sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.22/0.44    inference(flattening,[],[f6])).
% 0.22/0.44  fof(f6,plain,(
% 0.22/0.44    ? [X0,X1,X2] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))))),
% 0.22/0.44    inference(negated_conjecture,[],[f4])).
% 0.22/0.44  fof(f4,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f15,f26])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    r1_tarski(sK0,sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ~spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f16,f21])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (31567)------------------------------
% 0.22/0.44  % (31567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (31567)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (31567)Memory used [KB]: 6140
% 0.22/0.44  % (31567)Time elapsed: 0.004 s
% 0.22/0.44  % (31567)------------------------------
% 0.22/0.44  % (31567)------------------------------
% 0.22/0.44  % (31549)Success in time 0.071 s
%------------------------------------------------------------------------------
