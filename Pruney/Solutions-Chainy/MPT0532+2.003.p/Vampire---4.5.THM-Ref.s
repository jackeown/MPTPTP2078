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
% DateTime   : Thu Dec  3 12:49:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 114 expanded)
%              Number of leaves         :   17 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :  195 ( 372 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f161,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f44,f48,f52,f59,f63,f85,f144,f160])).

fof(f160,plain,
    ( spl3_1
    | ~ spl3_22 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl3_1
    | ~ spl3_22 ),
    inference(resolution,[],[f143,f24])).

fof(f24,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl3_1
  <=> r1_tarski(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f143,plain,
    ( ! [X0] : r1_tarski(k8_relat_1(X0,sK1),k8_relat_1(X0,sK2))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl3_22
  <=> ! [X0] : r1_tarski(k8_relat_1(X0,sK1),k8_relat_1(X0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f144,plain,
    ( spl3_22
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f140,f83,f57,f32,f27,f142])).

fof(f27,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

% (1237)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
fof(f32,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f57,plain,
    ( spl3_8
  <=> ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f83,plain,
    ( spl3_12
  <=> ! [X3,X2] :
        ( r1_tarski(k8_relat_1(X2,sK1),k5_relat_1(X3,k6_relat_1(X2)))
        | ~ r1_tarski(sK1,X3)
        | ~ v1_relat_1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f140,plain,
    ( ! [X0] : r1_tarski(k8_relat_1(X0,sK1),k8_relat_1(X0,sK2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f139,f34])).

fof(f34,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f139,plain,
    ( ! [X0] :
        ( r1_tarski(k8_relat_1(X0,sK1),k8_relat_1(X0,sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f136,f29])).

fof(f29,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f136,plain,
    ( ! [X0] :
        ( r1_tarski(k8_relat_1(X0,sK1),k8_relat_1(X0,sK2))
        | ~ r1_tarski(sK1,sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(superposition,[],[f84,f58])).

fof(f58,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f84,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k8_relat_1(X2,sK1),k5_relat_1(X3,k6_relat_1(X2)))
        | ~ r1_tarski(sK1,X3)
        | ~ v1_relat_1(X3) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f85,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f81,f61,f46,f42,f37,f83])).

fof(f37,plain,
    ( spl3_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f42,plain,
    ( spl3_5
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f46,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f61,plain,
    ( spl3_9
  <=> ! [X1] : k8_relat_1(X1,sK1) = k5_relat_1(sK1,k6_relat_1(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f81,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k8_relat_1(X2,sK1),k5_relat_1(X3,k6_relat_1(X2)))
        | ~ r1_tarski(sK1,X3)
        | ~ v1_relat_1(X3) )
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f80,f39])).

fof(f39,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f80,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k8_relat_1(X2,sK1),k5_relat_1(X3,k6_relat_1(X2)))
        | ~ r1_tarski(sK1,X3)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f69,f43])).

fof(f43,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f69,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k8_relat_1(X2,sK1),k5_relat_1(X3,k6_relat_1(X2)))
        | ~ r1_tarski(sK1,X3)
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(superposition,[],[f47,f62])).

fof(f62,plain,
    ( ! [X1] : k8_relat_1(X1,sK1) = k5_relat_1(sK1,k6_relat_1(X1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f47,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f63,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f54,f50,f37,f61])).

fof(f50,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f54,plain,
    ( ! [X1] : k8_relat_1(X1,sK1) = k5_relat_1(sK1,k6_relat_1(X1))
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(resolution,[],[f51,f39])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f59,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f53,f50,f32,f57])).

fof(f53,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f51,f34])).

fof(f52,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f48,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f46])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).

fof(f44,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f40,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f14,f37])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
            & r1_tarski(X1,X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_relat_1(sK0,sK1),k8_relat_1(sK0,X2))
          & r1_tarski(sK1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_relat_1(sK0,sK1),k8_relat_1(sK0,X2))
        & r1_tarski(sK1,X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

fof(f35,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f15,f32])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f27])).

fof(f16,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f22])).

fof(f17,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:35:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.39  % (1236)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.39  % (1240)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.40  % (1240)Refutation found. Thanks to Tanya!
% 0.21/0.40  % SZS status Theorem for theBenchmark
% 0.21/0.40  % SZS output start Proof for theBenchmark
% 0.21/0.40  fof(f161,plain,(
% 0.21/0.40    $false),
% 0.21/0.40    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f44,f48,f52,f59,f63,f85,f144,f160])).
% 0.21/0.40  fof(f160,plain,(
% 0.21/0.40    spl3_1 | ~spl3_22),
% 0.21/0.40    inference(avatar_contradiction_clause,[],[f159])).
% 0.21/0.40  fof(f159,plain,(
% 0.21/0.40    $false | (spl3_1 | ~spl3_22)),
% 0.21/0.40    inference(resolution,[],[f143,f24])).
% 0.21/0.40  fof(f24,plain,(
% 0.21/0.40    ~r1_tarski(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)) | spl3_1),
% 0.21/0.40    inference(avatar_component_clause,[],[f22])).
% 0.21/0.40  fof(f22,plain,(
% 0.21/0.40    spl3_1 <=> r1_tarski(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.40  fof(f143,plain,(
% 0.21/0.40    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK1),k8_relat_1(X0,sK2))) ) | ~spl3_22),
% 0.21/0.40    inference(avatar_component_clause,[],[f142])).
% 0.21/0.40  fof(f142,plain,(
% 0.21/0.40    spl3_22 <=> ! [X0] : r1_tarski(k8_relat_1(X0,sK1),k8_relat_1(X0,sK2))),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.40  fof(f144,plain,(
% 0.21/0.40    spl3_22 | ~spl3_2 | ~spl3_3 | ~spl3_8 | ~spl3_12),
% 0.21/0.40    inference(avatar_split_clause,[],[f140,f83,f57,f32,f27,f142])).
% 0.21/0.40  fof(f27,plain,(
% 0.21/0.40    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.40  % (1237)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.40  fof(f32,plain,(
% 0.21/0.40    spl3_3 <=> v1_relat_1(sK2)),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.40  fof(f57,plain,(
% 0.21/0.40    spl3_8 <=> ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.40  fof(f83,plain,(
% 0.21/0.40    spl3_12 <=> ! [X3,X2] : (r1_tarski(k8_relat_1(X2,sK1),k5_relat_1(X3,k6_relat_1(X2))) | ~r1_tarski(sK1,X3) | ~v1_relat_1(X3))),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.40  fof(f140,plain,(
% 0.21/0.40    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK1),k8_relat_1(X0,sK2))) ) | (~spl3_2 | ~spl3_3 | ~spl3_8 | ~spl3_12)),
% 0.21/0.40    inference(subsumption_resolution,[],[f139,f34])).
% 0.21/0.40  fof(f34,plain,(
% 0.21/0.40    v1_relat_1(sK2) | ~spl3_3),
% 0.21/0.40    inference(avatar_component_clause,[],[f32])).
% 0.21/0.40  fof(f139,plain,(
% 0.21/0.40    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK1),k8_relat_1(X0,sK2)) | ~v1_relat_1(sK2)) ) | (~spl3_2 | ~spl3_8 | ~spl3_12)),
% 0.21/0.40    inference(subsumption_resolution,[],[f136,f29])).
% 0.21/0.40  fof(f29,plain,(
% 0.21/0.40    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.21/0.40    inference(avatar_component_clause,[],[f27])).
% 0.21/0.40  fof(f136,plain,(
% 0.21/0.40    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK1),k8_relat_1(X0,sK2)) | ~r1_tarski(sK1,sK2) | ~v1_relat_1(sK2)) ) | (~spl3_8 | ~spl3_12)),
% 0.21/0.40    inference(superposition,[],[f84,f58])).
% 0.21/0.40  fof(f58,plain,(
% 0.21/0.40    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) ) | ~spl3_8),
% 0.21/0.40    inference(avatar_component_clause,[],[f57])).
% 0.21/0.40  fof(f84,plain,(
% 0.21/0.40    ( ! [X2,X3] : (r1_tarski(k8_relat_1(X2,sK1),k5_relat_1(X3,k6_relat_1(X2))) | ~r1_tarski(sK1,X3) | ~v1_relat_1(X3)) ) | ~spl3_12),
% 0.21/0.40    inference(avatar_component_clause,[],[f83])).
% 0.21/0.40  fof(f85,plain,(
% 0.21/0.40    spl3_12 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_9),
% 0.21/0.40    inference(avatar_split_clause,[],[f81,f61,f46,f42,f37,f83])).
% 0.21/0.40  fof(f37,plain,(
% 0.21/0.40    spl3_4 <=> v1_relat_1(sK1)),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.40  fof(f42,plain,(
% 0.21/0.40    spl3_5 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.40  fof(f46,plain,(
% 0.21/0.40    spl3_6 <=> ! [X1,X0,X2] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.40  fof(f61,plain,(
% 0.21/0.40    spl3_9 <=> ! [X1] : k8_relat_1(X1,sK1) = k5_relat_1(sK1,k6_relat_1(X1))),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.40  fof(f81,plain,(
% 0.21/0.40    ( ! [X2,X3] : (r1_tarski(k8_relat_1(X2,sK1),k5_relat_1(X3,k6_relat_1(X2))) | ~r1_tarski(sK1,X3) | ~v1_relat_1(X3)) ) | (~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_9)),
% 0.21/0.40    inference(subsumption_resolution,[],[f80,f39])).
% 0.21/0.40  fof(f39,plain,(
% 0.21/0.40    v1_relat_1(sK1) | ~spl3_4),
% 0.21/0.40    inference(avatar_component_clause,[],[f37])).
% 0.21/0.40  fof(f80,plain,(
% 0.21/0.40    ( ! [X2,X3] : (r1_tarski(k8_relat_1(X2,sK1),k5_relat_1(X3,k6_relat_1(X2))) | ~r1_tarski(sK1,X3) | ~v1_relat_1(X3) | ~v1_relat_1(sK1)) ) | (~spl3_5 | ~spl3_6 | ~spl3_9)),
% 0.21/0.40    inference(subsumption_resolution,[],[f69,f43])).
% 0.21/0.40  fof(f43,plain,(
% 0.21/0.40    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_5),
% 0.21/0.40    inference(avatar_component_clause,[],[f42])).
% 0.21/0.40  fof(f69,plain,(
% 0.21/0.40    ( ! [X2,X3] : (r1_tarski(k8_relat_1(X2,sK1),k5_relat_1(X3,k6_relat_1(X2))) | ~r1_tarski(sK1,X3) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(X3) | ~v1_relat_1(sK1)) ) | (~spl3_6 | ~spl3_9)),
% 0.21/0.40    inference(superposition,[],[f47,f62])).
% 0.21/0.40  fof(f62,plain,(
% 0.21/0.40    ( ! [X1] : (k8_relat_1(X1,sK1) = k5_relat_1(sK1,k6_relat_1(X1))) ) | ~spl3_9),
% 0.21/0.40    inference(avatar_component_clause,[],[f61])).
% 0.21/0.40  fof(f47,plain,(
% 0.21/0.40    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl3_6),
% 0.21/0.40    inference(avatar_component_clause,[],[f46])).
% 0.21/0.40  fof(f63,plain,(
% 0.21/0.40    spl3_9 | ~spl3_4 | ~spl3_7),
% 0.21/0.40    inference(avatar_split_clause,[],[f54,f50,f37,f61])).
% 0.21/0.40  fof(f50,plain,(
% 0.21/0.40    spl3_7 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.40  fof(f54,plain,(
% 0.21/0.40    ( ! [X1] : (k8_relat_1(X1,sK1) = k5_relat_1(sK1,k6_relat_1(X1))) ) | (~spl3_4 | ~spl3_7)),
% 0.21/0.40    inference(resolution,[],[f51,f39])).
% 0.21/0.40  fof(f51,plain,(
% 0.21/0.40    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) ) | ~spl3_7),
% 0.21/0.40    inference(avatar_component_clause,[],[f50])).
% 0.21/0.40  fof(f59,plain,(
% 0.21/0.40    spl3_8 | ~spl3_3 | ~spl3_7),
% 0.21/0.40    inference(avatar_split_clause,[],[f53,f50,f32,f57])).
% 0.21/0.40  fof(f53,plain,(
% 0.21/0.40    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) ) | (~spl3_3 | ~spl3_7)),
% 0.21/0.40    inference(resolution,[],[f51,f34])).
% 0.21/0.40  fof(f52,plain,(
% 0.21/0.40    spl3_7),
% 0.21/0.40    inference(avatar_split_clause,[],[f20,f50])).
% 0.21/0.40  fof(f20,plain,(
% 0.21/0.40    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.40    inference(cnf_transformation,[],[f10])).
% 0.21/0.40  fof(f10,plain,(
% 0.21/0.40    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.40    inference(ennf_transformation,[],[f2])).
% 0.21/0.40  fof(f2,axiom,(
% 0.21/0.40    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.40  fof(f48,plain,(
% 0.21/0.40    spl3_6),
% 0.21/0.40    inference(avatar_split_clause,[],[f19,f46])).
% 0.21/0.40  fof(f19,plain,(
% 0.21/0.40    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.40    inference(cnf_transformation,[],[f9])).
% 0.21/0.40  fof(f9,plain,(
% 0.21/0.40    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.40    inference(flattening,[],[f8])).
% 0.21/0.40  fof(f8,plain,(
% 0.21/0.40    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.40    inference(ennf_transformation,[],[f3])).
% 0.21/0.40  fof(f3,axiom,(
% 0.21/0.40    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))))))),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).
% 0.21/0.40  fof(f44,plain,(
% 0.21/0.40    spl3_5),
% 0.21/0.40    inference(avatar_split_clause,[],[f18,f42])).
% 0.21/0.40  fof(f18,plain,(
% 0.21/0.40    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.40    inference(cnf_transformation,[],[f1])).
% 0.21/0.40  fof(f1,axiom,(
% 0.21/0.40    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.40  fof(f40,plain,(
% 0.21/0.40    spl3_4),
% 0.21/0.40    inference(avatar_split_clause,[],[f14,f37])).
% 0.21/0.40  fof(f14,plain,(
% 0.21/0.40    v1_relat_1(sK1)),
% 0.21/0.40    inference(cnf_transformation,[],[f13])).
% 0.21/0.40  fof(f13,plain,(
% 0.21/0.40    (~r1_tarski(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)) & r1_tarski(sK1,sK2) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.21/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12,f11])).
% 0.21/0.40  fof(f11,plain,(
% 0.21/0.40    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) & r1_tarski(X1,X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k8_relat_1(sK0,sK1),k8_relat_1(sK0,X2)) & r1_tarski(sK1,X2) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.40    introduced(choice_axiom,[])).
% 0.21/0.40  fof(f12,plain,(
% 0.21/0.40    ? [X2] : (~r1_tarski(k8_relat_1(sK0,sK1),k8_relat_1(sK0,X2)) & r1_tarski(sK1,X2) & v1_relat_1(X2)) => (~r1_tarski(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)) & r1_tarski(sK1,sK2) & v1_relat_1(sK2))),
% 0.21/0.40    introduced(choice_axiom,[])).
% 0.21/0.40  fof(f7,plain,(
% 0.21/0.40    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) & r1_tarski(X1,X2) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.40    inference(flattening,[],[f6])).
% 0.21/0.40  fof(f6,plain,(
% 0.21/0.40    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) & r1_tarski(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.40    inference(ennf_transformation,[],[f5])).
% 0.21/0.40  fof(f5,negated_conjecture,(
% 0.21/0.40    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 0.21/0.40    inference(negated_conjecture,[],[f4])).
% 0.21/0.40  fof(f4,conjecture,(
% 0.21/0.40    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).
% 0.21/0.40  fof(f35,plain,(
% 0.21/0.40    spl3_3),
% 0.21/0.40    inference(avatar_split_clause,[],[f15,f32])).
% 0.21/0.40  fof(f15,plain,(
% 0.21/0.40    v1_relat_1(sK2)),
% 0.21/0.40    inference(cnf_transformation,[],[f13])).
% 0.21/0.40  fof(f30,plain,(
% 0.21/0.40    spl3_2),
% 0.21/0.40    inference(avatar_split_clause,[],[f16,f27])).
% 0.21/0.40  fof(f16,plain,(
% 0.21/0.40    r1_tarski(sK1,sK2)),
% 0.21/0.40    inference(cnf_transformation,[],[f13])).
% 0.21/0.40  fof(f25,plain,(
% 0.21/0.40    ~spl3_1),
% 0.21/0.40    inference(avatar_split_clause,[],[f17,f22])).
% 0.21/0.40  fof(f17,plain,(
% 0.21/0.40    ~r1_tarski(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),
% 0.21/0.40    inference(cnf_transformation,[],[f13])).
% 0.21/0.40  % SZS output end Proof for theBenchmark
% 0.21/0.40  % (1240)------------------------------
% 0.21/0.40  % (1240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.40  % (1240)Termination reason: Refutation
% 0.21/0.40  
% 0.21/0.40  % (1240)Memory used [KB]: 6140
% 0.21/0.40  % (1240)Time elapsed: 0.005 s
% 0.21/0.40  % (1240)------------------------------
% 0.21/0.40  % (1240)------------------------------
% 0.21/0.40  % (1229)Success in time 0.041 s
%------------------------------------------------------------------------------
