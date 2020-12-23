%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  59 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   91 ( 117 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f219,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f38,f44,f65,f77,f218])).

fof(f218,plain,
    ( ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f200,f15])).

fof(f15,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f200,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,sK1),sK1)
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(superposition,[],[f64,f76])).

fof(f76,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl3_9
  <=> sK1 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f64,plain,
    ( ! [X1] : ~ r1_xboole_0(k4_xboole_0(sK2,sK1),k2_xboole_0(X1,sK0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_8
  <=> ! [X1] : ~ r1_xboole_0(k4_xboole_0(sK2,sK1),k2_xboole_0(X1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f77,plain,
    ( spl3_9
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f72,f41,f74])).

fof(f41,plain,
    ( spl3_4
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f72,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f68,f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f68,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f16,f43])).

fof(f43,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f65,plain,
    ( spl3_8
    | spl3_3 ),
    inference(avatar_split_clause,[],[f57,f35,f63])).

fof(f35,plain,
    ( spl3_3
  <=> r1_xboole_0(k4_xboole_0(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f57,plain,
    ( ! [X1] : ~ r1_xboole_0(k4_xboole_0(sK2,sK1),k2_xboole_0(X1,sK0))
    | spl3_3 ),
    inference(resolution,[],[f21,f37])).

fof(f37,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,sK1),sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f44,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f39,f29,f41])).

fof(f29,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f39,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f18,f31])).

fof(f31,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f38,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f33,f24,f35])).

fof(f24,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f33,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,sK1),sK0)
    | spl3_1 ),
    inference(resolution,[],[f17,f26])).

fof(f26,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f32,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f12,f29])).

fof(f12,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f27,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f13,f24])).

fof(f13,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (14689)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.13/0.42  % (14683)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.43  % (14683)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f219,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f27,f32,f38,f44,f65,f77,f218])).
% 0.20/0.43  fof(f218,plain,(
% 0.20/0.43    ~spl3_8 | ~spl3_9),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f217])).
% 0.20/0.43  fof(f217,plain,(
% 0.20/0.43    $false | (~spl3_8 | ~spl3_9)),
% 0.20/0.43    inference(subsumption_resolution,[],[f200,f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.43  fof(f200,plain,(
% 0.20/0.43    ~r1_xboole_0(k4_xboole_0(sK2,sK1),sK1) | (~spl3_8 | ~spl3_9)),
% 0.20/0.43    inference(superposition,[],[f64,f76])).
% 0.20/0.43  fof(f76,plain,(
% 0.20/0.43    sK1 = k2_xboole_0(sK1,sK0) | ~spl3_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f74])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    spl3_9 <=> sK1 = k2_xboole_0(sK1,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    ( ! [X1] : (~r1_xboole_0(k4_xboole_0(sK2,sK1),k2_xboole_0(X1,sK0))) ) | ~spl3_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f63])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    spl3_8 <=> ! [X1] : ~r1_xboole_0(k4_xboole_0(sK2,sK1),k2_xboole_0(X1,sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    spl3_9 | ~spl3_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f72,f41,f74])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    spl3_4 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    sK1 = k2_xboole_0(sK1,sK0) | ~spl3_4),
% 0.20/0.43    inference(forward_demodulation,[],[f68,f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) | ~spl3_4),
% 0.20/0.43    inference(superposition,[],[f16,f43])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f41])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    spl3_8 | spl3_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f57,f35,f63])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    spl3_3 <=> r1_xboole_0(k4_xboole_0(sK2,sK1),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    ( ! [X1] : (~r1_xboole_0(k4_xboole_0(sK2,sK1),k2_xboole_0(X1,sK0))) ) | spl3_3),
% 0.20/0.43    inference(resolution,[],[f21,f37])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ~r1_xboole_0(k4_xboole_0(sK2,sK1),sK0) | spl3_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f35])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    spl3_4 | ~spl3_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f39,f29,f41])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_2),
% 0.20/0.43    inference(resolution,[],[f18,f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f29])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ~spl3_3 | spl3_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f33,f24,f35])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    spl3_1 <=> r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ~r1_xboole_0(k4_xboole_0(sK2,sK1),sK0) | spl3_1),
% 0.20/0.43    inference(resolution,[],[f17,f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) | spl3_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f24])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    spl3_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f12,f29])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    r1_tarski(sK0,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.20/0.43    inference(negated_conjecture,[],[f7])).
% 0.20/0.43  fof(f7,conjecture,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ~spl3_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f13,f24])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (14683)------------------------------
% 0.20/0.43  % (14683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (14683)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (14683)Memory used [KB]: 10618
% 0.20/0.43  % (14683)Time elapsed: 0.008 s
% 0.20/0.43  % (14683)------------------------------
% 0.20/0.43  % (14683)------------------------------
% 0.20/0.43  % (14681)Success in time 0.074 s
%------------------------------------------------------------------------------
