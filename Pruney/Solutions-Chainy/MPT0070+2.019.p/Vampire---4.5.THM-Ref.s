%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:28 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   44 (  67 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 164 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f221,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f65,f194,f210])).

fof(f210,plain,
    ( spl5_1
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f203,f191,f46])).

fof(f46,plain,
    ( spl5_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f191,plain,
    ( spl5_21
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f203,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl5_21 ),
    inference(trivial_inequality_removal,[],[f199])).

fof(f199,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK2)
    | ~ spl5_21 ),
    inference(superposition,[],[f41,f193])).

fof(f193,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f191])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f194,plain,
    ( spl5_21
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f189,f62,f56,f191])).

fof(f56,plain,
    ( spl5_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f62,plain,
    ( spl5_4
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f189,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f173,f58])).

fof(f58,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = k3_xboole_0(X0,sK2) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f171,f32])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f171,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,sK2),k1_xboole_0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f72,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f72,plain,
    ( ! [X0] :
        ( r1_tarski(k3_xboole_0(X0,sK2),k1_xboole_0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl5_4 ),
    inference(superposition,[],[f44,f64])).

fof(f64,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

fof(f65,plain,
    ( spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f60,f51,f62])).

fof(f51,plain,
    ( spl5_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f60,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f53,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f59,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f54,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f29,f51])).

fof(f29,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f30,f46])).

fof(f30,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (15834)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.13/0.41  % (15834)Refutation found. Thanks to Tanya!
% 0.13/0.41  % SZS status Theorem for theBenchmark
% 0.13/0.41  % SZS output start Proof for theBenchmark
% 0.13/0.41  fof(f221,plain,(
% 0.13/0.41    $false),
% 0.13/0.41    inference(avatar_sat_refutation,[],[f49,f54,f59,f65,f194,f210])).
% 0.13/0.41  fof(f210,plain,(
% 0.13/0.41    spl5_1 | ~spl5_21),
% 0.13/0.41    inference(avatar_split_clause,[],[f203,f191,f46])).
% 0.13/0.41  fof(f46,plain,(
% 0.13/0.41    spl5_1 <=> r1_xboole_0(sK0,sK2)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.13/0.41  fof(f191,plain,(
% 0.13/0.41    spl5_21 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.13/0.41  fof(f203,plain,(
% 0.13/0.41    r1_xboole_0(sK0,sK2) | ~spl5_21),
% 0.13/0.41    inference(trivial_inequality_removal,[],[f199])).
% 0.13/0.41  fof(f199,plain,(
% 0.13/0.41    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK2) | ~spl5_21),
% 0.13/0.41    inference(superposition,[],[f41,f193])).
% 0.13/0.41  fof(f193,plain,(
% 0.13/0.41    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl5_21),
% 0.13/0.41    inference(avatar_component_clause,[],[f191])).
% 0.13/0.41  fof(f41,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f26])).
% 0.13/0.41  fof(f26,plain,(
% 0.13/0.41    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.13/0.41    inference(nnf_transformation,[],[f2])).
% 0.13/0.41  fof(f2,axiom,(
% 0.13/0.41    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.13/0.41  fof(f194,plain,(
% 0.13/0.41    spl5_21 | ~spl5_3 | ~spl5_4),
% 0.13/0.41    inference(avatar_split_clause,[],[f189,f62,f56,f191])).
% 0.13/0.41  fof(f56,plain,(
% 0.13/0.41    spl5_3 <=> r1_tarski(sK0,sK1)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.13/0.41  fof(f62,plain,(
% 0.13/0.41    spl5_4 <=> k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.13/0.41  fof(f189,plain,(
% 0.13/0.41    k1_xboole_0 = k3_xboole_0(sK0,sK2) | (~spl5_3 | ~spl5_4)),
% 0.13/0.41    inference(resolution,[],[f173,f58])).
% 0.13/0.41  fof(f58,plain,(
% 0.13/0.41    r1_tarski(sK0,sK1) | ~spl5_3),
% 0.13/0.41    inference(avatar_component_clause,[],[f56])).
% 0.13/0.41  fof(f173,plain,(
% 0.13/0.41    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = k3_xboole_0(X0,sK2)) ) | ~spl5_4),
% 0.13/0.41    inference(forward_demodulation,[],[f171,f32])).
% 0.13/0.41  fof(f32,plain,(
% 0.13/0.41    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.13/0.41    inference(cnf_transformation,[],[f9])).
% 0.13/0.41  fof(f9,axiom,(
% 0.13/0.41    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.13/0.41  fof(f171,plain,(
% 0.13/0.41    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,sK2),k1_xboole_0)) ) | ~spl5_4),
% 0.13/0.41    inference(resolution,[],[f72,f43])).
% 0.13/0.41  fof(f43,plain,(
% 0.13/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f27])).
% 0.13/0.41  fof(f27,plain,(
% 0.13/0.41    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.13/0.41    inference(nnf_transformation,[],[f5])).
% 0.13/0.41  fof(f5,axiom,(
% 0.13/0.41    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.13/0.41  fof(f72,plain,(
% 0.13/0.41    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,sK2),k1_xboole_0) | ~r1_tarski(X0,sK1)) ) | ~spl5_4),
% 0.13/0.41    inference(superposition,[],[f44,f64])).
% 0.13/0.41  fof(f64,plain,(
% 0.13/0.41    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl5_4),
% 0.13/0.41    inference(avatar_component_clause,[],[f62])).
% 0.13/0.41  fof(f44,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f19])).
% 0.13/0.41  fof(f19,plain,(
% 0.13/0.41    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.13/0.41    inference(ennf_transformation,[],[f6])).
% 0.13/0.41  fof(f6,axiom,(
% 0.13/0.41    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).
% 0.13/0.41  fof(f65,plain,(
% 0.13/0.41    spl5_4 | ~spl5_2),
% 0.13/0.41    inference(avatar_split_clause,[],[f60,f51,f62])).
% 0.13/0.41  fof(f51,plain,(
% 0.13/0.41    spl5_2 <=> r1_xboole_0(sK1,sK2)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.13/0.41  fof(f60,plain,(
% 0.13/0.41    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl5_2),
% 0.13/0.41    inference(resolution,[],[f53,f40])).
% 0.13/0.41  fof(f40,plain,(
% 0.13/0.41    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.13/0.41    inference(cnf_transformation,[],[f26])).
% 0.13/0.41  fof(f53,plain,(
% 0.13/0.41    r1_xboole_0(sK1,sK2) | ~spl5_2),
% 0.13/0.41    inference(avatar_component_clause,[],[f51])).
% 0.13/0.41  fof(f59,plain,(
% 0.13/0.41    spl5_3),
% 0.13/0.41    inference(avatar_split_clause,[],[f28,f56])).
% 0.13/0.41  fof(f28,plain,(
% 0.13/0.41    r1_tarski(sK0,sK1)),
% 0.13/0.41    inference(cnf_transformation,[],[f21])).
% 0.13/0.41  fof(f21,plain,(
% 0.13/0.41    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.13/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20])).
% 0.13/0.41  fof(f20,plain,(
% 0.13/0.41    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.13/0.41    introduced(choice_axiom,[])).
% 0.13/0.41  fof(f16,plain,(
% 0.13/0.41    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.13/0.41    inference(flattening,[],[f15])).
% 0.13/0.41  fof(f15,plain,(
% 0.13/0.41    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.13/0.41    inference(ennf_transformation,[],[f13])).
% 0.13/0.41  fof(f13,negated_conjecture,(
% 0.13/0.41    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.13/0.41    inference(negated_conjecture,[],[f12])).
% 0.13/0.41  fof(f12,conjecture,(
% 0.13/0.41    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.13/0.41  fof(f54,plain,(
% 0.13/0.41    spl5_2),
% 0.13/0.41    inference(avatar_split_clause,[],[f29,f51])).
% 0.13/0.41  fof(f29,plain,(
% 0.13/0.41    r1_xboole_0(sK1,sK2)),
% 0.13/0.41    inference(cnf_transformation,[],[f21])).
% 0.13/0.41  fof(f49,plain,(
% 0.13/0.41    ~spl5_1),
% 0.13/0.41    inference(avatar_split_clause,[],[f30,f46])).
% 0.13/0.41  fof(f30,plain,(
% 0.13/0.41    ~r1_xboole_0(sK0,sK2)),
% 0.13/0.41    inference(cnf_transformation,[],[f21])).
% 0.13/0.41  % SZS output end Proof for theBenchmark
% 0.13/0.41  % (15834)------------------------------
% 0.13/0.41  % (15834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.41  % (15834)Termination reason: Refutation
% 0.13/0.41  
% 0.13/0.41  % (15834)Memory used [KB]: 10746
% 0.13/0.41  % (15834)Time elapsed: 0.006 s
% 0.13/0.41  % (15834)------------------------------
% 0.13/0.41  % (15834)------------------------------
% 0.13/0.42  % (15822)Success in time 0.06 s
%------------------------------------------------------------------------------
