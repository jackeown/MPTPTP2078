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
% DateTime   : Thu Dec  3 12:32:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  62 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   89 ( 125 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f36,f68,f83,f110,f138,f156,f158])).

fof(f158,plain,
    ( spl2_15
    | ~ spl2_17 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl2_15
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f137,f155])).

fof(f155,plain,
    ( ! [X12,X11] : r1_xboole_0(k5_xboole_0(X11,X12),k3_xboole_0(X11,X12))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl2_17
  <=> ! [X11,X12] : r1_xboole_0(k5_xboole_0(X11,X12),k3_xboole_0(X11,X12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f137,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl2_15
  <=> r1_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f156,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f96,f81,f34,f154])).

fof(f34,plain,
    ( spl2_3
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f81,plain,
    ( spl2_10
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f96,plain,
    ( ! [X12,X11] : r1_xboole_0(k5_xboole_0(X11,X12),k3_xboole_0(X11,X12))
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(superposition,[],[f35,f82])).

fof(f82,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f35,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f138,plain,
    ( ~ spl2_15
    | spl2_1
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f111,f108,f25,f135])).

fof(f25,plain,
    ( spl2_1
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f108,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | ~ r1_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f111,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))
    | spl2_1
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f27,f109])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,X0)
        | r1_xboole_0(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f27,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f110,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f89,f66,f30,f108])).

fof(f30,plain,
    ( spl2_2
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f66,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
        | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | ~ r1_xboole_0(X1,X0) )
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f86,f31])).

fof(f31,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,X0)
        | r1_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) )
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(superposition,[],[f67,f31])).

fof(f67,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        | r1_xboole_0(X1,k4_xboole_0(X0,X2)) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f83,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f20,f81])).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f68,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f23,f66])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f36,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f32,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f28,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f15,f25])).

fof(f15,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f12])).

fof(f12,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))
   => ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:01:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (6745)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (6750)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (6740)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (6745)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f28,f32,f36,f68,f83,f110,f138,f156,f158])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    spl2_15 | ~spl2_17),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f157])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    $false | (spl2_15 | ~spl2_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f137,f155])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ( ! [X12,X11] : (r1_xboole_0(k5_xboole_0(X11,X12),k3_xboole_0(X11,X12))) ) | ~spl2_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f154])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    spl2_17 <=> ! [X11,X12] : r1_xboole_0(k5_xboole_0(X11,X12),k3_xboole_0(X11,X12))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ~r1_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) | spl2_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f135])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    spl2_15 <=> r1_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    spl2_17 | ~spl2_3 | ~spl2_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f96,f81,f34,f154])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    spl2_3 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl2_10 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X12,X11] : (r1_xboole_0(k5_xboole_0(X11,X12),k3_xboole_0(X11,X12))) ) | (~spl2_3 | ~spl2_10)),
% 0.21/0.48    inference(superposition,[],[f35,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl2_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f81])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f34])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ~spl2_15 | spl2_1 | ~spl2_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f111,f108,f25,f135])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    spl2_1 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl2_12 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X1,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ~r1_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) | (spl2_1 | ~spl2_12)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f27,f109])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | r1_xboole_0(X0,X1)) ) | ~spl2_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f108])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) | spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f25])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl2_12 | ~spl2_2 | ~spl2_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f89,f66,f30,f108])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    spl2_2 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl2_9 <=> ! [X1,X0,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X1,X0)) ) | (~spl2_2 | ~spl2_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f86,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f30])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | r1_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0))) ) | (~spl2_2 | ~spl2_9)),
% 0.21/0.48    inference(superposition,[],[f67,f31])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X1,k4_xboole_0(X0,X2))) ) | ~spl2_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f66])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl2_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f81])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl2_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f66])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f34])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f30])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ~spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f15,f25])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) => ~r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_xboole_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (6745)------------------------------
% 0.21/0.48  % (6745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (6745)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (6745)Memory used [KB]: 6140
% 0.21/0.48  % (6745)Time elapsed: 0.052 s
% 0.21/0.48  % (6745)------------------------------
% 0.21/0.48  % (6745)------------------------------
% 0.21/0.48  % (6739)Success in time 0.116 s
%------------------------------------------------------------------------------
