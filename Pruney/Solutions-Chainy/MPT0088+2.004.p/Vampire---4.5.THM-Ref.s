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
% DateTime   : Thu Dec  3 12:31:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  84 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 144 expanded)
%              Number of equality atoms :   31 (  51 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f637,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f57,f96,f168,f617])).

fof(f617,plain,
    ( ~ spl3_10
    | spl3_4 ),
    inference(avatar_split_clause,[],[f616,f54,f163])).

fof(f163,plain,
    ( spl3_10
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f54,plain,
    ( spl3_4
  <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f616,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | spl3_4 ),
    inference(forward_demodulation,[],[f615,f107])).

fof(f107,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5))) ),
    inference(superposition,[],[f23,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f615,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_4 ),
    inference(forward_demodulation,[],[f598,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f598,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))))
    | spl3_4 ),
    inference(resolution,[],[f113,f56])).

fof(f56,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k4_xboole_0(X0,X1),X2)
      | k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) ) ),
    inference(forward_demodulation,[],[f106,f28])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2)))
      | r1_xboole_0(k4_xboole_0(X0,X1),X2) ) ),
    inference(superposition,[],[f29,f28])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f168,plain,
    ( spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f167,f92,f163])).

fof(f92,plain,
    ( spl3_8
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f167,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f152,f21])).

fof(f152,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))
    | ~ spl3_8 ),
    inference(superposition,[],[f115,f94])).

fof(f94,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f115,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(forward_demodulation,[],[f31,f28])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f27,f22,f22])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f96,plain,
    ( spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f81,f38,f92])).

fof(f38,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f81,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_2 ),
    inference(resolution,[],[f30,f40])).

fof(f40,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f25,f22])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,
    ( ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f43,f33,f54])).

fof(f33,plain,
    ( spl3_1
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f43,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f35,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f35,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f41,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f38])).

fof(f17,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f36,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f33])).

fof(f18,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:26:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (5501)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (5511)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (5510)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (5500)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (5503)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (5505)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (5508)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (5504)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (5512)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (5514)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (5513)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (5505)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (5506)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (5502)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f637,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f36,f41,f57,f96,f168,f617])).
% 0.21/0.52  fof(f617,plain,(
% 0.21/0.52    ~spl3_10 | spl3_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f616,f54,f163])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    spl3_10 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl3_4 <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f616,plain,(
% 0.21/0.52    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | spl3_4),
% 0.21/0.52    inference(forward_demodulation,[],[f615,f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5)))) )),
% 0.21/0.52    inference(superposition,[],[f23,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.52  fof(f615,plain,(
% 0.21/0.52    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))) | spl3_4),
% 0.21/0.52    inference(forward_demodulation,[],[f598,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.52  fof(f598,plain,(
% 0.21/0.52    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)))) | spl3_4),
% 0.21/0.52    inference(resolution,[],[f113,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f54])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X2) | k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f106,f28])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 != k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) | r1_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.52    inference(superposition,[],[f29,f28])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f26,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    spl3_10 | ~spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f167,f92,f163])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    spl3_8 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | ~spl3_8),
% 0.21/0.52    inference(forward_demodulation,[],[f152,f21])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) | ~spl3_8),
% 0.21/0.52    inference(superposition,[],[f115,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f92])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f31,f28])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f27,f22,f22])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl3_8 | ~spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f81,f38,f92])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    spl3_2 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_2),
% 0.21/0.52    inference(resolution,[],[f30,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f38])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f25,f22])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ~spl3_4 | spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f43,f33,f54])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    spl3_1 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | spl3_1),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f35,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f33])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f17,f38])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ~spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f18,f33])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (5505)------------------------------
% 0.21/0.52  % (5505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5505)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (5505)Memory used [KB]: 6524
% 0.21/0.52  % (5505)Time elapsed: 0.084 s
% 0.21/0.52  % (5505)------------------------------
% 0.21/0.52  % (5505)------------------------------
% 0.21/0.52  % (5498)Success in time 0.156 s
%------------------------------------------------------------------------------
