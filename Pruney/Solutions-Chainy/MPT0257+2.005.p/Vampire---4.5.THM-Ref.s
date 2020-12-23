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
% DateTime   : Thu Dec  3 12:40:03 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   53 (  83 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 126 expanded)
%              Number of equality atoms :   44 (  73 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1759,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f138,f1517,f1693])).

fof(f1693,plain,
    ( spl4_1
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f1649,f1514,f57])).

fof(f57,plain,
    ( spl4_1
  <=> k2_tarski(sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1514,plain,
    ( spl4_74
  <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f1649,plain,
    ( k2_tarski(sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))
    | ~ spl4_74 ),
    inference(superposition,[],[f48,f1516])).

fof(f1516,plain,
    ( k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1))
    | ~ spl4_74 ),
    inference(avatar_component_clause,[],[f1514])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f33,f35,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1517,plain,
    ( spl4_74
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f1465,f134,f1514])).

fof(f134,plain,
    ( spl4_11
  <=> sK1 = k2_xboole_0(k2_tarski(sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1465,plain,
    ( k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1))
    | ~ spl4_11 ),
    inference(superposition,[],[f735,f136])).

fof(f136,plain,
    ( sK1 = k2_xboole_0(k2_tarski(sK0,sK0),sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f735,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(forward_demodulation,[],[f700,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f700,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f207,f66])).

fof(f66,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f31,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f31,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f207,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X7),X8))) = k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k4_xboole_0(X6,X8))) ),
    inference(superposition,[],[f55,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f46,f35,f35,f35])).

fof(f46,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f138,plain,
    ( spl4_11
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f130,f62,f134])).

fof(f62,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f130,plain,
    ( sK1 = k2_xboole_0(k2_tarski(sK0,sK0),sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f53,f64])).

fof(f64,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k2_tarski(X0,X0),X1) = X1 ) ),
    inference(definition_unfolding,[],[f42,f32])).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f65,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f29,f62])).

fof(f29,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
        & r2_hidden(X0,X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

fof(f60,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f47,f57])).

fof(f47,plain,(
    k2_tarski(sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0))) ),
    inference(definition_unfolding,[],[f30,f32,f35,f32])).

fof(f30,plain,(
    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:04:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.45  % (2582)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.18/0.46  % (2581)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.18/0.48  % (2590)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.18/0.48  % (2582)Refutation found. Thanks to Tanya!
% 0.18/0.48  % SZS status Theorem for theBenchmark
% 0.18/0.48  % SZS output start Proof for theBenchmark
% 0.18/0.48  fof(f1759,plain,(
% 0.18/0.48    $false),
% 0.18/0.48    inference(avatar_sat_refutation,[],[f60,f65,f138,f1517,f1693])).
% 0.18/0.48  fof(f1693,plain,(
% 0.18/0.48    spl4_1 | ~spl4_74),
% 0.18/0.48    inference(avatar_split_clause,[],[f1649,f1514,f57])).
% 0.18/0.48  fof(f57,plain,(
% 0.18/0.48    spl4_1 <=> k2_tarski(sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.18/0.48  fof(f1514,plain,(
% 0.18/0.48    spl4_74 <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1))),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 0.18/0.48  fof(f1649,plain,(
% 0.18/0.48    k2_tarski(sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0))) | ~spl4_74),
% 0.18/0.48    inference(superposition,[],[f48,f1516])).
% 0.18/0.48  fof(f1516,plain,(
% 0.18/0.48    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)) | ~spl4_74),
% 0.18/0.48    inference(avatar_component_clause,[],[f1514])).
% 0.18/0.48  fof(f48,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.18/0.48    inference(definition_unfolding,[],[f33,f35,f35])).
% 0.18/0.48  fof(f35,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f7])).
% 0.18/0.48  fof(f7,axiom,(
% 0.18/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.18/0.48  fof(f33,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f1])).
% 0.18/0.48  fof(f1,axiom,(
% 0.18/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.18/0.48  fof(f1517,plain,(
% 0.18/0.48    spl4_74 | ~spl4_11),
% 0.18/0.48    inference(avatar_split_clause,[],[f1465,f134,f1514])).
% 0.18/0.48  fof(f134,plain,(
% 0.18/0.48    spl4_11 <=> sK1 = k2_xboole_0(k2_tarski(sK0,sK0),sK1)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.18/0.48  fof(f1465,plain,(
% 0.18/0.48    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)) | ~spl4_11),
% 0.18/0.48    inference(superposition,[],[f735,f136])).
% 0.18/0.48  fof(f136,plain,(
% 0.18/0.48    sK1 = k2_xboole_0(k2_tarski(sK0,sK0),sK1) | ~spl4_11),
% 0.18/0.48    inference(avatar_component_clause,[],[f134])).
% 0.18/0.48  fof(f735,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 0.18/0.48    inference(forward_demodulation,[],[f700,f49])).
% 0.18/0.48  fof(f49,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 0.18/0.48    inference(definition_unfolding,[],[f34,f35])).
% 0.18/0.48  fof(f34,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.18/0.48    inference(cnf_transformation,[],[f4])).
% 0.18/0.48  fof(f4,axiom,(
% 0.18/0.48    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.18/0.48  fof(f700,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))) )),
% 0.18/0.48    inference(superposition,[],[f207,f66])).
% 0.18/0.48  fof(f66,plain,(
% 0.18/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f31,f43])).
% 0.18/0.48  fof(f43,plain,(
% 0.18/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.18/0.48    inference(cnf_transformation,[],[f28])).
% 0.18/0.48  fof(f28,plain,(
% 0.18/0.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.18/0.48    inference(nnf_transformation,[],[f9])).
% 0.18/0.48  fof(f9,axiom,(
% 0.18/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.18/0.48  fof(f31,plain,(
% 0.18/0.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f8])).
% 0.18/0.48  fof(f8,axiom,(
% 0.18/0.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.18/0.48  fof(f207,plain,(
% 0.18/0.48    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X7),X8))) = k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k4_xboole_0(X6,X8)))) )),
% 0.18/0.48    inference(superposition,[],[f55,f50])).
% 0.18/0.48  fof(f50,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.18/0.48    inference(definition_unfolding,[],[f36,f35])).
% 0.18/0.48  fof(f36,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f6])).
% 0.18/0.48  fof(f6,axiom,(
% 0.18/0.48    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.18/0.48  fof(f55,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.18/0.48    inference(definition_unfolding,[],[f46,f35,f35,f35])).
% 0.18/0.48  fof(f46,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f5])).
% 0.18/0.48  fof(f5,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.18/0.48  fof(f138,plain,(
% 0.18/0.48    spl4_11 | ~spl4_2),
% 0.18/0.48    inference(avatar_split_clause,[],[f130,f62,f134])).
% 0.18/0.48  fof(f62,plain,(
% 0.18/0.48    spl4_2 <=> r2_hidden(sK0,sK1)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.18/0.48  fof(f130,plain,(
% 0.18/0.48    sK1 = k2_xboole_0(k2_tarski(sK0,sK0),sK1) | ~spl4_2),
% 0.18/0.48    inference(resolution,[],[f53,f64])).
% 0.18/0.48  fof(f64,plain,(
% 0.18/0.48    r2_hidden(sK0,sK1) | ~spl4_2),
% 0.18/0.48    inference(avatar_component_clause,[],[f62])).
% 0.18/0.48  fof(f53,plain,(
% 0.18/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k2_tarski(X0,X0),X1) = X1) )),
% 0.18/0.48    inference(definition_unfolding,[],[f42,f32])).
% 0.18/0.48  fof(f32,plain,(
% 0.18/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f10])).
% 0.18/0.48  fof(f10,axiom,(
% 0.18/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.18/0.48  fof(f42,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f20])).
% 0.18/0.48  fof(f20,plain,(
% 0.18/0.48    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.18/0.48    inference(ennf_transformation,[],[f11])).
% 0.18/0.48  fof(f11,axiom,(
% 0.18/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.18/0.48  fof(f65,plain,(
% 0.18/0.48    spl4_2),
% 0.18/0.48    inference(avatar_split_clause,[],[f29,f62])).
% 0.18/0.48  fof(f29,plain,(
% 0.18/0.48    r2_hidden(sK0,sK1)),
% 0.18/0.48    inference(cnf_transformation,[],[f23])).
% 0.18/0.48  fof(f23,plain,(
% 0.18/0.48    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 0.18/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f22])).
% 0.18/0.48  fof(f22,plain,(
% 0.18/0.48    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1)) => (k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 0.18/0.48    introduced(choice_axiom,[])).
% 0.18/0.48  fof(f17,plain,(
% 0.18/0.48    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1))),
% 0.18/0.48    inference(ennf_transformation,[],[f14])).
% 0.18/0.48  fof(f14,negated_conjecture,(
% 0.18/0.48    ~! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.18/0.48    inference(negated_conjecture,[],[f13])).
% 0.18/0.48  fof(f13,conjecture,(
% 0.18/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).
% 0.18/0.48  fof(f60,plain,(
% 0.18/0.48    ~spl4_1),
% 0.18/0.48    inference(avatar_split_clause,[],[f47,f57])).
% 0.18/0.48  fof(f47,plain,(
% 0.18/0.48    k2_tarski(sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))),
% 0.18/0.48    inference(definition_unfolding,[],[f30,f32,f35,f32])).
% 0.18/0.48  fof(f30,plain,(
% 0.18/0.48    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.18/0.48    inference(cnf_transformation,[],[f23])).
% 0.18/0.48  % SZS output end Proof for theBenchmark
% 0.18/0.48  % (2582)------------------------------
% 0.18/0.48  % (2582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (2582)Termination reason: Refutation
% 0.18/0.48  
% 0.18/0.48  % (2582)Memory used [KB]: 7419
% 0.18/0.48  % (2582)Time elapsed: 0.041 s
% 0.18/0.48  % (2582)------------------------------
% 0.18/0.48  % (2582)------------------------------
% 0.18/0.49  % (2570)Success in time 0.141 s
%------------------------------------------------------------------------------
