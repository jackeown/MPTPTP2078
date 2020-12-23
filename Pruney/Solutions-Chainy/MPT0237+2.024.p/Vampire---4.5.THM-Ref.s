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
% DateTime   : Thu Dec  3 12:37:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 160 expanded)
%              Number of leaves         :   15 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  107 ( 216 expanded)
%              Number of equality atoms :   69 ( 165 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f446,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f417,f430,f444])).

fof(f444,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f443])).

fof(f443,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f436,f440])).

fof(f440,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f434,f30])).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f434,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f431,f85])).

fof(f85,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f59,f84])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f78,f28])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f78,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f37,f63])).

fof(f63,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f58,f29])).

fof(f29,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f58,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f36,f28])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f59,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f36,f31])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f431,plain,
    ( k2_tarski(sK0,sK0) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f415,f412])).

fof(f412,plain,
    ( sK0 = sK1
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f410])).

fof(f410,plain,
    ( spl2_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f415,plain,
    ( k2_tarski(sK0,sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f414])).

fof(f414,plain,
    ( spl2_2
  <=> k2_tarski(sK0,sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f436,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f435,f434])).

fof(f435,plain,
    ( k1_tarski(sK0) != k2_tarski(sK0,sK0)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f432,f90])).

fof(f90,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = X1 ),
    inference(forward_demodulation,[],[f88,f29])).

fof(f88,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f35,f84])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f432,plain,
    ( k2_tarski(sK0,sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl2_1 ),
    inference(backward_demodulation,[],[f55,f412])).

fof(f55,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f27,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f27,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).

fof(f24,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

fof(f430,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f429])).

fof(f429,plain,
    ( $false
    | spl2_2 ),
    inference(trivial_inequality_removal,[],[f428])).

fof(f428,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | spl2_2 ),
    inference(superposition,[],[f424,f30])).

fof(f424,plain,
    ( k1_tarski(sK0) != k2_tarski(sK0,sK0)
    | spl2_2 ),
    inference(forward_demodulation,[],[f421,f90])).

fof(f421,plain,
    ( k2_tarski(sK0,sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | spl2_2 ),
    inference(backward_demodulation,[],[f55,f419])).

fof(f419,plain,
    ( sK0 = sK1
    | spl2_2 ),
    inference(trivial_inequality_removal,[],[f418])).

fof(f418,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | sK0 = sK1
    | spl2_2 ),
    inference(superposition,[],[f416,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f416,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f414])).

fof(f417,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f407,f414,f410])).

fof(f407,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK0 = sK1 ),
    inference(superposition,[],[f55,f105])).

fof(f105,plain,(
    ! [X4,X3] :
      ( k2_xboole_0(k1_tarski(X4),k1_tarski(X3)) = k5_xboole_0(k1_tarski(X4),k1_tarski(X3))
      | X3 = X4 ) ),
    inference(superposition,[],[f35,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f40,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (13477)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.44  % (13486)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.45  % (13486)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.46  % (13483)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f446,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f417,f430,f444])).
% 0.21/0.46  fof(f444,plain,(
% 0.21/0.46    ~spl2_1 | ~spl2_2),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f443])).
% 0.21/0.46  fof(f443,plain,(
% 0.21/0.46    $false | (~spl2_1 | ~spl2_2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f436,f440])).
% 0.21/0.46  fof(f440,plain,(
% 0.21/0.46    k1_xboole_0 = k1_tarski(sK0) | (~spl2_1 | ~spl2_2)),
% 0.21/0.46    inference(superposition,[],[f434,f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.46  fof(f434,plain,(
% 0.21/0.46    k1_xboole_0 = k2_tarski(sK0,sK0) | (~spl2_1 | ~spl2_2)),
% 0.21/0.46    inference(forward_demodulation,[],[f431,f85])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 0.21/0.46    inference(backward_demodulation,[],[f59,f84])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f78,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.21/0.46    inference(superposition,[],[f37,f63])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.46    inference(forward_demodulation,[],[f58,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.46    inference(superposition,[],[f36,f28])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ( ! [X1] : (k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)) )),
% 0.21/0.46    inference(superposition,[],[f36,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.46    inference(rectify,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.46  fof(f431,plain,(
% 0.21/0.46    k2_tarski(sK0,sK0) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | (~spl2_1 | ~spl2_2)),
% 0.21/0.46    inference(backward_demodulation,[],[f415,f412])).
% 0.21/0.46  fof(f412,plain,(
% 0.21/0.46    sK0 = sK1 | ~spl2_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f410])).
% 0.21/0.46  fof(f410,plain,(
% 0.21/0.46    spl2_1 <=> sK0 = sK1),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.46  fof(f415,plain,(
% 0.21/0.46    k2_tarski(sK0,sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl2_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f414])).
% 0.21/0.46  fof(f414,plain,(
% 0.21/0.46    spl2_2 <=> k2_tarski(sK0,sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.46  fof(f436,plain,(
% 0.21/0.46    k1_xboole_0 != k1_tarski(sK0) | (~spl2_1 | ~spl2_2)),
% 0.21/0.46    inference(forward_demodulation,[],[f435,f434])).
% 0.21/0.47  fof(f435,plain,(
% 0.21/0.47    k1_tarski(sK0) != k2_tarski(sK0,sK0) | ~spl2_1),
% 0.21/0.47    inference(forward_demodulation,[],[f432,f90])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ( ! [X1] : (k2_xboole_0(X1,X1) = X1) )),
% 0.21/0.47    inference(forward_demodulation,[],[f88,f29])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ( ! [X1] : (k2_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0)) )),
% 0.21/0.47    inference(superposition,[],[f35,f84])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.47  fof(f432,plain,(
% 0.21/0.47    k2_tarski(sK0,sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | ~spl2_1),
% 0.21/0.47    inference(backward_demodulation,[],[f55,f412])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.47    inference(superposition,[],[f27,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f18])).
% 0.21/0.47  fof(f18,conjecture,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 0.21/0.47  fof(f430,plain,(
% 0.21/0.47    spl2_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f429])).
% 0.21/0.47  fof(f429,plain,(
% 0.21/0.47    $false | spl2_2),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f428])).
% 0.21/0.47  fof(f428,plain,(
% 0.21/0.47    k1_tarski(sK0) != k1_tarski(sK0) | spl2_2),
% 0.21/0.47    inference(superposition,[],[f424,f30])).
% 0.21/0.47  fof(f424,plain,(
% 0.21/0.47    k1_tarski(sK0) != k2_tarski(sK0,sK0) | spl2_2),
% 0.21/0.47    inference(forward_demodulation,[],[f421,f90])).
% 0.21/0.47  fof(f421,plain,(
% 0.21/0.47    k2_tarski(sK0,sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | spl2_2),
% 0.21/0.47    inference(backward_demodulation,[],[f55,f419])).
% 0.21/0.47  fof(f419,plain,(
% 0.21/0.47    sK0 = sK1 | spl2_2),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f418])).
% 0.21/0.47  fof(f418,plain,(
% 0.21/0.47    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | sK0 = sK1 | spl2_2),
% 0.21/0.47    inference(superposition,[],[f416,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.21/0.47    inference(ennf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,axiom,(
% 0.21/0.47    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 0.21/0.47  fof(f416,plain,(
% 0.21/0.47    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f414])).
% 0.21/0.47  fof(f417,plain,(
% 0.21/0.47    spl2_1 | ~spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f407,f414,f410])).
% 0.21/0.47  fof(f407,plain,(
% 0.21/0.47    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | sK0 = sK1),
% 0.21/0.47    inference(superposition,[],[f55,f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ( ! [X4,X3] : (k2_xboole_0(k1_tarski(X4),k1_tarski(X3)) = k5_xboole_0(k1_tarski(X4),k1_tarski(X3)) | X3 = X4) )),
% 0.21/0.47    inference(superposition,[],[f35,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.47    inference(resolution,[],[f40,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.21/0.47    inference(ennf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,axiom,(
% 0.21/0.47    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (13486)------------------------------
% 0.21/0.47  % (13486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (13486)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (13486)Memory used [KB]: 6396
% 0.21/0.47  % (13486)Time elapsed: 0.059 s
% 0.21/0.47  % (13486)------------------------------
% 0.21/0.47  % (13486)------------------------------
% 0.21/0.47  % (13468)Success in time 0.109 s
%------------------------------------------------------------------------------
