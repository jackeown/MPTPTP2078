%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 (  57 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :   75 ( 114 expanded)
%              Number of equality atoms :   37 (  68 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f57])).

fof(f57,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f55,f45])).

fof(f45,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f22,f34])).

fof(f34,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f22,plain,(
    ! [X1] : ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f55,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f53])).

fof(f53,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f21,f52])).

fof(f52,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f18,f47])).

fof(f47,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f19,f42])).

fof(f42,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK1))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f14,f34])).

fof(f14,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f41,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f40])).

fof(f40,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f38,f15])).

fof(f15,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,
    ( sK0 = sK1
    | spl2_1 ),
    inference(resolution,[],[f30,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f30,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_1
  <=> r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f36,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f24,f32,f28])).

fof(f24,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f20,f14])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (28062)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.45  % (28062)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f36,f41,f57])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    ~spl2_2),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f56])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    $false | ~spl2_2),
% 0.22/0.47    inference(subsumption_resolution,[],[f55,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 0.22/0.47    inference(superposition,[],[f22,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    k1_xboole_0 = k1_tarski(sK0) | ~spl2_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    spl2_2 <=> k1_xboole_0 = k1_tarski(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X1] : (~r1_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.22/0.47    inference(equality_resolution,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f53])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 0.22/0.47    inference(superposition,[],[f21,f52])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 0.22/0.47    inference(superposition,[],[f18,f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 0.22/0.47    inference(superposition,[],[f19,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK1)) | ~spl2_2),
% 0.22/0.47    inference(backward_demodulation,[],[f14,f34])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.22/0.47    inference(negated_conjecture,[],[f6])).
% 0.22/0.47  fof(f6,conjecture,(
% 0.22/0.47    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.47    inference(nnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    spl2_1),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f40])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    $false | spl2_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f38,f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    sK0 != sK1),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    sK0 = sK1 | spl2_1),
% 0.22/0.47    inference(resolution,[],[f30,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    spl2_1 <=> r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ~spl2_1 | spl2_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f24,f32,f28])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    k1_xboole_0 = k1_tarski(sK0) | ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.47    inference(superposition,[],[f20,f14])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (28062)------------------------------
% 0.22/0.47  % (28062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (28062)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (28062)Memory used [KB]: 6140
% 0.22/0.47  % (28062)Time elapsed: 0.032 s
% 0.22/0.47  % (28062)------------------------------
% 0.22/0.47  % (28062)------------------------------
% 0.22/0.47  % (28042)Success in time 0.108 s
%------------------------------------------------------------------------------
