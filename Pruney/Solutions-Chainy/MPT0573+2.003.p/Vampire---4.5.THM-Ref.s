%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 (  73 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 139 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f284,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f281,f283])).

fof(f283,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl3_2
    | spl3_3 ),
    inference(resolution,[],[f280,f40])).

fof(f40,plain,
    ( ! [X8,X7] : r1_tarski(k10_relat_1(sK2,X7),k10_relat_1(sK2,k2_xboole_0(X7,X8)))
    | ~ spl3_2 ),
    inference(superposition,[],[f16,f34])).

fof(f34,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ spl3_2 ),
    inference(resolution,[],[f32,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f32,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f280,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl3_3
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f281,plain,
    ( ~ spl3_3
    | spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f276,f30,f25,f278])).

fof(f25,plain,
    ( spl3_1
  <=> r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f276,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))
    | spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f275,f57])).

fof(f57,plain,
    ( ! [X2,X3] : k10_relat_1(sK2,k2_xboole_0(X2,X3)) = k10_relat_1(sK2,k2_xboole_0(X3,X2))
    | ~ spl3_2 ),
    inference(superposition,[],[f35,f34])).

fof(f35,plain,
    ( ! [X2,X3] : k2_xboole_0(k10_relat_1(sK2,X3),k10_relat_1(sK2,X2)) = k10_relat_1(sK2,k2_xboole_0(X2,X3))
    | ~ spl3_2 ),
    inference(superposition,[],[f34,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f275,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,sK0)))
    | spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f266,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f266,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))))
    | spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f37,f27])).

fof(f27,plain,
    ( ~ r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f37,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k4_xboole_0(X2,k10_relat_1(sK2,X0)),k10_relat_1(sK2,X1))
        | ~ r1_tarski(X2,k10_relat_1(sK2,k2_xboole_0(X0,X1))) )
    | ~ spl3_2 ),
    inference(superposition,[],[f21,f34])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f30])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_relat_1)).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f25])).

fof(f23,plain,(
    ~ r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f22,f17])).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f22,plain,(
    ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f15,f17])).

fof(f15,plain,(
    ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:38:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.44  % (30119)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.45  % (30119)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f284,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f28,f33,f281,f283])).
% 0.22/0.45  fof(f283,plain,(
% 0.22/0.45    ~spl3_2 | spl3_3),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f282])).
% 0.22/0.45  fof(f282,plain,(
% 0.22/0.45    $false | (~spl3_2 | spl3_3)),
% 0.22/0.45    inference(resolution,[],[f280,f40])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ( ! [X8,X7] : (r1_tarski(k10_relat_1(sK2,X7),k10_relat_1(sK2,k2_xboole_0(X7,X8)))) ) | ~spl3_2),
% 0.22/0.45    inference(superposition,[],[f16,f34])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | ~spl3_2),
% 0.22/0.45    inference(resolution,[],[f32,f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    v1_relat_1(sK2) | ~spl3_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f30])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    spl3_2 <=> v1_relat_1(sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.45  fof(f280,plain,(
% 0.22/0.45    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))) | spl3_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f278])).
% 0.22/0.45  fof(f278,plain,(
% 0.22/0.45    spl3_3 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.45  fof(f281,plain,(
% 0.22/0.45    ~spl3_3 | spl3_1 | ~spl3_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f276,f30,f25,f278])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    spl3_1 <=> r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.45  fof(f276,plain,(
% 0.22/0.45    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))) | (spl3_1 | ~spl3_2)),
% 0.22/0.45    inference(forward_demodulation,[],[f275,f57])).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    ( ! [X2,X3] : (k10_relat_1(sK2,k2_xboole_0(X2,X3)) = k10_relat_1(sK2,k2_xboole_0(X3,X2))) ) | ~spl3_2),
% 0.22/0.45    inference(superposition,[],[f35,f34])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    ( ! [X2,X3] : (k2_xboole_0(k10_relat_1(sK2,X3),k10_relat_1(sK2,X2)) = k10_relat_1(sK2,k2_xboole_0(X2,X3))) ) | ~spl3_2),
% 0.22/0.45    inference(superposition,[],[f34,f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.45  fof(f275,plain,(
% 0.22/0.45    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,sK0))) | (spl3_1 | ~spl3_2)),
% 0.22/0.45    inference(forward_demodulation,[],[f266,f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.45  fof(f266,plain,(
% 0.22/0.45    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) | (spl3_1 | ~spl3_2)),
% 0.22/0.45    inference(resolution,[],[f37,f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ~r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k4_xboole_0(sK0,sK1))) | spl3_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f25])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,k10_relat_1(sK2,X0)),k10_relat_1(sK2,X1)) | ~r1_tarski(X2,k10_relat_1(sK2,k2_xboole_0(X0,X1)))) ) | ~spl3_2),
% 0.22/0.45    inference(superposition,[],[f21,f34])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    spl3_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f14,f30])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    v1_relat_1(sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2)) => (~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.22/0.45    inference(negated_conjecture,[],[f7])).
% 0.22/0.45  fof(f7,conjecture,(
% 0.22/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_relat_1)).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ~spl3_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f23,f25])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ~r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))),
% 0.22/0.45    inference(forward_demodulation,[],[f22,f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))),
% 0.22/0.45    inference(forward_demodulation,[],[f15,f17])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (30119)------------------------------
% 0.22/0.45  % (30119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (30119)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (30119)Memory used [KB]: 10746
% 0.22/0.45  % (30119)Time elapsed: 0.035 s
% 0.22/0.45  % (30119)------------------------------
% 0.22/0.45  % (30119)------------------------------
% 0.22/0.45  % (30107)Success in time 0.089 s
%------------------------------------------------------------------------------
