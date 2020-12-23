%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 106 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :  118 ( 234 expanded)
%              Number of equality atoms :    5 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f275,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f262,f274])).

fof(f274,plain,
    ( ~ spl2_5
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f271,f41,f36,f31,f100])).

fof(f100,plain,
    ( spl2_5
  <=> r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f31,plain,
    ( spl2_1
  <=> r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_relat_1(sK0),k4_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f36,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f41,plain,
    ( spl2_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f271,plain,
    ( ~ r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f43,f50,f22,f33,f61])).

% (27565)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f61,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k3_relat_1(X3),X4)
      | r1_tarski(k3_relat_1(X3),k4_xboole_0(k3_relat_1(X5),k4_xboole_0(k3_relat_1(X5),X4)))
      | ~ r1_tarski(X3,X5)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f33,plain,
    ( ~ r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_relat_1(sK0),k4_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f50,plain,
    ( ! [X4] : v1_relat_1(k4_xboole_0(X4,k4_xboole_0(X4,sK1)))
    | ~ spl2_2 ),
    inference(superposition,[],[f45,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f24,f24])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f45,plain,
    ( ! [X0] : v1_relat_1(k4_xboole_0(sK1,X0))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f38,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f38,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f43,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f262,plain,
    ( spl2_5
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f261,f41,f36,f100])).

fof(f261,plain,
    ( r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f204,f28])).

fof(f204,plain,
    ( r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),k3_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f38,f22,f55,f21])).

fof(f55,plain,
    ( ! [X0] : v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,sK0)))
    | ~ spl2_3 ),
    inference(superposition,[],[f46,f28])).

fof(f46,plain,
    ( ! [X0] : v1_relat_1(k4_xboole_0(sK0,X0))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f43,f25])).

fof(f44,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

fof(f39,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f36])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f27,f31])).

fof(f27,plain,(
    ~ r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_relat_1(sK0),k4_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f20,f24,f24])).

fof(f20,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (27573)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.45  % (27561)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (27564)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (27566)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (27566)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f275,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f34,f39,f44,f262,f274])).
% 0.21/0.47  fof(f274,plain,(
% 0.21/0.47    ~spl2_5 | spl2_1 | ~spl2_2 | ~spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f271,f41,f36,f31,f100])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    spl2_5 <=> r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    spl2_1 <=> r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_relat_1(sK0),k4_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    spl2_3 <=> v1_relat_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f271,plain,(
% 0.21/0.47    ~r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK1)) | (spl2_1 | ~spl2_2 | ~spl2_3)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f43,f50,f22,f33,f61])).
% 0.21/0.47  % (27565)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (~r1_tarski(k3_relat_1(X3),X4) | r1_tarski(k3_relat_1(X3),k4_xboole_0(k3_relat_1(X5),k4_xboole_0(k3_relat_1(X5),X4))) | ~r1_tarski(X3,X5) | ~v1_relat_1(X5) | ~v1_relat_1(X3)) )),
% 0.21/0.47    inference(resolution,[],[f29,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f26,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ~r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_relat_1(sK0),k4_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))) | spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f31])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X4] : (v1_relat_1(k4_xboole_0(X4,k4_xboole_0(X4,sK1)))) ) | ~spl2_2),
% 0.21/0.47    inference(superposition,[],[f45,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f23,f24,f24])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK1,X0))) ) | ~spl2_2),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f38,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f36])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    v1_relat_1(sK0) | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f41])).
% 0.21/0.47  fof(f262,plain,(
% 0.21/0.47    spl2_5 | ~spl2_2 | ~spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f261,f41,f36,f100])).
% 0.21/0.47  fof(f261,plain,(
% 0.21/0.47    r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK1)) | (~spl2_2 | ~spl2_3)),
% 0.21/0.47    inference(forward_demodulation,[],[f204,f28])).
% 0.21/0.47  fof(f204,plain,(
% 0.21/0.47    r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),k3_relat_1(sK1)) | (~spl2_2 | ~spl2_3)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f38,f22,f55,f21])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,sK0)))) ) | ~spl2_3),
% 0.21/0.47    inference(superposition,[],[f46,f28])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK0,X0))) ) | ~spl2_3),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f43,f25])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f18,f41])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    v1_relat_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f16,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f7])).
% 0.21/0.47  fof(f7,conjecture,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f36])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    v1_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ~spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f31])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ~r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_relat_1(sK0),k4_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))))),
% 0.21/0.47    inference(definition_unfolding,[],[f20,f24,f24])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (27566)------------------------------
% 0.21/0.47  % (27566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (27566)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (27566)Memory used [KB]: 6268
% 0.21/0.47  % (27566)Time elapsed: 0.058 s
% 0.21/0.47  % (27566)------------------------------
% 0.21/0.47  % (27566)------------------------------
% 0.21/0.48  % (27559)Success in time 0.12 s
%------------------------------------------------------------------------------
