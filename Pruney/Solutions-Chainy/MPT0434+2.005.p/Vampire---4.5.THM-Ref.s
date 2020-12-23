%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 (  92 expanded)
%              Number of leaves         :   15 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  123 ( 215 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f132,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f60,f74,f131])).

fof(f131,plain,
    ( ~ spl2_7
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f130,f40,f35,f30,f71])).

fof(f71,plain,
    ( spl2_7
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

% (31913)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f30,plain,
    ( spl2_1
  <=> r1_tarski(k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f35,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f40,plain,
    ( spl2_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f130,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1)))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f129,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f129,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0)))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f128,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f128,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f115,f32])).

fof(f32,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k4_xboole_0(X1,k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,X0)))
        | ~ r1_tarski(X1,k1_relat_1(k2_xboole_0(sK1,k4_xboole_0(sK0,X0)))) )
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f26,f111])).

fof(f111,plain,
    ( ! [X4] : k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(sK0,X4))) = k1_relat_1(k2_xboole_0(sK1,k4_xboole_0(sK0,X4)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f50,f42])).

fof(f42,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(X0,X1))) = k1_relat_1(k2_xboole_0(sK1,k4_xboole_0(X0,X1))) )
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f49,f23])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k2_xboole_0(k4_xboole_0(X0,X1),sK1)) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(X0,X1)))
        | ~ v1_relat_1(X0) )
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f46,f23])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k2_xboole_0(k4_xboole_0(X0,X1),sK1)) = k2_xboole_0(k1_relat_1(k4_xboole_0(X0,X1)),k1_relat_1(sK1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f44,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f44,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(k2_xboole_0(X0,sK1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(sK1)) )
    | ~ spl2_2 ),
    inference(resolution,[],[f37,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

fof(f37,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f74,plain,
    ( spl2_7
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f69,f57,f71])).

fof(f57,plain,
    ( spl2_5
  <=> k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f69,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1)))
    | ~ spl2_5 ),
    inference(superposition,[],[f21,f59])).

fof(f59,plain,
    ( k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f60,plain,
    ( spl2_5
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f48,f40,f35,f57])).

fof(f48,plain,
    ( k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f44,f42])).

fof(f43,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

fof(f38,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f28,f30])).

fof(f28,plain,(
    ~ r1_tarski(k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f27,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f27,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f19,f22])).

fof(f19,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:01:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (31923)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (31923)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f132,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f33,f38,f43,f60,f74,f131])).
% 0.22/0.47  fof(f131,plain,(
% 0.22/0.47    ~spl2_7 | spl2_1 | ~spl2_2 | ~spl2_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f130,f40,f35,f30,f71])).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    spl2_7 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.47  % (31913)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    spl2_1 <=> r1_tarski(k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,sK1)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    spl2_2 <=> v1_relat_1(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    spl2_3 <=> v1_relat_1(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.47  fof(f130,plain,(
% 0.22/0.47    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) | (spl2_1 | ~spl2_2 | ~spl2_3)),
% 0.22/0.47    inference(forward_demodulation,[],[f129,f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.47  fof(f129,plain,(
% 0.22/0.47    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0))) | (spl2_1 | ~spl2_2 | ~spl2_3)),
% 0.22/0.47    inference(forward_demodulation,[],[f128,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.47  fof(f128,plain,(
% 0.22/0.47    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) | (spl2_1 | ~spl2_2 | ~spl2_3)),
% 0.22/0.47    inference(resolution,[],[f115,f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ~r1_tarski(k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,sK1))) | spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f30])).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,X0))) | ~r1_tarski(X1,k1_relat_1(k2_xboole_0(sK1,k4_xboole_0(sK0,X0))))) ) | (~spl2_2 | ~spl2_3)),
% 0.22/0.47    inference(superposition,[],[f26,f111])).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    ( ! [X4] : (k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(sK0,X4))) = k1_relat_1(k2_xboole_0(sK1,k4_xboole_0(sK0,X4)))) ) | (~spl2_2 | ~spl2_3)),
% 0.22/0.47    inference(resolution,[],[f50,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    v1_relat_1(sK0) | ~spl2_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f40])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(X0,X1))) = k1_relat_1(k2_xboole_0(sK1,k4_xboole_0(X0,X1)))) ) | ~spl2_2),
% 0.22/0.47    inference(forward_demodulation,[],[f49,f23])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_relat_1(k2_xboole_0(k4_xboole_0(X0,X1),sK1)) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(X0,X1))) | ~v1_relat_1(X0)) ) | ~spl2_2),
% 0.22/0.47    inference(forward_demodulation,[],[f46,f23])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_relat_1(k2_xboole_0(k4_xboole_0(X0,X1),sK1)) = k2_xboole_0(k1_relat_1(k4_xboole_0(X0,X1)),k1_relat_1(sK1)) | ~v1_relat_1(X0)) ) | ~spl2_2),
% 0.22/0.47    inference(resolution,[],[f44,f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k2_xboole_0(X0,sK1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(sK1))) ) | ~spl2_2),
% 0.22/0.47    inference(resolution,[],[f37,f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    v1_relat_1(sK1) | ~spl2_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f35])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    spl2_7 | ~spl2_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f69,f57,f71])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    spl2_5 <=> k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) | ~spl2_5),
% 0.22/0.47    inference(superposition,[],[f21,f59])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl2_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f57])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    spl2_5 | ~spl2_2 | ~spl2_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f48,f40,f35,f57])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | (~spl2_2 | ~spl2_3)),
% 0.22/0.47    inference(resolution,[],[f44,f42])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    spl2_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f17,f40])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    v1_relat_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f15,f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 0.22/0.47    inference(negated_conjecture,[],[f8])).
% 0.22/0.47  fof(f8,conjecture,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    spl2_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f18,f35])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    v1_relat_1(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ~spl2_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f28,f30])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ~r1_tarski(k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,sK1)))),
% 0.22/0.47    inference(forward_demodulation,[],[f27,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k4_xboole_0(sK0,sK1)))),
% 0.22/0.48    inference(forward_demodulation,[],[f19,f22])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (31923)------------------------------
% 0.22/0.48  % (31923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (31923)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (31923)Memory used [KB]: 10618
% 0.22/0.48  % (31923)Time elapsed: 0.013 s
% 0.22/0.48  % (31923)------------------------------
% 0.22/0.48  % (31923)------------------------------
% 0.22/0.48  % (31911)Success in time 0.116 s
%------------------------------------------------------------------------------
