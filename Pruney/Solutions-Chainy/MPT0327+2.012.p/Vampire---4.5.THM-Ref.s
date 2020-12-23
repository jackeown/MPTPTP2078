%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 136 expanded)
%              Number of leaves         :   15 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 194 expanded)
%              Number of equality atoms :   49 ( 125 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f97,f112,f116])).

fof(f116,plain,
    ( ~ spl2_5
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f115,f94,f37,f109])).

fof(f109,plain,
    ( spl2_5
  <=> sK1 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f37,plain,
    ( spl2_1
  <=> sK1 = k3_tarski(k2_enumset1(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f94,plain,
    ( spl2_3
  <=> sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f115,plain,
    ( sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))))
    | spl2_1
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f114,f96])).

fof(f96,plain,
    ( sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f114,plain,
    ( sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))))))
    | spl2_1 ),
    inference(forward_demodulation,[],[f113,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f113,plain,
    ( sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))))
    | spl2_1 ),
    inference(forward_demodulation,[],[f39,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f20,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f39,plain,
    ( sK1 != k3_tarski(k2_enumset1(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f112,plain,
    ( spl2_5
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f107,f94,f109])).

fof(f107,plain,
    ( sK1 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f106,f96])).

fof(f106,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f100,f33])).

fof(f100,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))))
    | ~ spl2_3 ),
    inference(superposition,[],[f49,f96])).

fof(f49,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))))))) ),
    inference(forward_demodulation,[],[f34,f26])).

fof(f34,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k2_enumset1(X1,X1,X1,X0)))))) ),
    inference(definition_unfolding,[],[f24,f28,f30,f28])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f22,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f25,f28])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f21,f23])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f97,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f92,f42,f94])).

fof(f42,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f92,plain,
    ( sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f90,f33])).

fof(f90,plain,
    ( sK1 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f44,f44,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X0,X0,X0,X2),k2_enumset1(X0,X0,X0,X2),X1)) = X1 ) ),
    inference(definition_unfolding,[],[f27,f28,f23])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f44,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f45,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f42])).

fof(f17,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f40,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f32,f37])).

fof(f32,plain,(
    sK1 != k3_tarski(k2_enumset1(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f18,f28,f30,f31,f31])).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f18,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.43  % (13483)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.45  % (13477)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.45  % (13477)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f40,f45,f97,f112,f116])).
% 0.21/0.45  fof(f116,plain,(
% 0.21/0.45    ~spl2_5 | spl2_1 | ~spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f115,f94,f37,f109])).
% 0.21/0.45  fof(f109,plain,(
% 0.21/0.45    spl2_5 <=> sK1 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    spl2_1 <=> sK1 = k3_tarski(k2_enumset1(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    spl2_3 <=> sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))))) | (spl2_1 | ~spl2_3)),
% 0.21/0.45    inference(forward_demodulation,[],[f114,f96])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl2_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f94])).
% 0.21/0.45  fof(f114,plain,(
% 0.21/0.45    sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))))) | spl2_1),
% 0.21/0.45    inference(forward_demodulation,[],[f113,f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))))) | spl2_1),
% 0.21/0.45    inference(forward_demodulation,[],[f39,f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f20,f23,f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    sK1 != k3_tarski(k2_enumset1(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k2_enumset1(sK0,sK0,sK0,sK0))) | spl2_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f37])).
% 0.21/0.45  fof(f112,plain,(
% 0.21/0.45    spl2_5 | ~spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f107,f94,f109])).
% 0.21/0.45  fof(f107,plain,(
% 0.21/0.45    sK1 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))))) | ~spl2_3),
% 0.21/0.45    inference(forward_demodulation,[],[f106,f96])).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))))) | ~spl2_3),
% 0.21/0.45    inference(forward_demodulation,[],[f100,f33])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))))) | ~spl2_3),
% 0.21/0.45    inference(superposition,[],[f49,f96])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0)))))))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f34,f26])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k2_enumset1(X1,X1,X1,X0))))))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f24,f28,f30,f28])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f22,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f25,f28])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f21,f23])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    spl2_3 | ~spl2_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f92,f42,f94])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    spl2_2 <=> r2_hidden(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl2_2),
% 0.21/0.45    inference(forward_demodulation,[],[f90,f33])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    sK1 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~spl2_2),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f44,f44,f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,X1) | k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X0,X0,X0,X2),k2_enumset1(X0,X0,X0,X2),X1)) = X1) )),
% 0.21/0.45    inference(definition_unfolding,[],[f27,f28,f23])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    r2_hidden(sK0,sK1) | ~spl2_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f42])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    spl2_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f17,f42])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    r2_hidden(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.45    inference(negated_conjecture,[],[f10])).
% 0.21/0.45  fof(f10,conjecture,(
% 0.21/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ~spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f32,f37])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    sK1 != k3_tarski(k2_enumset1(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.21/0.45    inference(definition_unfolding,[],[f18,f28,f30,f31,f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f19,f23])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (13477)------------------------------
% 0.21/0.45  % (13477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (13477)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (13477)Memory used [KB]: 6268
% 0.21/0.45  % (13477)Time elapsed: 0.008 s
% 0.21/0.45  % (13477)------------------------------
% 0.21/0.45  % (13477)------------------------------
% 0.21/0.46  % (13470)Success in time 0.095 s
%------------------------------------------------------------------------------
