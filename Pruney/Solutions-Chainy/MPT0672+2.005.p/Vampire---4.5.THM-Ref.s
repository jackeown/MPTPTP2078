%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 101 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  138 ( 267 expanded)
%              Number of equality atoms :   51 (  94 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f56,f64,f76,f109,f138])).

fof(f138,plain,
    ( spl3_2
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f137,f106,f53,f38])).

fof(f38,plain,
    ( spl3_2
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f53,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f106,plain,
    ( spl3_7
  <=> k8_relat_1(sK0,k6_relat_1(sK1)) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f137,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f131,f65])).

fof(f65,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f55,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f55,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f131,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k5_relat_1(sK2,k6_relat_1(sK0))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(superposition,[],[f84,f108])).

fof(f108,plain,
    ( k8_relat_1(sK0,k6_relat_1(sK1)) = k6_relat_1(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f84,plain,
    ( ! [X0,X1] : k5_relat_1(sK2,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k8_relat_1(X1,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f79,f65])).

fof(f79,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k5_relat_1(sK2,k6_relat_1(X1))) = k5_relat_1(sK2,k8_relat_1(X0,k6_relat_1(X1)))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f55,f23,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f109,plain,
    ( spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f96,f60,f106])).

fof(f60,plain,
    ( spl3_6
  <=> sK0 = k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f96,plain,
    ( k8_relat_1(sK0,k6_relat_1(sK1)) = k6_relat_1(sK0)
    | ~ spl3_6 ),
    inference(superposition,[],[f95,f62])).

fof(f62,plain,
    ( sK0 = k1_setfam_1(k2_tarski(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f95,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k2_tarski(X0,X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(backward_demodulation,[],[f31,f66])).

fof(f66,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(unit_resulting_resolution,[],[f23,f27])).

fof(f31,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f26,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f76,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f69,f53,f43,f34])).

fof(f34,plain,
    ( spl3_1
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f43,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f69,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f55,f45,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(f45,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f64,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f58,f43,f60])).

fof(f58,plain,
    ( sK0 = k1_setfam_1(k2_tarski(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f32,f45])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f29,f25])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f56,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f53])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
      | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) )
    & r1_tarski(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
          | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
        & r1_tarski(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
        | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) )
      & r1_tarski(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r1_tarski(X0,X1)
         => ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
            & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
          & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_funct_1)).

fof(f46,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f43])).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f22,f38,f34])).

fof(f22,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
    | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:26:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (25560)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.44  % (25560)Refutation not found, incomplete strategy% (25560)------------------------------
% 0.21/0.44  % (25560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (25560)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (25560)Memory used [KB]: 10618
% 0.21/0.44  % (25560)Time elapsed: 0.007 s
% 0.21/0.44  % (25560)------------------------------
% 0.21/0.44  % (25560)------------------------------
% 0.21/0.46  % (25554)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (25554)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f139,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f41,f46,f56,f64,f76,f109,f138])).
% 0.21/0.46  fof(f138,plain,(
% 0.21/0.46    spl3_2 | ~spl3_5 | ~spl3_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f137,f106,f53,f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    spl3_2 <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    spl3_5 <=> v1_relat_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    spl3_7 <=> k8_relat_1(sK0,k6_relat_1(sK1)) = k6_relat_1(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.46  fof(f137,plain,(
% 0.21/0.46    k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) | (~spl3_5 | ~spl3_7)),
% 0.21/0.46    inference(forward_demodulation,[],[f131,f65])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) ) | ~spl3_5),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f55,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    v1_relat_1(sK2) | ~spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f53])).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k5_relat_1(sK2,k6_relat_1(sK0)) | (~spl3_5 | ~spl3_7)),
% 0.21/0.46    inference(superposition,[],[f84,f108])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    k8_relat_1(sK0,k6_relat_1(sK1)) = k6_relat_1(sK0) | ~spl3_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f106])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k5_relat_1(sK2,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k8_relat_1(X1,sK2))) ) | ~spl3_5),
% 0.21/0.46    inference(forward_demodulation,[],[f79,f65])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k8_relat_1(X0,k5_relat_1(sK2,k6_relat_1(X1))) = k5_relat_1(sK2,k8_relat_1(X0,k6_relat_1(X1)))) ) | ~spl3_5),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f55,f23,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    spl3_7 | ~spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f96,f60,f106])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    spl3_6 <=> sK0 = k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    k8_relat_1(sK0,k6_relat_1(sK1)) = k6_relat_1(sK0) | ~spl3_6),
% 0.21/0.46    inference(superposition,[],[f95,f62])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    sK0 = k1_setfam_1(k2_tarski(sK0,sK1)) | ~spl3_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f60])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k2_tarski(X0,X1))) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.21/0.46    inference(backward_demodulation,[],[f31,f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f23,f27])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f26,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    spl3_1 | ~spl3_3 | ~spl3_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f69,f53,f43,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    spl3_1 <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | (~spl3_3 | ~spl3_5)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f55,f45,f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f43])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl3_6 | ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f58,f43,f60])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    sK0 = k1_setfam_1(k2_tarski(sK0,sK1)) | ~spl3_3),
% 0.21/0.47    inference(resolution,[],[f32,f45])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.21/0.47    inference(definition_unfolding,[],[f29,f25])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f53])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    v1_relat_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    (k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))) & r1_tarski(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))) & r1_tarski(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => ((k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))) & r1_tarski(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))) & r1_tarski(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (((k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))) & r1_tarski(X0,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f8])).
% 0.21/0.47  fof(f8,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_funct_1)).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f21,f43])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    r1_tarski(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ~spl3_1 | ~spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f38,f34])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (25554)------------------------------
% 0.21/0.47  % (25554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (25554)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (25554)Memory used [KB]: 6140
% 0.21/0.47  % (25554)Time elapsed: 0.047 s
% 0.21/0.47  % (25554)------------------------------
% 0.21/0.47  % (25554)------------------------------
% 0.21/0.47  % (25543)Success in time 0.108 s
%------------------------------------------------------------------------------
