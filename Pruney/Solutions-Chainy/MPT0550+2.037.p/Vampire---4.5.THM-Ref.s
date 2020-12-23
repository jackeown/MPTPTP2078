%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  76 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 204 expanded)
%              Number of equality atoms :   36 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f41,f46,f54,f61,f68])).

fof(f68,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f66,f32])).

fof(f32,plain,
    ( k1_xboole_0 != sK0
    | spl2_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f66,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f65,f17])).

fof(f17,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f65,plain,
    ( k1_relat_1(k1_xboole_0) = sK0
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f62,f40])).

fof(f40,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_3
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f62,plain,
    ( k1_relat_1(k1_xboole_0) = sK0
    | ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(superposition,[],[f36,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_6
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f36,plain,
    ( ! [X2] :
        ( k1_relat_1(k7_relat_1(sK1,X2)) = X2
        | ~ r1_tarski(X2,k1_relat_1(sK1)) )
    | ~ spl2_1 ),
    inference(resolution,[],[f27,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f27,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f61,plain,
    ( spl2_6
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f56,f51,f25,f58])).

fof(f51,plain,
    ( spl2_5
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f56,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(resolution,[],[f35,f53])).

fof(f53,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f35,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(k1_relat_1(sK1),X1)
        | k1_xboole_0 = k7_relat_1(sK1,X1) )
    | ~ spl2_1 ),
    inference(resolution,[],[f27,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f54,plain,
    ( spl2_5
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f49,f43,f25,f51])).

fof(f43,plain,
    ( spl2_4
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f49,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f48,f27])).

fof(f48,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f47])).

fof(f47,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(superposition,[],[f23,f45])).

fof(f45,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) != k1_xboole_0
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k9_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k9_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f46,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f16,f43])).

fof(f16,plain,(
    k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) = k1_xboole_0
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) = k1_xboole_0
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k9_relat_1(X1,X0) = k1_xboole_0
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k9_relat_1(X1,X0) = k1_xboole_0
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

fof(f41,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f15,f38])).

fof(f15,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f33,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f14,f30])).

fof(f14,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f28,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f13,f25])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:19:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (25096)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (25085)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (25085)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f28,f33,f41,f46,f54,f61,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ~spl2_1 | spl2_2 | ~spl2_3 | ~spl2_6),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    $false | (~spl2_1 | spl2_2 | ~spl2_3 | ~spl2_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f66,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 | spl2_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    spl2_2 <=> k1_xboole_0 = sK0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | (~spl2_1 | ~spl2_3 | ~spl2_6)),
% 0.21/0.48    inference(forward_demodulation,[],[f65,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    k1_relat_1(k1_xboole_0) = sK0 | (~spl2_1 | ~spl2_3 | ~spl2_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f62,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    spl2_3 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    k1_relat_1(k1_xboole_0) = sK0 | ~r1_tarski(sK0,k1_relat_1(sK1)) | (~spl2_1 | ~spl2_6)),
% 0.21/0.48    inference(superposition,[],[f36,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl2_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl2_6 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X2] : (k1_relat_1(k7_relat_1(sK1,X2)) = X2 | ~r1_tarski(X2,k1_relat_1(sK1))) ) | ~spl2_1),
% 0.21/0.48    inference(resolution,[],[f27,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl2_6 | ~spl2_1 | ~spl2_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f56,f51,f25,f58])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl2_5 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl2_1 | ~spl2_5)),
% 0.21/0.48    inference(resolution,[],[f35,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f51])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_xboole_0(k1_relat_1(sK1),X1) | k1_xboole_0 = k7_relat_1(sK1,X1)) ) | ~spl2_1),
% 0.21/0.48    inference(resolution,[],[f27,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl2_5 | ~spl2_1 | ~spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f49,f43,f25,f51])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl2_4 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    r1_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_1 | ~spl2_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f48,f27])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl2_4),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl2_4),
% 0.21/0.48    inference(superposition,[],[f23,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl2_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f43])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k9_relat_1(X1,X0) != k1_xboole_0 | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : ((k9_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (k9_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f43])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1] : (k9_relat_1(X1,X0) = k1_xboole_0 & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0,X1] : ((k9_relat_1(X1,X0) = k1_xboole_0 & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (v1_relat_1(X1) => ~(k9_relat_1(X1,X0) = k1_xboole_0 & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => ~(k9_relat_1(X1,X0) = k1_xboole_0 & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f15,f38])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ~spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f14,f30])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    k1_xboole_0 != sK0),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f13,f25])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (25085)------------------------------
% 0.21/0.48  % (25085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (25085)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (25085)Memory used [KB]: 10618
% 0.21/0.48  % (25085)Time elapsed: 0.054 s
% 0.21/0.48  % (25085)------------------------------
% 0.21/0.48  % (25085)------------------------------
% 0.21/0.48  % (25081)Success in time 0.12 s
%------------------------------------------------------------------------------
