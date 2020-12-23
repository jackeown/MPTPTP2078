%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 115 expanded)
%              Number of leaves         :   17 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  190 ( 328 expanded)
%              Number of equality atoms :   56 ( 115 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f80,f92,f101,f106,f118,f132,f140])).

fof(f140,plain,
    ( spl2_2
    | ~ spl2_16 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl2_2
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f136,f43])).

fof(f43,plain,
    ( k1_xboole_0 != sK0
    | spl2_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f136,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_16 ),
    inference(superposition,[],[f55,f131])).

fof(f131,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK0)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl2_16
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f26,f33])).

fof(f33,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f132,plain,
    ( spl2_16
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f123,f115,f129])).

fof(f115,plain,
    ( spl2_14
  <=> r1_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f123,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK0)
    | ~ spl2_14 ),
    inference(resolution,[],[f117,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f117,plain,
    ( r1_xboole_0(sK0,sK0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f115])).

fof(f118,plain,
    ( spl2_14
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f109,f103,f99,f115])).

fof(f99,plain,
    ( spl2_11
  <=> ! [X2] :
        ( r1_xboole_0(sK0,X2)
        | k1_xboole_0 != k3_xboole_0(k2_relat_1(sK1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f103,plain,
    ( spl2_12
  <=> k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f109,plain,
    ( r1_xboole_0(sK0,sK0)
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(trivial_inequality_removal,[],[f108])).

fof(f108,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK0)
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(superposition,[],[f100,f105])).

fof(f105,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f103])).

fof(f100,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k3_xboole_0(k2_relat_1(sK1),X2)
        | r1_xboole_0(sK0,X2) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f106,plain,
    ( spl2_12
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f97,f89,f103])).

fof(f89,plain,
    ( spl2_10
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f97,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl2_10 ),
    inference(resolution,[],[f91,f30])).

fof(f91,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f101,plain,
    ( spl2_11
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f94,f46,f99])).

fof(f46,plain,
    ( spl2_3
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f94,plain,
    ( ! [X2] :
        ( r1_xboole_0(sK0,X2)
        | k1_xboole_0 != k3_xboole_0(k2_relat_1(sK1),X2) )
    | ~ spl2_3 ),
    inference(resolution,[],[f65,f48])).

fof(f48,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1)
      | k1_xboole_0 != k3_xboole_0(X2,X1) ) ),
    inference(resolution,[],[f32,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f92,plain,
    ( spl2_10
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f86,f78,f51,f89])).

fof(f51,plain,
    ( spl2_4
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f78,plain,
    ( spl2_8
  <=> ! [X0] :
        ( k1_xboole_0 != k10_relat_1(sK1,X0)
        | r1_xboole_0(k2_relat_1(sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f86,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(trivial_inequality_removal,[],[f85])).

fof(f85,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(superposition,[],[f79,f53])).

fof(f53,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f79,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k10_relat_1(sK1,X0)
        | r1_xboole_0(k2_relat_1(sK1),X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,
    ( spl2_8
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f75,f36,f78])).

fof(f36,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f75,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k10_relat_1(sK1,X0)
        | r1_xboole_0(k2_relat_1(sK1),X0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f24,f38])).

fof(f38,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 != k10_relat_1(X1,X0)
      | r1_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f54,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f23,f51])).

fof(f23,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    & r1_tarski(sK0,k2_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k10_relat_1(X1,X0)
        & r1_tarski(X0,k2_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k10_relat_1(sK1,sK0)
      & r1_tarski(sK0,k2_relat_1(sK1))
      & k1_xboole_0 != sK0
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
            & r1_tarski(X0,k2_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

fof(f49,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f22,f46])).

fof(f22,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:30:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (830)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.45  % (823)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.45  % (823)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f141,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f80,f92,f101,f106,f118,f132,f140])).
% 0.21/0.45  fof(f140,plain,(
% 0.21/0.45    spl2_2 | ~spl2_16),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f139])).
% 0.21/0.45  fof(f139,plain,(
% 0.21/0.45    $false | (spl2_2 | ~spl2_16)),
% 0.21/0.45    inference(subsumption_resolution,[],[f136,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    k1_xboole_0 != sK0 | spl2_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    spl2_2 <=> k1_xboole_0 = sK0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.45  fof(f136,plain,(
% 0.21/0.45    k1_xboole_0 = sK0 | ~spl2_16),
% 0.21/0.45    inference(superposition,[],[f55,f131])).
% 0.21/0.45  fof(f131,plain,(
% 0.21/0.45    k1_xboole_0 = k3_xboole_0(sK0,sK0) | ~spl2_16),
% 0.21/0.45    inference(avatar_component_clause,[],[f129])).
% 0.21/0.45  fof(f129,plain,(
% 0.21/0.45    spl2_16 <=> k1_xboole_0 = k3_xboole_0(sK0,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.45    inference(resolution,[],[f26,f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.45    inference(equality_resolution,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.45    inference(flattening,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.45    inference(nnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.45  fof(f132,plain,(
% 0.21/0.45    spl2_16 | ~spl2_14),
% 0.21/0.45    inference(avatar_split_clause,[],[f123,f115,f129])).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    spl2_14 <=> r1_xboole_0(sK0,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.45  fof(f123,plain,(
% 0.21/0.45    k1_xboole_0 = k3_xboole_0(sK0,sK0) | ~spl2_14),
% 0.21/0.45    inference(resolution,[],[f117,f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK0) | ~spl2_14),
% 0.21/0.45    inference(avatar_component_clause,[],[f115])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    spl2_14 | ~spl2_11 | ~spl2_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f109,f103,f99,f115])).
% 0.21/0.45  fof(f99,plain,(
% 0.21/0.45    spl2_11 <=> ! [X2] : (r1_xboole_0(sK0,X2) | k1_xboole_0 != k3_xboole_0(k2_relat_1(sK1),X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.45  fof(f103,plain,(
% 0.21/0.45    spl2_12 <=> k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.45  fof(f109,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK0) | (~spl2_11 | ~spl2_12)),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f108])).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK0) | (~spl2_11 | ~spl2_12)),
% 0.21/0.45    inference(superposition,[],[f100,f105])).
% 0.21/0.45  fof(f105,plain,(
% 0.21/0.45    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0) | ~spl2_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f103])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    ( ! [X2] : (k1_xboole_0 != k3_xboole_0(k2_relat_1(sK1),X2) | r1_xboole_0(sK0,X2)) ) | ~spl2_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f99])).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    spl2_12 | ~spl2_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f97,f89,f103])).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    spl2_10 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0) | ~spl2_10),
% 0.21/0.45    inference(resolution,[],[f91,f30])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl2_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f89])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    spl2_11 | ~spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f94,f46,f99])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    spl2_3 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    ( ! [X2] : (r1_xboole_0(sK0,X2) | k1_xboole_0 != k3_xboole_0(k2_relat_1(sK1),X2)) ) | ~spl2_3),
% 0.21/0.45    inference(resolution,[],[f65,f48])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    r1_tarski(sK0,k2_relat_1(sK1)) | ~spl2_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f46])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r1_xboole_0(X0,X1) | k1_xboole_0 != k3_xboole_0(X2,X1)) )),
% 0.21/0.45    inference(resolution,[],[f32,f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    spl2_10 | ~spl2_4 | ~spl2_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f86,f78,f51,f89])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    spl2_4 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    spl2_8 <=> ! [X0] : (k1_xboole_0 != k10_relat_1(sK1,X0) | r1_xboole_0(k2_relat_1(sK1),X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    r1_xboole_0(k2_relat_1(sK1),sK0) | (~spl2_4 | ~spl2_8)),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f85])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),sK0) | (~spl2_4 | ~spl2_8)),
% 0.21/0.45    inference(superposition,[],[f79,f53])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl2_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f51])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 != k10_relat_1(sK1,X0) | r1_xboole_0(k2_relat_1(sK1),X0)) ) | ~spl2_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f78])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    spl2_8 | ~spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f75,f36,f78])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 != k10_relat_1(sK1,X0) | r1_xboole_0(k2_relat_1(sK1),X0)) ) | ~spl2_1),
% 0.21/0.45    inference(resolution,[],[f24,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f36])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 != k10_relat_1(X1,X0) | r1_xboole_0(k2_relat_1(X1),X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(nnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    spl2_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f23,f51])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.21/0.45    inference(flattening,[],[f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.45    inference(negated_conjecture,[],[f6])).
% 0.21/0.45  fof(f6,conjecture,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f22,f46])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ~spl2_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f21,f41])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    k1_xboole_0 != sK0),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f20,f36])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    v1_relat_1(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (823)------------------------------
% 0.21/0.45  % (823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (823)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (823)Memory used [KB]: 6140
% 0.21/0.45  % (823)Time elapsed: 0.067 s
% 0.21/0.45  % (823)------------------------------
% 0.21/0.45  % (823)------------------------------
% 0.21/0.46  % (820)Success in time 0.106 s
%------------------------------------------------------------------------------
