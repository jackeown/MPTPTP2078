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
% DateTime   : Thu Dec  3 12:50:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 (  96 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  169 ( 285 expanded)
%              Number of equality atoms :   46 (  93 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f55,f88,f99,f107,f119,f128])).

fof(f128,plain,
    ( spl2_2
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl2_2
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f126,f44])).

fof(f44,plain,
    ( k1_xboole_0 != sK0
    | spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f126,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f125,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f32,f34])).

fof(f34,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f125,plain,
    ( sK0 = k4_xboole_0(sK0,sK0)
    | ~ spl2_13 ),
    inference(resolution,[],[f118,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f118,plain,
    ( r1_xboole_0(sK0,sK0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl2_13
  <=> r1_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f119,plain,
    ( spl2_13
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f114,f105,f47,f116])).

fof(f47,plain,
    ( spl2_3
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f105,plain,
    ( spl2_11
  <=> ! [X0] :
        ( r1_xboole_0(X0,sK0)
        | ~ r1_tarski(X0,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f114,plain,
    ( r1_xboole_0(sK0,sK0)
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(resolution,[],[f106,f49])).

fof(f49,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK1))
        | r1_xboole_0(X0,sK0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f107,plain,
    ( spl2_11
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f102,f96,f105])).

fof(f96,plain,
    ( spl2_10
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f102,plain,
    ( ! [X0] :
        ( r1_xboole_0(X0,sK0)
        | ~ r1_tarski(X0,k2_relat_1(sK1)) )
    | ~ spl2_10 ),
    inference(resolution,[],[f98,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f98,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f99,plain,
    ( spl2_10
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f94,f86,f52,f96])).

fof(f52,plain,
    ( spl2_4
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f86,plain,
    ( spl2_8
  <=> ! [X0] :
        ( k1_xboole_0 != k10_relat_1(sK1,X0)
        | r1_xboole_0(k2_relat_1(sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f94,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(trivial_inequality_removal,[],[f93])).

fof(f93,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(superposition,[],[f87,f54])).

fof(f54,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f87,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k10_relat_1(sK1,X0)
        | r1_xboole_0(k2_relat_1(sK1),X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f88,plain,
    ( spl2_8
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f71,f37,f86])).

fof(f37,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f71,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k10_relat_1(sK1,X0)
        | r1_xboole_0(k2_relat_1(sK1),X0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f24,f39])).

fof(f39,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 != k10_relat_1(X1,X0)
      | r1_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f55,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    & r1_tarski(sK0,k2_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13])).

fof(f13,plain,
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

fof(f50,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f20,f37])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:42:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (21126)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (21115)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.46  % (21115)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f129,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f40,f45,f50,f55,f88,f99,f107,f119,f128])).
% 0.21/0.46  fof(f128,plain,(
% 0.21/0.46    spl2_2 | ~spl2_13),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f127])).
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    $false | (spl2_2 | ~spl2_13)),
% 0.21/0.46    inference(subsumption_resolution,[],[f126,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    k1_xboole_0 != sK0 | spl2_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    spl2_2 <=> k1_xboole_0 = sK0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    k1_xboole_0 = sK0 | ~spl2_13),
% 0.21/0.46    inference(forward_demodulation,[],[f125,f56])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.46    inference(resolution,[],[f32,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.46    inference(equality_resolution,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.46    inference(flattening,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.46    inference(nnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    sK0 = k4_xboole_0(sK0,sK0) | ~spl2_13),
% 0.21/0.46    inference(resolution,[],[f118,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.46    inference(nnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    r1_xboole_0(sK0,sK0) | ~spl2_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f116])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    spl2_13 <=> r1_xboole_0(sK0,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.46  fof(f119,plain,(
% 0.21/0.46    spl2_13 | ~spl2_3 | ~spl2_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f114,f105,f47,f116])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    spl2_3 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    spl2_11 <=> ! [X0] : (r1_xboole_0(X0,sK0) | ~r1_tarski(X0,k2_relat_1(sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.46  fof(f114,plain,(
% 0.21/0.46    r1_xboole_0(sK0,sK0) | (~spl2_3 | ~spl2_11)),
% 0.21/0.46    inference(resolution,[],[f106,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    r1_tarski(sK0,k2_relat_1(sK1)) | ~spl2_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f47])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | r1_xboole_0(X0,sK0)) ) | ~spl2_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f105])).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    spl2_11 | ~spl2_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f102,f96,f105])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    spl2_10 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    ( ! [X0] : (r1_xboole_0(X0,sK0) | ~r1_tarski(X0,k2_relat_1(sK1))) ) | ~spl2_10),
% 0.21/0.46    inference(resolution,[],[f98,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl2_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f96])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    spl2_10 | ~spl2_4 | ~spl2_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f94,f86,f52,f96])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    spl2_4 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    spl2_8 <=> ! [X0] : (k1_xboole_0 != k10_relat_1(sK1,X0) | r1_xboole_0(k2_relat_1(sK1),X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    r1_xboole_0(k2_relat_1(sK1),sK0) | (~spl2_4 | ~spl2_8)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f93])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),sK0) | (~spl2_4 | ~spl2_8)),
% 0.21/0.46    inference(superposition,[],[f87,f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl2_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f52])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 != k10_relat_1(sK1,X0) | r1_xboole_0(k2_relat_1(sK1),X0)) ) | ~spl2_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f86])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    spl2_8 | ~spl2_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f71,f37,f86])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 != k10_relat_1(sK1,X0) | r1_xboole_0(k2_relat_1(sK1),X0)) ) | ~spl2_1),
% 0.21/0.46    inference(resolution,[],[f24,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f37])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 != k10_relat_1(X1,X0) | r1_xboole_0(k2_relat_1(X1),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    spl2_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f23,f52])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.46    inference(negated_conjecture,[],[f6])).
% 0.21/0.46  fof(f6,conjecture,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    spl2_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f47])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ~spl2_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f21,f42])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    k1_xboole_0 != sK0),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    spl2_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f20,f37])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    v1_relat_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (21115)------------------------------
% 0.21/0.46  % (21115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (21115)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (21115)Memory used [KB]: 6140
% 0.21/0.46  % (21115)Time elapsed: 0.058 s
% 0.21/0.46  % (21115)------------------------------
% 0.21/0.46  % (21115)------------------------------
% 0.21/0.46  % (21110)Success in time 0.108 s
%------------------------------------------------------------------------------
