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
% DateTime   : Thu Dec  3 12:49:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  70 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  128 ( 226 expanded)
%              Number of equality atoms :   36 (  81 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f86,f107])).

fof(f107,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | spl2_8 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | spl2_8 ),
    inference(subsumption_resolution,[],[f105,f46])).

fof(f46,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f105,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl2_1
    | spl2_8 ),
    inference(subsumption_resolution,[],[f102,f84])).

fof(f84,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_8
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f102,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f101])).

fof(f101,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(superposition,[],[f20,f31])).

fof(f31,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f86,plain,
    ( ~ spl2_8
    | ~ spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f61,f39,f34,f82])).

fof(f34,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f39,plain,
    ( spl2_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f61,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_2
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f27,f41,f36,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f36,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f41,plain,
    ( k1_xboole_0 != sK0
    | spl2_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f27,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f47,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f16,f44])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k9_relat_1(X1,X0)
        & r1_tarski(X0,k1_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k9_relat_1(sK1,sK0)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & k1_xboole_0 != sK0
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

fof(f42,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f19,f29])).

fof(f19,plain,(
    k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (20502)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (20494)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.48  % (20502)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f86,f107])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    ~spl2_1 | ~spl2_4 | spl2_8),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f106])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    $false | (~spl2_1 | ~spl2_4 | spl2_8)),
% 0.20/0.48    inference(subsumption_resolution,[],[f105,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    v1_relat_1(sK1) | ~spl2_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    spl2_4 <=> v1_relat_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    ~v1_relat_1(sK1) | (~spl2_1 | spl2_8)),
% 0.20/0.48    inference(subsumption_resolution,[],[f102,f84])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl2_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f82])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    spl2_8 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl2_1),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f101])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl2_1),
% 0.20/0.48    inference(superposition,[],[f20,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl2_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    spl2_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    ~spl2_8 | ~spl2_2 | spl2_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f61,f39,f34,f82])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    spl2_2 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    spl2_3 <=> k1_xboole_0 = sK0),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ~r1_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_2 | spl2_3)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f27,f41,f36,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f34])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    k1_xboole_0 != sK0 | spl2_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f39])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.48    inference(equality_resolution,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    spl2_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f16,f44])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    v1_relat_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    k1_xboole_0 = k9_relat_1(sK1,sK0) & r1_tarski(sK0,k1_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k9_relat_1(sK1,sK0) & r1_tarski(sK0,k1_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.48    inference(negated_conjecture,[],[f4])).
% 0.20/0.48  fof(f4,conjecture,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ~spl2_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f17,f39])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    k1_xboole_0 != sK0),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    spl2_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f18,f34])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    spl2_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f19,f29])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (20502)------------------------------
% 0.20/0.48  % (20502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (20502)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (20502)Memory used [KB]: 6140
% 0.20/0.48  % (20502)Time elapsed: 0.072 s
% 0.20/0.48  % (20502)------------------------------
% 0.20/0.48  % (20502)------------------------------
% 0.20/0.48  % (20484)Success in time 0.123 s
%------------------------------------------------------------------------------
