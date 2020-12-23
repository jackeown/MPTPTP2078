%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   51 (  80 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :  120 ( 213 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f58,f87,f137,f279,f280])).

fof(f280,plain,
    ( sK0 != k3_xboole_0(sK0,sK1)
    | k7_relat_1(sK2,sK0) = k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f279,plain,(
    spl3_16 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | spl3_16 ),
    inference(unit_resulting_resolution,[],[f27,f135,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f135,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl3_16
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f27,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f137,plain,
    ( spl3_15
    | ~ spl3_16
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f99,f54,f133,f129])).

fof(f129,plain,
    ( spl3_15
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f54,plain,
    ( spl3_4
  <=> r1_tarski(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f99,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f56,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f87,plain,
    ( ~ spl3_9
    | spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f82,f39,f29,f84])).

fof(f84,plain,
    ( spl3_9
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f29,plain,
    ( spl3_1
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f39,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f82,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f31,f43])).

fof(f43,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f41,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f41,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f31,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f58,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f49,f34,f54])).

fof(f34,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f49,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f27,f36,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f36,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f42,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f37,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f19,f29])).

fof(f19,plain,(
    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:07:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.48  % (7320)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.48  % (7320)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f281,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(avatar_sat_refutation,[],[f32,f37,f42,f58,f87,f137,f279,f280])).
% 0.19/0.48  fof(f280,plain,(
% 0.19/0.48    sK0 != k3_xboole_0(sK0,sK1) | k7_relat_1(sK2,sK0) = k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 0.19/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.48  fof(f279,plain,(
% 0.19/0.48    spl3_16),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f278])).
% 0.19/0.48  fof(f278,plain,(
% 0.19/0.48    $false | spl3_16),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f27,f135,f25])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f12])).
% 0.19/0.48  fof(f12,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.19/0.48    inference(ennf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.19/0.48  fof(f135,plain,(
% 0.19/0.48    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | spl3_16),
% 0.19/0.48    inference(avatar_component_clause,[],[f133])).
% 0.19/0.48  fof(f133,plain,(
% 0.19/0.48    spl3_16 <=> r1_tarski(k3_xboole_0(sK0,sK1),sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.48    inference(equality_resolution,[],[f20])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.19/0.48    inference(cnf_transformation,[],[f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.48    inference(flattening,[],[f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.48    inference(nnf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.48  fof(f137,plain,(
% 0.19/0.48    spl3_15 | ~spl3_16 | ~spl3_4),
% 0.19/0.48    inference(avatar_split_clause,[],[f99,f54,f133,f129])).
% 0.19/0.48  fof(f129,plain,(
% 0.19/0.48    spl3_15 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.19/0.48  fof(f54,plain,(
% 0.19/0.48    spl3_4 <=> r1_tarski(sK0,k3_xboole_0(sK0,sK1))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.48  fof(f99,plain,(
% 0.19/0.48    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | sK0 = k3_xboole_0(sK0,sK1) | ~spl3_4),
% 0.19/0.48    inference(resolution,[],[f56,f22])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.19/0.48    inference(cnf_transformation,[],[f16])).
% 0.19/0.48  fof(f56,plain,(
% 0.19/0.48    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_4),
% 0.19/0.48    inference(avatar_component_clause,[],[f54])).
% 0.19/0.48  fof(f87,plain,(
% 0.19/0.48    ~spl3_9 | spl3_1 | ~spl3_3),
% 0.19/0.48    inference(avatar_split_clause,[],[f82,f39,f29,f84])).
% 0.19/0.48  fof(f84,plain,(
% 0.19/0.48    spl3_9 <=> k7_relat_1(sK2,sK0) = k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.48  fof(f29,plain,(
% 0.19/0.48    spl3_1 <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.48  fof(f39,plain,(
% 0.19/0.48    spl3_3 <=> v1_relat_1(sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.48  fof(f82,plain,(
% 0.19/0.48    k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) | (spl3_1 | ~spl3_3)),
% 0.19/0.48    inference(superposition,[],[f31,f43])).
% 0.19/0.48  fof(f43,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) ) | ~spl3_3),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f41,f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f9])).
% 0.19/0.48  fof(f9,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.19/0.48  fof(f41,plain,(
% 0.19/0.48    v1_relat_1(sK2) | ~spl3_3),
% 0.19/0.48    inference(avatar_component_clause,[],[f39])).
% 0.19/0.48  fof(f31,plain,(
% 0.19/0.48    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) | spl3_1),
% 0.19/0.48    inference(avatar_component_clause,[],[f29])).
% 0.19/0.48  fof(f58,plain,(
% 0.19/0.48    spl3_4 | ~spl3_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f49,f34,f54])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.48  fof(f49,plain,(
% 0.19/0.48    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_2),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f27,f36,f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f11])).
% 0.19/0.48  fof(f11,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.48    inference(flattening,[],[f10])).
% 0.19/0.48  fof(f10,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.48    inference(ennf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.19/0.48    inference(avatar_component_clause,[],[f34])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    spl3_3),
% 0.19/0.48    inference(avatar_split_clause,[],[f17,f39])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    v1_relat_1(sK2)),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f8,plain,(
% 0.19/0.48    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.19/0.48    inference(flattening,[],[f7])).
% 0.19/0.48  fof(f7,plain,(
% 0.19/0.48    ? [X0,X1,X2] : ((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.19/0.48    inference(ennf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,negated_conjecture,(
% 0.19/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.19/0.48    inference(negated_conjecture,[],[f5])).
% 0.19/0.48  fof(f5,conjecture,(
% 0.19/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 0.19/0.48  fof(f37,plain,(
% 0.19/0.48    spl3_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f18,f34])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    r1_tarski(sK0,sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    ~spl3_1),
% 0.19/0.48    inference(avatar_split_clause,[],[f19,f29])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (7320)------------------------------
% 0.19/0.48  % (7320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (7320)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (7320)Memory used [KB]: 6268
% 0.19/0.48  % (7320)Time elapsed: 0.043 s
% 0.19/0.48  % (7320)------------------------------
% 0.19/0.48  % (7320)------------------------------
% 0.19/0.49  % (7301)Success in time 0.136 s
%------------------------------------------------------------------------------
