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
% DateTime   : Thu Dec  3 12:47:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  82 expanded)
%              Number of leaves         :   11 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  121 ( 244 expanded)
%              Number of equality atoms :   15 (  37 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f47,f73])).

fof(f73,plain,
    ( spl5_1
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f60,f35])).

fof(f35,plain,
    ( k1_xboole_0 != sK2
    | spl5_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f60,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f54,f54,f24,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f24,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f54,plain,
    ( ! [X0] : r1_tarski(sK2,X0)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f46,f50,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,X0)
      | r1_tarski(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ~ sP0(X1,X0) )
          & ( sP0(X1,X0)
            | ~ r1_tarski(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> sP0(X1,X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f50,plain,(
    ! [X0] : sP0(X0,sK2) ),
    inference(unit_resulting_resolution,[],[f22,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
          & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) )
      & ( ! [X4,X5] :
            ( r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X1) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ~ r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(k4_tarski(X2,X3),X1) ) )
      & ( ! [X4,X5] :
            ( r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2,X3] :
            ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            & r2_hidden(k4_tarski(X2,X3),X0) ) )
      & ( ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X1)
          | ~ r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X2,X1] : ~ r2_hidden(k4_tarski(X1,X2),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != sK2
    & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f7,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != sK2
      & ! [X2,X1] : ~ r2_hidden(k4_tarski(X1,X2),sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
         => k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(f46,plain,
    ( sP1(sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl5_3
  <=> sP1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f47,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f42,f38,f44])).

fof(f38,plain,
    ( spl5_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f42,plain,
    ( sP1(sK2)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f40,f30])).

fof(f30,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f8,f12,f11])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f40,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f41,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f21,f38])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f23,f33])).

fof(f23,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:17:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (30413)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (30415)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (30422)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (30405)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (30422)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f36,f41,f47,f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl5_1 | ~spl5_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    $false | (spl5_1 | ~spl5_3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f60,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    k1_xboole_0 != sK2 | spl5_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    spl5_1 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl5_3),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f54,f54,f24,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(sK2,X0)) ) | ~spl5_3),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f46,f50,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sP0(X1,X0) | r1_tarski(X0,X1) | ~sP1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~r1_tarski(X0,X1))) | ~sP1(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> sP0(X1,X0)) | ~sP1(X0))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0] : (sP0(X0,sK2)) )),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f22,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) | sP0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP0(X0,X1) | (~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) | ~sP0(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X2,X3),X1)) => (~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X2,X3),X1))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) | ~sP0(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X1,X0] : ((sP0(X1,X0) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~sP0(X1,X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X1,X2),sK2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    k1_xboole_0 != sK2 & ! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),sK2) & v1_relat_1(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f7,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : (k1_xboole_0 != X0 & ! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) & v1_relat_1(X0)) => (k1_xboole_0 != sK2 & ! [X2,X1] : ~r2_hidden(k4_tarski(X1,X2),sK2) & v1_relat_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (k1_xboole_0 != X0 & ! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) & v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0] : ((k1_xboole_0 != X0 & ! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0)) & v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    sP1(sK2) | ~spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl5_3 <=> sP1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl5_3 | ~spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f42,f38,f44])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    spl5_2 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    sP1(sK2) | ~spl5_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f40,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0] : (sP1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(definition_folding,[],[f8,f12,f11])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f38])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f38])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ~spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f33])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    k1_xboole_0 != sK2),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (30422)------------------------------
% 0.21/0.48  % (30422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30422)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (30422)Memory used [KB]: 10618
% 0.21/0.48  % (30422)Time elapsed: 0.057 s
% 0.21/0.48  % (30422)------------------------------
% 0.21/0.48  % (30422)------------------------------
% 0.21/0.48  % (30406)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (30404)Success in time 0.12 s
%------------------------------------------------------------------------------
