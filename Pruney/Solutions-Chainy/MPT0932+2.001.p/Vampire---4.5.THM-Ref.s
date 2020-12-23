%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  60 expanded)
%              Number of leaves         :    9 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :  107 ( 164 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f24,f29,f34,f39,f45,f48])).

fof(f48,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f46,f18])).

fof(f18,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f16,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f46,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(resolution,[],[f44,f28])).

fof(f28,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl2_3
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f44,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_6
  <=> ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

% (32410)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
fof(f45,plain,
    ( spl2_6
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f41,f37,f26,f21,f43])).

fof(f21,plain,
    ( spl2_2
  <=> r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f37,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k2_mcart_1(X0),k11_relat_1(sK0,k1_mcart_1(X0)))
        | ~ r2_hidden(X0,X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f41,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ v1_relat_1(X0) )
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f40,f23])).

fof(f23,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f21])).

fof(f40,plain,
    ( ! [X0] :
        ( r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1)))
        | ~ r2_hidden(sK1,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(resolution,[],[f38,f28])).

fof(f38,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k2_mcart_1(X0),k11_relat_1(sK0,k1_mcart_1(X0)))
        | ~ r2_hidden(X0,X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f37])).

fof(f39,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f35,f32,f37])).

fof(f32,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( r2_hidden(X0,k11_relat_1(sK0,X1))
        | ~ r2_hidden(k4_tarski(X1,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f35,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k2_mcart_1(X0),k11_relat_1(sK0,k1_mcart_1(X0)))
        | ~ r2_hidden(X0,X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_4 ),
    inference(superposition,[],[f33,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f33,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X1,X0),sK0)
        | r2_hidden(X0,k11_relat_1(sK0,X1)) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f32])).

fof(f34,plain,
    ( spl2_4
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f30,f16,f32])).

fof(f30,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k11_relat_1(sK0,X1))
        | ~ r2_hidden(k4_tarski(X1,X0),sK0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f14,f18])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f29,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f9,f26])).

fof(f9,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1)))
          & r2_hidden(X1,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r2_hidden(X1,X0)
           => r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_mcart_1)).

fof(f24,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f10,f21])).

fof(f10,plain,(
    ~ r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1))) ),
    inference(cnf_transformation,[],[f5])).

fof(f19,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f11,f16])).

fof(f11,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:12:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.40  % (32406)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.42  % (32405)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (32407)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.43  % (32400)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (32400)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f19,f24,f29,f34,f39,f45,f48])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ~spl2_1 | ~spl2_3 | ~spl2_6),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    $false | (~spl2_1 | ~spl2_3 | ~spl2_6)),
% 0.21/0.43    inference(subsumption_resolution,[],[f46,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    v1_relat_1(sK0) | ~spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    spl2_1 <=> v1_relat_1(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ~v1_relat_1(sK0) | (~spl2_3 | ~spl2_6)),
% 0.21/0.43    inference(resolution,[],[f44,f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    r2_hidden(sK1,sK0) | ~spl2_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    spl2_3 <=> r2_hidden(sK1,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(sK1,X0) | ~v1_relat_1(X0)) ) | ~spl2_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f43])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    spl2_6 <=> ! [X0] : (~r2_hidden(sK1,X0) | ~v1_relat_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.43  % (32410)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    spl2_6 | spl2_2 | ~spl2_3 | ~spl2_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f41,f37,f26,f21,f43])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    spl2_2 <=> r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    spl2_5 <=> ! [X1,X0] : (~r2_hidden(X0,sK0) | r2_hidden(k2_mcart_1(X0),k11_relat_1(sK0,k1_mcart_1(X0))) | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(sK1,X0) | ~v1_relat_1(X0)) ) | (spl2_2 | ~spl2_3 | ~spl2_5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f40,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ~r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1))) | spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f21])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X0] : (r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1))) | ~r2_hidden(sK1,X0) | ~v1_relat_1(X0)) ) | (~spl2_3 | ~spl2_5)),
% 0.21/0.43    inference(resolution,[],[f38,f28])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | r2_hidden(k2_mcart_1(X0),k11_relat_1(sK0,k1_mcart_1(X0))) | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) ) | ~spl2_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f37])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    spl2_5 | ~spl2_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f35,f32,f37])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    spl2_4 <=> ! [X1,X0] : (r2_hidden(X0,k11_relat_1(sK0,X1)) | ~r2_hidden(k4_tarski(X1,X0),sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | r2_hidden(k2_mcart_1(X0),k11_relat_1(sK0,k1_mcart_1(X0))) | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) ) | ~spl2_4),
% 0.21/0.43    inference(superposition,[],[f33,f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f6])).
% 0.21/0.43  fof(f6,plain,(
% 0.21/0.43    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X1,X0),sK0) | r2_hidden(X0,k11_relat_1(sK0,X1))) ) | ~spl2_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f32])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    spl2_4 | ~spl2_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f30,f16,f32])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(X0,k11_relat_1(sK0,X1)) | ~r2_hidden(k4_tarski(X1,X0),sK0)) ) | ~spl2_1),
% 0.21/0.43    inference(resolution,[],[f14,f18])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    spl2_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f9,f26])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    r2_hidden(sK1,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (~r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1))) & r2_hidden(X1,X0)) & v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_hidden(X1,X0) => r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1)))))),
% 0.21/0.43    inference(negated_conjecture,[],[f3])).
% 0.21/0.43  fof(f3,conjecture,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_hidden(X1,X0) => r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1)))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_mcart_1)).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ~spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f10,f21])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ~r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1)))),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    spl2_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f11,f16])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    v1_relat_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (32400)------------------------------
% 0.21/0.43  % (32400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (32400)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (32400)Memory used [KB]: 10490
% 0.21/0.43  % (32400)Time elapsed: 0.005 s
% 0.21/0.43  % (32400)------------------------------
% 0.21/0.43  % (32400)------------------------------
% 0.21/0.43  % (32401)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.43  % (32403)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  % (32404)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (32398)Success in time 0.083 s
%------------------------------------------------------------------------------
