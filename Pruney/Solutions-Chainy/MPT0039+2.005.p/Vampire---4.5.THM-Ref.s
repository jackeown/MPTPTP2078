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
% DateTime   : Thu Dec  3 12:29:47 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 104 expanded)
%              Number of leaves         :    9 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :  148 ( 255 expanded)
%              Number of equality atoms :   23 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f53,f64,f71,f91,f99,f101,f105])).

fof(f105,plain,
    ( spl5_4
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f103,f51])).

fof(f51,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl5_4
  <=> r2_hidden(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f103,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f69,f12])).

fof(f12,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f69,plain,
    ( sP4(sK2(sK0,sK1),sK1,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_5
  <=> sP4(sK2(sK0,sK1),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f101,plain,
    ( ~ spl5_3
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | ~ spl5_3
    | spl5_5 ),
    inference(subsumption_resolution,[],[f48,f73])).

fof(f73,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1))
    | spl5_5 ),
    inference(resolution,[],[f70,f18])).

fof(f18,plain,(
    ! [X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f70,plain,
    ( ~ sP4(sK2(sK0,sK1),sK1,sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f48,plain,
    ( r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl5_3
  <=> r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f99,plain,
    ( spl5_1
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl5_1
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f97,f23])).

fof(f23,plain,
    ( sK0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl5_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f97,plain,
    ( sK0 = sK1
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f94,f52])).

fof(f52,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f94,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK0)
    | sK0 = sK1
    | ~ spl5_9 ),
    inference(resolution,[],[f90,f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | ~ r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f90,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_9
  <=> r2_hidden(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f91,plain,
    ( spl5_9
    | ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f74,f68,f50,f88])).

fof(f74,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f72,f52])).

fof(f72,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ r2_hidden(sK2(sK0,sK1),sK0)
    | spl5_5 ),
    inference(resolution,[],[f70,f11])).

fof(f11,plain,(
    ! [X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f71,plain,
    ( ~ spl5_5
    | spl5_3 ),
    inference(avatar_split_clause,[],[f66,f46,f68])).

fof(f66,plain,
    ( ~ sP4(sK2(sK0,sK1),sK1,sK0)
    | spl5_3 ),
    inference(resolution,[],[f47,f19])).

fof(f19,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f47,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f64,plain,
    ( ~ spl5_3
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f61,f50,f26,f46])).

fof(f26,plain,
    ( spl5_2
  <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f61,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(superposition,[],[f58,f28])).

fof(f28,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f58,plain,
    ( ! [X1] : ~ r2_hidden(sK2(sK0,sK1),k4_xboole_0(X1,sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f54,f18])).

fof(f54,plain,
    ( ! [X0] : ~ sP4(sK2(sK0,sK1),sK0,X0)
    | ~ spl5_4 ),
    inference(resolution,[],[f52,f13])).

fof(f13,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f53,plain,
    ( spl5_3
    | spl5_4
    | spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f42,f26,f21,f50,f46])).

fof(f42,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f41,f23])).

fof(f41,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1))
    | sK0 = sK1
    | ~ spl5_2 ),
    inference(factoring,[],[f36])).

fof(f36,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0,sK1),sK0)
        | r2_hidden(sK2(X0,sK1),k4_xboole_0(sK0,sK1))
        | r2_hidden(sK2(X0,sK1),X0)
        | sK1 = X0 )
    | ~ spl5_2 ),
    inference(resolution,[],[f32,f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f32,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r2_hidden(X1,sK0)
        | r2_hidden(X1,k4_xboole_0(sK0,sK1)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f30,f11])).

fof(f30,plain,
    ( ! [X0] :
        ( ~ sP4(X0,sK0,sK1)
        | r2_hidden(X0,k4_xboole_0(sK0,sK1)) )
    | ~ spl5_2 ),
    inference(superposition,[],[f19,f28])).

fof(f29,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f7,f26])).

fof(f7,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f24,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f8,f21])).

fof(f8,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (29768)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (29792)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.22/0.52  % (29784)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.22/0.52  % (29784)Refutation found. Thanks to Tanya!
% 1.22/0.52  % SZS status Theorem for theBenchmark
% 1.22/0.52  % SZS output start Proof for theBenchmark
% 1.22/0.52  fof(f106,plain,(
% 1.22/0.52    $false),
% 1.22/0.52    inference(avatar_sat_refutation,[],[f24,f29,f53,f64,f71,f91,f99,f101,f105])).
% 1.22/0.52  fof(f105,plain,(
% 1.22/0.52    spl5_4 | ~spl5_5),
% 1.22/0.52    inference(avatar_contradiction_clause,[],[f104])).
% 1.22/0.52  fof(f104,plain,(
% 1.22/0.52    $false | (spl5_4 | ~spl5_5)),
% 1.22/0.52    inference(subsumption_resolution,[],[f103,f51])).
% 1.22/0.52  fof(f51,plain,(
% 1.22/0.52    ~r2_hidden(sK2(sK0,sK1),sK0) | spl5_4),
% 1.22/0.52    inference(avatar_component_clause,[],[f50])).
% 1.22/0.52  fof(f50,plain,(
% 1.22/0.52    spl5_4 <=> r2_hidden(sK2(sK0,sK1),sK0)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.22/0.52  fof(f103,plain,(
% 1.22/0.52    r2_hidden(sK2(sK0,sK1),sK0) | ~spl5_5),
% 1.22/0.52    inference(resolution,[],[f69,f12])).
% 1.22/0.52  fof(f12,plain,(
% 1.22/0.52    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f1])).
% 1.22/0.52  fof(f1,axiom,(
% 1.22/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.22/0.52  fof(f69,plain,(
% 1.22/0.52    sP4(sK2(sK0,sK1),sK1,sK0) | ~spl5_5),
% 1.22/0.52    inference(avatar_component_clause,[],[f68])).
% 1.22/0.52  fof(f68,plain,(
% 1.22/0.52    spl5_5 <=> sP4(sK2(sK0,sK1),sK1,sK0)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.22/0.52  fof(f101,plain,(
% 1.22/0.52    ~spl5_3 | spl5_5),
% 1.22/0.52    inference(avatar_contradiction_clause,[],[f100])).
% 1.22/0.52  fof(f100,plain,(
% 1.22/0.52    $false | (~spl5_3 | spl5_5)),
% 1.22/0.52    inference(subsumption_resolution,[],[f48,f73])).
% 1.22/0.52  fof(f73,plain,(
% 1.22/0.52    ~r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1)) | spl5_5),
% 1.22/0.52    inference(resolution,[],[f70,f18])).
% 1.22/0.52  fof(f18,plain,(
% 1.22/0.52    ( ! [X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 1.22/0.52    inference(equality_resolution,[],[f15])).
% 1.22/0.52  fof(f15,plain,(
% 1.22/0.52    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.22/0.52    inference(cnf_transformation,[],[f1])).
% 1.22/0.52  fof(f70,plain,(
% 1.22/0.52    ~sP4(sK2(sK0,sK1),sK1,sK0) | spl5_5),
% 1.22/0.52    inference(avatar_component_clause,[],[f68])).
% 1.22/0.52  fof(f48,plain,(
% 1.22/0.52    r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1)) | ~spl5_3),
% 1.22/0.52    inference(avatar_component_clause,[],[f46])).
% 1.22/0.52  fof(f46,plain,(
% 1.22/0.52    spl5_3 <=> r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.22/0.52  fof(f99,plain,(
% 1.22/0.52    spl5_1 | ~spl5_4 | ~spl5_9),
% 1.22/0.52    inference(avatar_contradiction_clause,[],[f98])).
% 1.22/0.52  fof(f98,plain,(
% 1.22/0.52    $false | (spl5_1 | ~spl5_4 | ~spl5_9)),
% 1.22/0.52    inference(subsumption_resolution,[],[f97,f23])).
% 1.22/0.52  fof(f23,plain,(
% 1.22/0.52    sK0 != sK1 | spl5_1),
% 1.22/0.52    inference(avatar_component_clause,[],[f21])).
% 1.22/0.52  fof(f21,plain,(
% 1.22/0.52    spl5_1 <=> sK0 = sK1),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.22/0.52  fof(f97,plain,(
% 1.22/0.52    sK0 = sK1 | (~spl5_4 | ~spl5_9)),
% 1.22/0.52    inference(subsumption_resolution,[],[f94,f52])).
% 1.22/0.52  fof(f52,plain,(
% 1.22/0.52    r2_hidden(sK2(sK0,sK1),sK0) | ~spl5_4),
% 1.22/0.52    inference(avatar_component_clause,[],[f50])).
% 1.22/0.52  fof(f94,plain,(
% 1.22/0.52    ~r2_hidden(sK2(sK0,sK1),sK0) | sK0 = sK1 | ~spl5_9),
% 1.22/0.52    inference(resolution,[],[f90,f10])).
% 1.22/0.52  fof(f10,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0) | X0 = X1) )),
% 1.22/0.52    inference(cnf_transformation,[],[f6])).
% 1.22/0.52  fof(f6,plain,(
% 1.22/0.52    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.22/0.52    inference(ennf_transformation,[],[f2])).
% 1.22/0.52  fof(f2,axiom,(
% 1.22/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.22/0.52  fof(f90,plain,(
% 1.22/0.52    r2_hidden(sK2(sK0,sK1),sK1) | ~spl5_9),
% 1.22/0.52    inference(avatar_component_clause,[],[f88])).
% 1.22/0.52  fof(f88,plain,(
% 1.22/0.52    spl5_9 <=> r2_hidden(sK2(sK0,sK1),sK1)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.22/0.52  fof(f91,plain,(
% 1.22/0.52    spl5_9 | ~spl5_4 | spl5_5),
% 1.22/0.52    inference(avatar_split_clause,[],[f74,f68,f50,f88])).
% 1.22/0.52  fof(f74,plain,(
% 1.22/0.52    r2_hidden(sK2(sK0,sK1),sK1) | (~spl5_4 | spl5_5)),
% 1.22/0.52    inference(subsumption_resolution,[],[f72,f52])).
% 1.22/0.52  fof(f72,plain,(
% 1.22/0.52    r2_hidden(sK2(sK0,sK1),sK1) | ~r2_hidden(sK2(sK0,sK1),sK0) | spl5_5),
% 1.22/0.52    inference(resolution,[],[f70,f11])).
% 1.22/0.52  fof(f11,plain,(
% 1.22/0.52    ( ! [X0,X3,X1] : (sP4(X3,X1,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f1])).
% 1.22/0.52  fof(f71,plain,(
% 1.22/0.52    ~spl5_5 | spl5_3),
% 1.22/0.52    inference(avatar_split_clause,[],[f66,f46,f68])).
% 1.22/0.52  fof(f66,plain,(
% 1.22/0.52    ~sP4(sK2(sK0,sK1),sK1,sK0) | spl5_3),
% 1.22/0.52    inference(resolution,[],[f47,f19])).
% 1.22/0.52  fof(f19,plain,(
% 1.22/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | ~sP4(X3,X1,X0)) )),
% 1.22/0.52    inference(equality_resolution,[],[f14])).
% 1.22/0.52  fof(f14,plain,(
% 1.22/0.52    ( ! [X2,X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.22/0.52    inference(cnf_transformation,[],[f1])).
% 1.22/0.52  fof(f47,plain,(
% 1.22/0.52    ~r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1)) | spl5_3),
% 1.22/0.52    inference(avatar_component_clause,[],[f46])).
% 1.22/0.52  fof(f64,plain,(
% 1.22/0.52    ~spl5_3 | ~spl5_2 | ~spl5_4),
% 1.22/0.52    inference(avatar_split_clause,[],[f61,f50,f26,f46])).
% 1.22/0.52  fof(f26,plain,(
% 1.22/0.52    spl5_2 <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.22/0.52  fof(f61,plain,(
% 1.22/0.52    ~r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1)) | (~spl5_2 | ~spl5_4)),
% 1.22/0.52    inference(superposition,[],[f58,f28])).
% 1.22/0.52  fof(f28,plain,(
% 1.22/0.52    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0) | ~spl5_2),
% 1.22/0.52    inference(avatar_component_clause,[],[f26])).
% 1.22/0.52  fof(f58,plain,(
% 1.22/0.52    ( ! [X1] : (~r2_hidden(sK2(sK0,sK1),k4_xboole_0(X1,sK0))) ) | ~spl5_4),
% 1.22/0.52    inference(resolution,[],[f54,f18])).
% 1.22/0.52  fof(f54,plain,(
% 1.22/0.52    ( ! [X0] : (~sP4(sK2(sK0,sK1),sK0,X0)) ) | ~spl5_4),
% 1.22/0.52    inference(resolution,[],[f52,f13])).
% 1.22/0.52  fof(f13,plain,(
% 1.22/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~sP4(X3,X1,X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f1])).
% 1.22/0.52  fof(f53,plain,(
% 1.22/0.52    spl5_3 | spl5_4 | spl5_1 | ~spl5_2),
% 1.22/0.52    inference(avatar_split_clause,[],[f42,f26,f21,f50,f46])).
% 1.22/0.52  fof(f42,plain,(
% 1.22/0.52    r2_hidden(sK2(sK0,sK1),sK0) | r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1)) | (spl5_1 | ~spl5_2)),
% 1.22/0.52    inference(subsumption_resolution,[],[f41,f23])).
% 1.22/0.52  fof(f41,plain,(
% 1.22/0.52    r2_hidden(sK2(sK0,sK1),sK0) | r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1)) | sK0 = sK1 | ~spl5_2),
% 1.22/0.52    inference(factoring,[],[f36])).
% 1.22/0.52  fof(f36,plain,(
% 1.22/0.52    ( ! [X0] : (r2_hidden(sK2(X0,sK1),sK0) | r2_hidden(sK2(X0,sK1),k4_xboole_0(sK0,sK1)) | r2_hidden(sK2(X0,sK1),X0) | sK1 = X0) ) | ~spl5_2),
% 1.22/0.52    inference(resolution,[],[f32,f9])).
% 1.22/0.52  fof(f9,plain,(
% 1.22/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X0 = X1) )),
% 1.22/0.52    inference(cnf_transformation,[],[f6])).
% 1.22/0.52  fof(f32,plain,(
% 1.22/0.52    ( ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(X1,sK0) | r2_hidden(X1,k4_xboole_0(sK0,sK1))) ) | ~spl5_2),
% 1.22/0.52    inference(resolution,[],[f30,f11])).
% 1.22/0.52  fof(f30,plain,(
% 1.22/0.52    ( ! [X0] : (~sP4(X0,sK0,sK1) | r2_hidden(X0,k4_xboole_0(sK0,sK1))) ) | ~spl5_2),
% 1.22/0.52    inference(superposition,[],[f19,f28])).
% 1.22/0.52  fof(f29,plain,(
% 1.22/0.52    spl5_2),
% 1.22/0.52    inference(avatar_split_clause,[],[f7,f26])).
% 1.22/0.52  fof(f7,plain,(
% 1.22/0.52    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0)),
% 1.22/0.52    inference(cnf_transformation,[],[f5])).
% 1.22/0.52  fof(f5,plain,(
% 1.22/0.52    ? [X0,X1] : (X0 != X1 & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f4])).
% 1.22/0.52  fof(f4,negated_conjecture,(
% 1.22/0.52    ~! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 1.22/0.52    inference(negated_conjecture,[],[f3])).
% 1.22/0.52  fof(f3,conjecture,(
% 1.22/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).
% 1.22/0.52  fof(f24,plain,(
% 1.22/0.52    ~spl5_1),
% 1.22/0.52    inference(avatar_split_clause,[],[f8,f21])).
% 1.22/0.52  fof(f8,plain,(
% 1.22/0.52    sK0 != sK1),
% 1.22/0.52    inference(cnf_transformation,[],[f5])).
% 1.22/0.52  % SZS output end Proof for theBenchmark
% 1.22/0.52  % (29784)------------------------------
% 1.22/0.52  % (29784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (29784)Termination reason: Refutation
% 1.22/0.52  
% 1.22/0.52  % (29784)Memory used [KB]: 10746
% 1.22/0.52  % (29784)Time elapsed: 0.130 s
% 1.22/0.52  % (29784)------------------------------
% 1.22/0.52  % (29784)------------------------------
% 1.22/0.52  % (29757)Success in time 0.159 s
%------------------------------------------------------------------------------
