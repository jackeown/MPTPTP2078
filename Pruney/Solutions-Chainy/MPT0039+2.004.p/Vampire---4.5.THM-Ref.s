%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 (  68 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  117 ( 172 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f120,f126,f130])).

fof(f130,plain,
    ( spl6_11
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f129,f41,f123])).

fof(f123,plain,
    ( spl6_11
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f41,plain,
    ( spl6_2
  <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f129,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl6_2 ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f85,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f85,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(X1,sK0),sK1)
        | r1_tarski(X1,sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f82,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f82,plain,
    ( ! [X3] :
        ( r2_hidden(X3,sK0)
        | ~ r2_hidden(X3,sK1) )
    | ~ spl6_2 ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,
    ( ! [X3] :
        ( r2_hidden(X3,sK0)
        | ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(X3,sK1) )
    | ~ spl6_2 ),
    inference(resolution,[],[f47,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f47,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k4_xboole_0(sK0,sK1))
        | r2_hidden(X2,sK0)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl6_2 ),
    inference(superposition,[],[f32,f43])).

fof(f43,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f126,plain,
    ( ~ spl6_11
    | spl6_1
    | spl6_10 ),
    inference(avatar_split_clause,[],[f121,f117,f36,f123])).

fof(f36,plain,
    ( spl6_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f117,plain,
    ( spl6_10
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f121,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,sK0)
    | spl6_10 ),
    inference(resolution,[],[f119,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f119,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f120,plain,
    ( ~ spl6_10
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f115,f41,f117])).

fof(f115,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | ~ spl6_2 ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | ~ r2_xboole_0(sK1,sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f58,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f58,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK4(sK1,X2),sK0)
        | ~ r2_xboole_0(sK1,X2) )
    | ~ spl6_2 ),
    inference(resolution,[],[f55,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_2 ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f45,f32])).

fof(f45,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_xboole_0(sK0,sK1))
        | r2_hidden(X0,sK1) )
    | ~ spl6_2 ),
    inference(superposition,[],[f34,f43])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f44,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f12,f41])).

fof(f12,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f39,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f13,f36])).

fof(f13,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (31828)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (31843)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (31821)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (31842)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (31835)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (31824)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (31834)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (31829)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (31825)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (31836)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (31831)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (31826)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (31830)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (31842)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f39,f44,f120,f126,f130])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    spl6_11 | ~spl6_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f129,f41,f123])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    spl6_11 <=> r1_tarski(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    spl6_2 <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    r1_tarski(sK1,sK0) | ~spl6_2),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f128])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl6_2),
% 0.20/0.51    inference(resolution,[],[f85,f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ( ! [X1] : (~r2_hidden(sK3(X1,sK0),sK1) | r1_tarski(X1,sK0)) ) | ~spl6_2),
% 0.20/0.51    inference(resolution,[],[f82,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ( ! [X3] : (r2_hidden(X3,sK0) | ~r2_hidden(X3,sK1)) ) | ~spl6_2),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X3] : (r2_hidden(X3,sK0) | ~r2_hidden(X3,sK1) | ~r2_hidden(X3,sK1)) ) | ~spl6_2),
% 0.20/0.51    inference(resolution,[],[f47,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X2] : (r2_hidden(X2,k4_xboole_0(sK0,sK1)) | r2_hidden(X2,sK0) | ~r2_hidden(X2,sK1)) ) | ~spl6_2),
% 0.20/0.51    inference(superposition,[],[f32,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0) | ~spl6_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f41])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    ~spl6_11 | spl6_1 | spl6_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f121,f117,f36,f123])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    spl6_1 <=> sK0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    spl6_10 <=> r2_xboole_0(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    sK0 = sK1 | ~r1_tarski(sK1,sK0) | spl6_10),
% 0.20/0.51    inference(resolution,[],[f119,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    ~r2_xboole_0(sK1,sK0) | spl6_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f117])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    ~spl6_10 | ~spl6_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f115,f41,f117])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ~r2_xboole_0(sK1,sK0) | ~spl6_2),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ~r2_xboole_0(sK1,sK0) | ~r2_xboole_0(sK1,sK0) | ~spl6_2),
% 0.20/0.51    inference(resolution,[],[f58,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X2] : (~r2_hidden(sK4(sK1,X2),sK0) | ~r2_xboole_0(sK1,X2)) ) | ~spl6_2),
% 0.20/0.51    inference(resolution,[],[f55,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl6_2),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,sK1) | r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl6_2),
% 0.20/0.51    inference(resolution,[],[f45,f32])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,sK1)) | r2_hidden(X0,sK1)) ) | ~spl6_2),
% 0.20/0.51    inference(superposition,[],[f34,f43])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    spl6_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f12,f41])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ? [X0,X1] : (X0 != X1 & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 0.20/0.52    inference(negated_conjecture,[],[f7])).
% 0.20/0.52  fof(f7,conjecture,(
% 0.20/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ~spl6_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f13,f36])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    sK0 != sK1),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (31842)------------------------------
% 0.20/0.52  % (31842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31842)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (31842)Memory used [KB]: 10746
% 0.20/0.52  % (31842)Time elapsed: 0.073 s
% 0.20/0.52  % (31842)------------------------------
% 0.20/0.52  % (31842)------------------------------
% 0.20/0.52  % (31830)Refutation not found, incomplete strategy% (31830)------------------------------
% 0.20/0.52  % (31830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31830)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (31830)Memory used [KB]: 10618
% 0.20/0.52  % (31830)Time elapsed: 0.118 s
% 0.20/0.52  % (31830)------------------------------
% 0.20/0.52  % (31830)------------------------------
% 0.20/0.52  % (31820)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (31849)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (31819)Success in time 0.165 s
%------------------------------------------------------------------------------
