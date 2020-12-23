%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  71 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  121 ( 196 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f90,f138,f140])).

fof(f140,plain,
    ( ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f57,f110])).

fof(f110,plain,
    ( ~ r1_xboole_0(sK3(sK0),sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f96,f14])).

fof(f14,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r1_xboole_0(X1,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f96,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f79,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK3(X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f79,plain,
    ( r2_hidden(sK2(k1_xboole_0,sK0),sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl6_4
  <=> r2_hidden(sK2(k1_xboole_0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f57,plain,
    ( r1_xboole_0(sK3(sK0),sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl6_2
  <=> r1_xboole_0(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f138,plain,
    ( spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f136,f99])).

fof(f99,plain,
    ( sP4(sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f79,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | sP4(X1) ) ),
    inference(cnf_transformation,[],[f25_D])).

fof(f25_D,plain,(
    ! [X1] :
      ( ! [X0] : ~ r2_hidden(X0,X1)
    <=> ~ sP4(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f136,plain,
    ( ~ sP4(sK0)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f135,f61])).

fof(f61,plain,
    ( r2_hidden(sK1(sK3(sK0),sK0),sK3(sK0))
    | spl6_2 ),
    inference(resolution,[],[f58,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f58,plain,
    ( ~ r1_xboole_0(sK3(sK0),sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f135,plain,
    ( ~ r2_hidden(sK1(sK3(sK0),sK0),sK3(sK0))
    | ~ sP4(sK0)
    | spl6_2 ),
    inference(resolution,[],[f62,f26])).

fof(f26,plain,(
    ! [X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,sK3(X1))
      | ~ sP4(X1) ) ),
    inference(general_splitting,[],[f23,f25_D])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,sK3(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,
    ( r2_hidden(sK1(sK3(sK0),sK0),sK0)
    | spl6_2 ),
    inference(resolution,[],[f58,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f90,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f16,f75,f75,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f75,plain,
    ( r2_hidden(sK2(k1_xboole_0,sK0),k1_xboole_0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl6_3
  <=> r2_hidden(sK2(k1_xboole_0,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f16,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f80,plain,
    ( spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f34,f77,f73])).

fof(f34,plain,
    ( r2_hidden(sK2(k1_xboole_0,sK0),sK0)
    | r2_hidden(sK2(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(resolution,[],[f28,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0)
      | sQ5_eqProxy(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f21,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f28,plain,(
    ~ sQ5_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f15,f27])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:38:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (12766)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (12762)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (12774)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (12776)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (12774)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f141,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f80,f90,f138,f140])).
% 0.21/0.55  fof(f140,plain,(
% 0.21/0.55    ~spl6_2 | ~spl6_4),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f139])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    $false | (~spl6_2 | ~spl6_4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f57,f110])).
% 0.21/0.55  fof(f110,plain,(
% 0.21/0.55    ~r1_xboole_0(sK3(sK0),sK0) | ~spl6_4),
% 0.21/0.55    inference(resolution,[],[f96,f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.55    inference(negated_conjecture,[],[f6])).
% 0.21/0.55  fof(f6,conjecture,(
% 0.21/0.55    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    r2_hidden(sK3(sK0),sK0) | ~spl6_4),
% 0.21/0.55    inference(resolution,[],[f79,f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK3(X1),X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    r2_hidden(sK2(k1_xboole_0,sK0),sK0) | ~spl6_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f77])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    spl6_4 <=> r2_hidden(sK2(k1_xboole_0,sK0),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    r1_xboole_0(sK3(sK0),sK0) | ~spl6_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    spl6_2 <=> r1_xboole_0(sK3(sK0),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    spl6_2 | ~spl6_4),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f137])).
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    $false | (spl6_2 | ~spl6_4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f136,f99])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    sP4(sK0) | ~spl6_4),
% 0.21/0.55    inference(resolution,[],[f79,f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | sP4(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25_D])).
% 0.21/0.55  fof(f25_D,plain,(
% 0.21/0.55    ( ! [X1] : (( ! [X0] : ~r2_hidden(X0,X1) ) <=> ~sP4(X1)) )),
% 0.21/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    ~sP4(sK0) | spl6_2),
% 0.21/0.55    inference(subsumption_resolution,[],[f135,f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    r2_hidden(sK1(sK3(sK0),sK0),sK3(sK0)) | spl6_2),
% 0.21/0.55    inference(resolution,[],[f58,f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,plain,(
% 0.21/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ~r1_xboole_0(sK3(sK0),sK0) | spl6_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f56])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    ~r2_hidden(sK1(sK3(sK0),sK0),sK3(sK0)) | ~sP4(sK0) | spl6_2),
% 0.21/0.55    inference(resolution,[],[f62,f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ( ! [X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,sK3(X1)) | ~sP4(X1)) )),
% 0.21/0.55    inference(general_splitting,[],[f23,f25_D])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,sK3(X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    r2_hidden(sK1(sK3(sK0),sK0),sK0) | spl6_2),
% 0.21/0.55    inference(resolution,[],[f58,f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    ~spl6_3),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f82])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    $false | ~spl6_3),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f16,f75,f75,f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    r2_hidden(sK2(k1_xboole_0,sK0),k1_xboole_0) | ~spl6_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f73])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    spl6_3 <=> r2_hidden(sK2(k1_xboole_0,sK0),k1_xboole_0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    spl6_3 | spl6_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f34,f77,f73])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    r2_hidden(sK2(k1_xboole_0,sK0),sK0) | r2_hidden(sK2(k1_xboole_0,sK0),k1_xboole_0)),
% 0.21/0.55    inference(resolution,[],[f28,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | sQ5_eqProxy(X0,X1)) )),
% 0.21/0.55    inference(equality_proxy_replacement,[],[f21,f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.55    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X0 = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ~sQ5_eqProxy(k1_xboole_0,sK0)),
% 0.21/0.55    inference(equality_proxy_replacement,[],[f15,f27])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    k1_xboole_0 != sK0),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (12774)------------------------------
% 0.21/0.55  % (12774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12774)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (12774)Memory used [KB]: 6268
% 0.21/0.55  % (12774)Time elapsed: 0.082 s
% 0.21/0.55  % (12774)------------------------------
% 0.21/0.55  % (12774)------------------------------
% 0.21/0.56  % (12760)Success in time 0.192 s
%------------------------------------------------------------------------------
