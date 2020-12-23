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
% DateTime   : Thu Dec  3 12:48:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  99 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   15
%              Number of atoms          :  151 ( 272 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f217,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f56,f62,f216])).

fof(f216,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f208,f61])).

fof(f61,plain,
    ( sK1 != k5_relat_1(sK1,k6_relat_1(sK0))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_3
  <=> sK1 = k5_relat_1(sK1,k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f208,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(sK0))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f199,f55])).

fof(f55,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_2
  <=> r1_tarski(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f199,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k2_relat_1(sK1),X3)
        | sK1 = k5_relat_1(sK1,k6_relat_1(X3)) )
    | ~ spl5_1 ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,
    ( ! [X3] :
        ( sK1 = k5_relat_1(sK1,k6_relat_1(X3))
        | ~ r1_tarski(k2_relat_1(sK1),X3)
        | sK1 = k5_relat_1(sK1,k6_relat_1(X3)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f133,f117])).

fof(f117,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(X0))),k2_relat_1(sK1))
        | sK1 = k5_relat_1(sK1,k6_relat_1(X0)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f83,f49])).

fof(f49,plain,
    ( ! [X10,X9] :
        ( ~ r2_hidden(k4_tarski(X9,X10),sK1)
        | r2_hidden(X10,k2_relat_1(sK1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f41,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl5_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f83,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(X1))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(X1)))),sK1)
        | sK1 = k5_relat_1(sK1,k6_relat_1(X1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f63,f44])).

fof(f44,plain,
    ( ! [X3] :
        ( r1_tarski(sK1,X3)
        | r2_hidden(k4_tarski(sK2(sK1,X3),sK3(sK1,X3)),sK1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f41,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f63,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X0)))
        | sK1 = k5_relat_1(sK1,k6_relat_1(X0)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f46,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f46,plain,
    ( ! [X5] : r1_tarski(k5_relat_1(sK1,k6_relat_1(X5)),sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f41,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(X0))),X1)
        | sK1 = k5_relat_1(sK1,k6_relat_1(X0))
        | ~ r1_tarski(X1,X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f127,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f127,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(X0))),X0)
        | sK1 = k5_relat_1(sK1,k6_relat_1(X0)) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f126,f83])).

fof(f126,plain,
    ( ! [X0] :
        ( sK1 = k5_relat_1(sK1,k6_relat_1(X0))
        | ~ r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(X0))),X0)
        | ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(X0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(X0)))),sK1) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f124,f41])).

fof(f124,plain,
    ( ! [X0] :
        ( sK1 = k5_relat_1(sK1,k6_relat_1(X0))
        | ~ r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(X0))),X0)
        | ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(X0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(X0)))),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f82,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X3)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).

fof(f82,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(X0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(X0)))),k5_relat_1(sK1,k6_relat_1(X0)))
        | sK1 = k5_relat_1(sK1,k6_relat_1(X0)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f63,f45])).

fof(f45,plain,
    ( ! [X4] :
        ( r1_tarski(sK1,X4)
        | ~ r2_hidden(k4_tarski(sK2(sK1,X4),sK3(sK1,X4)),X4) )
    | ~ spl5_1 ),
    inference(resolution,[],[f41,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f62,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f19,f59])).

fof(f19,plain,(
    sK1 != k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k2_relat_1(X1),X0)
         => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f56,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f18,f53])).

fof(f18,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (21792)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.46  % (21809)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.46  % (21799)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.47  % (21799)Refutation not found, incomplete strategy% (21799)------------------------------
% 0.20/0.47  % (21799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (21799)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (21799)Memory used [KB]: 10618
% 0.20/0.48  % (21799)Time elapsed: 0.091 s
% 0.20/0.48  % (21799)------------------------------
% 0.20/0.48  % (21799)------------------------------
% 0.20/0.49  % (21809)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f217,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f42,f56,f62,f216])).
% 0.20/0.49  fof(f216,plain,(
% 0.20/0.49    ~spl5_1 | ~spl5_2 | spl5_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f215])).
% 0.20/0.49  fof(f215,plain,(
% 0.20/0.49    $false | (~spl5_1 | ~spl5_2 | spl5_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f208,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    sK1 != k5_relat_1(sK1,k6_relat_1(sK0)) | spl5_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    spl5_3 <=> sK1 = k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.49  fof(f208,plain,(
% 0.20/0.49    sK1 = k5_relat_1(sK1,k6_relat_1(sK0)) | (~spl5_1 | ~spl5_2)),
% 0.20/0.49    inference(resolution,[],[f199,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    r1_tarski(k2_relat_1(sK1),sK0) | ~spl5_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    spl5_2 <=> r1_tarski(k2_relat_1(sK1),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    ( ! [X3] : (~r1_tarski(k2_relat_1(sK1),X3) | sK1 = k5_relat_1(sK1,k6_relat_1(X3))) ) | ~spl5_1),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f190])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    ( ! [X3] : (sK1 = k5_relat_1(sK1,k6_relat_1(X3)) | ~r1_tarski(k2_relat_1(sK1),X3) | sK1 = k5_relat_1(sK1,k6_relat_1(X3))) ) | ~spl5_1),
% 0.20/0.49    inference(resolution,[],[f133,f117])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(X0))),k2_relat_1(sK1)) | sK1 = k5_relat_1(sK1,k6_relat_1(X0))) ) | ~spl5_1),
% 0.20/0.49    inference(resolution,[],[f83,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X10,X9] : (~r2_hidden(k4_tarski(X9,X10),sK1) | r2_hidden(X10,k2_relat_1(sK1))) ) | ~spl5_1),
% 0.20/0.49    inference(resolution,[],[f41,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k2_relat_1(X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    v1_relat_1(sK1) | ~spl5_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    spl5_1 <=> v1_relat_1(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ( ! [X1] : (r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(X1))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(X1)))),sK1) | sK1 = k5_relat_1(sK1,k6_relat_1(X1))) ) | ~spl5_1),
% 0.20/0.49    inference(resolution,[],[f63,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X3] : (r1_tarski(sK1,X3) | r2_hidden(k4_tarski(sK2(sK1,X3),sK3(sK1,X3)),sK1)) ) | ~spl5_1),
% 0.20/0.49    inference(resolution,[],[f41,f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X0))) | sK1 = k5_relat_1(sK1,k6_relat_1(X0))) ) | ~spl5_1),
% 0.20/0.49    inference(resolution,[],[f46,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X5] : (r1_tarski(k5_relat_1(sK1,k6_relat_1(X5)),sK1)) ) | ~spl5_1),
% 0.20/0.49    inference(resolution,[],[f41,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(X0))),X1) | sK1 = k5_relat_1(sK1,k6_relat_1(X0)) | ~r1_tarski(X1,X0)) ) | ~spl5_1),
% 0.20/0.49    inference(resolution,[],[f127,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(X0))),X0) | sK1 = k5_relat_1(sK1,k6_relat_1(X0))) ) | ~spl5_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f126,f83])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    ( ! [X0] : (sK1 = k5_relat_1(sK1,k6_relat_1(X0)) | ~r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(X0))),X0) | ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(X0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(X0)))),sK1)) ) | ~spl5_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f124,f41])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    ( ! [X0] : (sK1 = k5_relat_1(sK1,k6_relat_1(X0)) | ~r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(X0))),X0) | ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(X0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(X0)))),sK1) | ~v1_relat_1(sK1)) ) | ~spl5_1),
% 0.20/0.49    inference(resolution,[],[f82,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~r2_hidden(X1,X2) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~v1_relat_1(X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))) | ~v1_relat_1(X3))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(X0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(X0)))),k5_relat_1(sK1,k6_relat_1(X0))) | sK1 = k5_relat_1(sK1,k6_relat_1(X0))) ) | ~spl5_1),
% 0.20/0.49    inference(resolution,[],[f63,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X4] : (r1_tarski(sK1,X4) | ~r2_hidden(k4_tarski(sK2(sK1,X4),sK3(sK1,X4)),X4)) ) | ~spl5_1),
% 0.20/0.49    inference(resolution,[],[f41,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ~spl5_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f19,f59])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    sK1 != k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ? [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) != X1 & r1_tarski(k2_relat_1(X1),X0) & v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ? [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) != X1 & r1_tarski(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.50    inference(negated_conjecture,[],[f7])).
% 0.20/0.50  fof(f7,conjecture,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    spl5_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f18,f53])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    spl5_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f17,f39])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    v1_relat_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (21809)------------------------------
% 0.20/0.50  % (21809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21809)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (21809)Memory used [KB]: 10874
% 0.20/0.50  % (21809)Time elapsed: 0.095 s
% 0.20/0.50  % (21809)------------------------------
% 0.20/0.50  % (21809)------------------------------
% 0.20/0.50  % (21788)Success in time 0.141 s
%------------------------------------------------------------------------------
