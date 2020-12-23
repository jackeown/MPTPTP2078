%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  77 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  126 ( 224 expanded)
%              Number of equality atoms :   15 (  42 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f57,f76])).

fof(f76,plain,
    ( spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f75,f43,f52])).

fof(f52,plain,
    ( spl5_3
  <=> r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f43,plain,
    ( spl5_1
  <=> r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f75,plain,
    ( r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1)))
    | ~ spl5_1 ),
    inference(resolution,[],[f66,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f66,plain,
    ( r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f45,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f20,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    & k1_xboole_0 != sK0
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
      & k1_xboole_0 != sK0
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f45,plain,
    ( r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f57,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | ~ spl5_2 ),
    inference(resolution,[],[f49,f30])).

fof(f30,plain,(
    ~ sQ4_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f21,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,
    ( sQ4_eqProxy(k1_xboole_0,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl5_2
  <=> sQ4_eqProxy(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f55,plain,
    ( ~ spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f39,f47,f52])).

fof(f39,plain,
    ( sQ4_eqProxy(k1_xboole_0,sK0)
    | ~ r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1))) ),
    inference(resolution,[],[f22,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | sQ4_eqProxy(k1_xboole_0,X0)
      | ~ r1_tarski(X1,sK2(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f25,f29])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f22,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f38,f47,f43])).

fof(f38,plain,
    ( sQ4_eqProxy(k1_xboole_0,sK0)
    | r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0) ),
    inference(resolution,[],[f22,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | sQ4_eqProxy(k1_xboole_0,X0)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f24,f29])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (3201)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (3195)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (3209)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (3209)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f50,f55,f57,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    spl5_3 | ~spl5_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f75,f43,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    spl5_3 <=> r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    spl5_1 <=> r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1))) | ~spl5_1),
% 0.20/0.51    inference(resolution,[],[f66,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1) | ~spl5_1),
% 0.20/0.51    inference(resolution,[],[f45,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK1)) )),
% 0.20/0.51    inference(resolution,[],[f20,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0 & r1_tarski(X0,X1)) => (~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f7,plain,(
% 0.20/0.51    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0 & r1_tarski(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f6])).
% 0.20/0.51  fof(f6,plain,(
% 0.20/0.51    ? [X0,X1] : ((~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0) & r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.20/0.51    inference(negated_conjecture,[],[f4])).
% 0.20/0.51  fof(f4,conjecture,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0) | ~spl5_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f43])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ~spl5_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    $false | ~spl5_2),
% 0.20/0.51    inference(resolution,[],[f49,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ~sQ4_eqProxy(k1_xboole_0,sK0)),
% 0.20/0.51    inference(equality_proxy_replacement,[],[f21,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.51    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    k1_xboole_0 != sK0),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    sQ4_eqProxy(k1_xboole_0,sK0) | ~spl5_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    spl5_2 <=> sQ4_eqProxy(k1_xboole_0,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ~spl5_3 | spl5_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f39,f47,f52])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    sQ4_eqProxy(k1_xboole_0,sK0) | ~r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1)))),
% 0.20/0.51    inference(resolution,[],[f22,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | sQ4_eqProxy(k1_xboole_0,X0) | ~r1_tarski(X1,sK2(X0,X1))) )),
% 0.20/0.51    inference(equality_proxy_replacement,[],[f25,f29])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK2(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.20/0.51    inference(flattening,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    spl5_1 | spl5_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f38,f47,f43])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    sQ4_eqProxy(k1_xboole_0,sK0) | r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0)),
% 0.20/0.51    inference(resolution,[],[f22,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | sQ4_eqProxy(k1_xboole_0,X0) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.20/0.51    inference(equality_proxy_replacement,[],[f24,f29])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK2(X0,X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (3209)------------------------------
% 0.20/0.51  % (3209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3209)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (3209)Memory used [KB]: 6140
% 0.20/0.51  % (3209)Time elapsed: 0.106 s
% 0.20/0.51  % (3209)------------------------------
% 0.20/0.51  % (3209)------------------------------
% 0.20/0.51  % (3193)Success in time 0.152 s
%------------------------------------------------------------------------------
