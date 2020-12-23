%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  75 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  128 ( 212 expanded)
%              Number of equality atoms :   22 (  42 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f37,f41,f53,f62])).

fof(f62,plain,
    ( spl3_2
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f60,f51,f31,f35])).

fof(f35,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f31,plain,
    ( spl3_1
  <=> r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f51,plain,
    ( spl3_4
  <=> ! [X5] :
        ( r1_tarski(X5,k1_setfam_1(sK0))
        | r1_tarski(k1_tarski(sK2(sK0,X5)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f60,plain,
    ( r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    | k1_xboole_0 = sK0
    | ~ spl3_4 ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,
    ( r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    | k1_xboole_0 = sK0
    | r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f57,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK2(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f57,plain,
    ( ! [X1] :
        ( r1_tarski(k1_setfam_1(sK1),sK2(sK0,X1))
        | r1_tarski(X1,k1_setfam_1(sK0)) )
    | ~ spl3_4 ),
    inference(resolution,[],[f54,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f54,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK0,X0),sK1)
        | r1_tarski(X0,k1_setfam_1(sK0)) )
    | ~ spl3_4 ),
    inference(resolution,[],[f52,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f52,plain,
    ( ! [X5] :
        ( r1_tarski(k1_tarski(sK2(sK0,X5)),sK1)
        | r1_tarski(X5,k1_setfam_1(sK0)) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f53,plain,
    ( spl3_2
    | spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f48,f39,f51,f35])).

fof(f39,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f48,plain,
    ( ! [X5] :
        ( r1_tarski(X5,k1_setfam_1(sK0))
        | k1_xboole_0 = sK0
        | r1_tarski(k1_tarski(sK2(sK0,X5)),sK1) )
    | ~ spl3_3 ),
    inference(resolution,[],[f44,f43])).

fof(f43,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,sK1) )
    | ~ spl3_3 ),
    inference(resolution,[],[f42,f40])).

fof(f40,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f29,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(sK2(X0,X1)),X0)
      | r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f25,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    & k1_xboole_0 != sK0
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
      & k1_xboole_0 != sK0
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f37,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f21,f35])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f22,f31])).

fof(f22,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:11:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (3094)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (3090)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (3082)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (3082)Refutation not found, incomplete strategy% (3082)------------------------------
% 0.21/0.48  % (3082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3082)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (3082)Memory used [KB]: 6140
% 0.21/0.48  % (3082)Time elapsed: 0.060 s
% 0.21/0.48  % (3082)------------------------------
% 0.21/0.48  % (3082)------------------------------
% 0.21/0.49  % (3089)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (3088)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (3087)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (3088)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f33,f37,f41,f53,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl3_2 | spl3_1 | ~spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f60,f51,f31,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    spl3_2 <=> k1_xboole_0 = sK0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    spl3_1 <=> r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl3_4 <=> ! [X5] : (r1_tarski(X5,k1_setfam_1(sK0)) | r1_tarski(k1_tarski(sK2(sK0,X5)),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) | k1_xboole_0 = sK0 | ~spl3_4),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) | k1_xboole_0 = sK0 | r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) | ~spl3_4),
% 0.21/0.49    inference(resolution,[],[f57,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X1,sK2(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(k1_setfam_1(sK1),sK2(sK0,X1)) | r1_tarski(X1,k1_setfam_1(sK0))) ) | ~spl3_4),
% 0.21/0.49    inference(resolution,[],[f54,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK2(sK0,X0),sK1) | r1_tarski(X0,k1_setfam_1(sK0))) ) | ~spl3_4),
% 0.21/0.49    inference(resolution,[],[f52,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X5] : (r1_tarski(k1_tarski(sK2(sK0,X5)),sK1) | r1_tarski(X5,k1_setfam_1(sK0))) ) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f51])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl3_2 | spl3_4 | ~spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f39,f51,f35])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X5] : (r1_tarski(X5,k1_setfam_1(sK0)) | k1_xboole_0 = sK0 | r1_tarski(k1_tarski(sK2(sK0,X5)),sK1)) ) | ~spl3_3),
% 0.21/0.49    inference(resolution,[],[f44,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,sK1)) ) | ~spl3_3),
% 0.21/0.49    inference(resolution,[],[f42,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f39])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(superposition,[],[f29,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(sK2(X0,X1)),X0) | r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(resolution,[],[f25,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f39])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    r1_tarski(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0 & r1_tarski(X0,X1)) => (~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0 & r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1] : ((~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0) & r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f35])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    k1_xboole_0 != sK0),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ~spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f31])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (3088)------------------------------
% 0.21/0.49  % (3088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3088)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (3088)Memory used [KB]: 10618
% 0.21/0.49  % (3085)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (3088)Time elapsed: 0.083 s
% 0.21/0.49  % (3088)------------------------------
% 0.21/0.49  % (3088)------------------------------
% 0.21/0.49  % (3097)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (3086)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (3081)Success in time 0.134 s
%------------------------------------------------------------------------------
