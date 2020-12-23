%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  81 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  159 ( 284 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f87,f91])).

fof(f91,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | ~ spl5_1 ),
    inference(resolution,[],[f70,f26])).

fof(f26,plain,(
    ~ r1_xboole_0(k1_setfam_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_xboole_0(k1_setfam_1(sK1),sK2)
    & r1_xboole_0(sK0,sK2)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
        & r1_xboole_0(X0,X2)
        & r2_hidden(X0,X1) )
   => ( ~ r1_xboole_0(k1_setfam_1(sK1),sK2)
      & r1_xboole_0(sK0,sK2)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
      & r1_xboole_0(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
      & r1_xboole_0(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r2_hidden(X0,X1) )
       => r1_xboole_0(k1_setfam_1(X1),X2) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_xboole_0(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).

fof(f70,plain,
    ( r1_xboole_0(k1_setfam_1(sK1),sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_1
  <=> r1_xboole_0(k1_setfam_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f87,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | ~ spl5_2 ),
    inference(resolution,[],[f83,f24])).

fof(f24,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f73,f37])).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f73,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_2
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f74,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f64,f72,f68])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | ~ r2_hidden(X0,sK1)
      | r1_xboole_0(k1_setfam_1(sK1),sK2) ) ),
    inference(resolution,[],[f62,f43])).

fof(f43,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(X1,sK2),sK0)
      | r1_xboole_0(X1,sK2) ) ),
    inference(resolution,[],[f39,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f39,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f29,f25])).

fof(f25,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k1_setfam_1(sK1),sK2),X1)
      | ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f56,f26])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k1_setfam_1(X1),X3)
      | ~ r1_tarski(X0,X2)
      | r2_hidden(sK3(k1_setfam_1(X1),X3),X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f52,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_setfam_1(X2))
      | ~ r2_hidden(X0,X2)
      | ~ r1_tarski(X0,X1)
      | r2_hidden(X3,X1) ) ),
    inference(resolution,[],[f36,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.20/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 17:23:19 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.47  % (16629)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.48  % (16621)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (16637)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.48  % (16613)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (16621)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (16628)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.49  % (16620)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f74,f87,f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ~spl5_1),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    $false | ~spl5_1),
% 0.20/0.49    inference(resolution,[],[f70,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ~r1_xboole_0(k1_setfam_1(sK1),sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ~r1_xboole_0(k1_setfam_1(sK1),sK2) & r1_xboole_0(sK0,sK2) & r2_hidden(sK0,sK1)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_xboole_0(k1_setfam_1(X1),X2) & r1_xboole_0(X0,X2) & r2_hidden(X0,X1)) => (~r1_xboole_0(k1_setfam_1(sK1),sK2) & r1_xboole_0(sK0,sK2) & r2_hidden(sK0,sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_xboole_0(k1_setfam_1(X1),X2) & r1_xboole_0(X0,X2) & r2_hidden(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_xboole_0(k1_setfam_1(X1),X2) & (r1_xboole_0(X0,X2) & r2_hidden(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r2_hidden(X0,X1)) => r1_xboole_0(k1_setfam_1(X1),X2))),
% 0.20/0.49    inference(negated_conjecture,[],[f5])).
% 0.20/0.49  fof(f5,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r2_hidden(X0,X1)) => r1_xboole_0(k1_setfam_1(X1),X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    r1_xboole_0(k1_setfam_1(sK1),sK2) | ~spl5_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl5_1 <=> r1_xboole_0(k1_setfam_1(sK1),sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ~spl5_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    $false | ~spl5_2),
% 0.20/0.49    inference(resolution,[],[f83,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    r2_hidden(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ~r2_hidden(sK0,sK1) | ~spl5_2),
% 0.20/0.49    inference(resolution,[],[f73,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(X0,sK0) | ~r2_hidden(X0,sK1)) ) | ~spl5_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    spl5_2 <=> ! [X0] : (~r1_tarski(X0,sK0) | ~r2_hidden(X0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl5_1 | spl5_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f64,f72,f68])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(X0,sK0) | ~r2_hidden(X0,sK1) | r1_xboole_0(k1_setfam_1(sK1),sK2)) )),
% 0.20/0.49    inference(resolution,[],[f62,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X1] : (~r2_hidden(sK3(X1,sK2),sK0) | r1_xboole_0(X1,sK2)) )),
% 0.20/0.49    inference(resolution,[],[f39,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(rectify,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f29,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    r1_xboole_0(sK0,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK3(k1_setfam_1(sK1),sK2),X1) | ~r1_tarski(X0,X1) | ~r2_hidden(X0,sK1)) )),
% 0.20/0.49    inference(resolution,[],[f56,f26])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k1_setfam_1(X1),X3) | ~r1_tarski(X0,X2) | r2_hidden(sK3(k1_setfam_1(X1),X3),X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(resolution,[],[f52,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k1_setfam_1(X2)) | ~r2_hidden(X0,X2) | ~r1_tarski(X0,X1) | r2_hidden(X3,X1)) )),
% 0.20/0.50    inference(resolution,[],[f36,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(rectify,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (16621)------------------------------
% 0.20/0.50  % (16621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16621)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (16621)Memory used [KB]: 6268
% 0.20/0.50  % (16621)Time elapsed: 0.084 s
% 0.20/0.50  % (16621)------------------------------
% 0.20/0.50  % (16621)------------------------------
% 0.20/0.50  % (16608)Success in time 0.134 s
%------------------------------------------------------------------------------
