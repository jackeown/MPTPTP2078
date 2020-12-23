%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  85 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  193 ( 281 expanded)
%              Number of equality atoms :   30 (  50 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f45,f49,f57,f70,f77,f80])).

fof(f80,plain,
    ( spl4_1
    | spl4_2
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f78,f75,f43,f39])).

fof(f39,plain,
    ( spl4_1
  <=> r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f43,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f75,plain,
    ( spl4_7
  <=> r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f78,plain,
    ( k1_xboole_0 = sK0
    | r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f76,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK2(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f76,plain,
    ( r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f77,plain,
    ( spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f73,f68,f75])).

fof(f68,plain,
    ( spl4_6
  <=> r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f73,plain,
    ( r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1)))
    | ~ spl4_6 ),
    inference(resolution,[],[f69,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f69,plain,
    ( r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f70,plain,
    ( spl4_6
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f65,f54,f47,f68])).

fof(f47,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f54,plain,
    ( spl4_4
  <=> r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f65,plain,
    ( r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f59,f48])).

fof(f48,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f59,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK0,X1)
        | r2_hidden(sK2(sK0,k1_setfam_1(sK1)),X1) )
    | ~ spl4_4 ),
    inference(resolution,[],[f55,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f36,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f55,plain,
    ( r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f57,plain,
    ( spl4_4
    | spl4_2
    | spl4_1 ),
    inference(avatar_split_clause,[],[f52,f39,f43,f54])).

fof(f52,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0)
    | spl4_1 ),
    inference(resolution,[],[f27,f40])).

fof(f40,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    & k1_xboole_0 != sK0
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
      & k1_xboole_0 != sK0
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f45,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f23,f43])).

fof(f23,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f24,f39])).

fof(f24,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:45:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (20653)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (20652)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (20661)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (20655)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (20660)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (20653)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f41,f45,f49,f57,f70,f77,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl4_1 | spl4_2 | ~spl4_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f78,f75,f43,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    spl4_1 <=> r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    spl4_2 <=> k1_xboole_0 = sK0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl4_7 <=> r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) | ~spl4_7),
% 0.21/0.50    inference(resolution,[],[f76,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X1,sK2(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1))) | ~spl4_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f75])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl4_7 | ~spl4_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f73,f68,f75])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    spl4_6 <=> r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1))) | ~spl4_6),
% 0.21/0.50    inference(resolution,[],[f69,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1) | ~spl4_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f68])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl4_6 | ~spl4_3 | ~spl4_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f65,f54,f47,f68])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    spl4_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    spl4_4 <=> r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1) | (~spl4_3 | ~spl4_4)),
% 0.21/0.50    inference(resolution,[],[f59,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    r1_tarski(sK0,sK1) | ~spl4_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f47])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_tarski(sK0,X1) | r2_hidden(sK2(sK0,k1_setfam_1(sK1)),X1)) ) | ~spl4_4),
% 0.21/0.50    inference(resolution,[],[f55,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(superposition,[],[f36,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(rectify,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0) | ~spl4_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f54])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    spl4_4 | spl4_2 | spl4_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f39,f43,f54])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0) | spl4_1),
% 0.21/0.50    inference(resolution,[],[f27,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) | spl4_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f39])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK2(X0,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f47])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    r1_tarski(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0 & r1_tarski(X0,X1)) => (~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0 & r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0,X1] : ((~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0) & r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.50    inference(negated_conjecture,[],[f5])).
% 0.21/0.50  fof(f5,conjecture,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ~spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f43])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    k1_xboole_0 != sK0),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ~spl4_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f39])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (20653)------------------------------
% 0.21/0.50  % (20653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (20653)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (20653)Memory used [KB]: 10618
% 0.21/0.50  % (20653)Time elapsed: 0.062 s
% 0.21/0.50  % (20653)------------------------------
% 0.21/0.50  % (20653)------------------------------
% 0.21/0.50  % (20646)Success in time 0.138 s
%------------------------------------------------------------------------------
