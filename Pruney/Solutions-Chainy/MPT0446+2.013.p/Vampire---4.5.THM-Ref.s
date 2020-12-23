%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 102 expanded)
%              Number of leaves         :   13 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  207 ( 395 expanded)
%              Number of equality atoms :   17 (  31 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f47,f52,f60,f63,f69,f72])).

fof(f72,plain,
    ( spl4_2
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f70,f67,f50,f37])).

fof(f37,plain,
    ( spl4_2
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f50,plain,
    ( spl4_5
  <=> k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f67,plain,
    ( spl4_7
  <=> r2_hidden(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f70,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(resolution,[],[f68,f54])).

fof(f54,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK2))
        | r2_hidden(X1,k3_relat_1(sK2)) )
    | ~ spl4_5 ),
    inference(superposition,[],[f30,f51])).

fof(f51,plain,
    ( k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f30,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f68,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f69,plain,
    ( spl4_7
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f65,f45,f41,f67])).

fof(f41,plain,
    ( spl4_3
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f45,plain,
    ( spl4_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f65,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f64,f42])).

fof(f42,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(X1,k2_relat_1(sK2)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f23,f46])).

fof(f46,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f63,plain,
    ( spl4_1
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f61,f58,f50,f34])).

fof(f34,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f58,plain,
    ( spl4_6
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f61,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f59,f53])).

fof(f53,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(X0,k3_relat_1(sK2)) )
    | ~ spl4_5 ),
    inference(superposition,[],[f31,f51])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f60,plain,
    ( spl4_6
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f56,f45,f41,f58])).

fof(f56,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f55,f42])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f22,f46])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f48,f45,f50])).

fof(f48,plain,
    ( k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl4_4 ),
    inference(resolution,[],[f21,f46])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f47,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( ~ r2_hidden(sK1,k3_relat_1(sK2))
      | ~ r2_hidden(sK0,k3_relat_1(sK2)) )
    & r2_hidden(k4_tarski(sK0,sK1),sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,k3_relat_1(X2))
          | ~ r2_hidden(X0,k3_relat_1(X2)) )
        & r2_hidden(k4_tarski(X0,X1),X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK1,k3_relat_1(sK2))
        | ~ r2_hidden(sK0,k3_relat_1(sK2)) )
      & r2_hidden(k4_tarski(sK0,sK1),sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
         => ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f43,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f39,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f20,f37,f34])).

fof(f20,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:43:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (30575)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (30583)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (30572)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (30575)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f39,f43,f47,f52,f60,f63,f69,f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl4_2 | ~spl4_5 | ~spl4_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f70,f67,f50,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    spl4_2 <=> r2_hidden(sK1,k3_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl4_5 <=> k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl4_7 <=> r2_hidden(sK1,k2_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    r2_hidden(sK1,k3_relat_1(sK2)) | (~spl4_5 | ~spl4_7)),
% 0.21/0.47    inference(resolution,[],[f68,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK2)) | r2_hidden(X1,k3_relat_1(sK2))) ) | ~spl4_5),
% 0.21/0.47    inference(superposition,[],[f30,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl4_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f50])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.47    inference(rectify,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl4_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f67])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl4_7 | ~spl4_3 | ~spl4_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f65,f45,f41,f67])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    spl4_3 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    spl4_4 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    r2_hidden(sK1,k2_relat_1(sK2)) | (~spl4_3 | ~spl4_4)),
% 0.21/0.47    inference(resolution,[],[f64,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl4_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f41])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(X1,k2_relat_1(sK2))) ) | ~spl4_4),
% 0.21/0.47    inference(resolution,[],[f23,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    v1_relat_1(sK2) | ~spl4_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f45])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k2_relat_1(X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl4_1 | ~spl4_5 | ~spl4_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f61,f58,f50,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    spl4_1 <=> r2_hidden(sK0,k3_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl4_6 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    r2_hidden(sK0,k3_relat_1(sK2)) | (~spl4_5 | ~spl4_6)),
% 0.21/0.47    inference(resolution,[],[f59,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(X0,k3_relat_1(sK2))) ) | ~spl4_5),
% 0.21/0.47    inference(superposition,[],[f31,f51])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl4_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl4_6 | ~spl4_3 | ~spl4_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f56,f45,f41,f58])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    r2_hidden(sK0,k1_relat_1(sK2)) | (~spl4_3 | ~spl4_4)),
% 0.21/0.47    inference(resolution,[],[f55,f42])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(X0,k1_relat_1(sK2))) ) | ~spl4_4),
% 0.21/0.47    inference(resolution,[],[f22,f46])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl4_5 | ~spl4_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f48,f45,f50])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl4_4),
% 0.21/0.47    inference(resolution,[],[f21,f46])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl4_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f18,f45])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    v1_relat_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    (~r2_hidden(sK1,k3_relat_1(sK2)) | ~r2_hidden(sK0,k3_relat_1(sK2))) & r2_hidden(k4_tarski(sK0,sK1),sK2) & v1_relat_1(sK2)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2) & v1_relat_1(X2)) => ((~r2_hidden(sK1,k3_relat_1(sK2)) | ~r2_hidden(sK0,k3_relat_1(sK2))) & r2_hidden(k4_tarski(sK0,sK1),sK2) & v1_relat_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2) & v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl4_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f41])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ~spl4_1 | ~spl4_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f20,f37,f34])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ~r2_hidden(sK1,k3_relat_1(sK2)) | ~r2_hidden(sK0,k3_relat_1(sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (30575)------------------------------
% 0.21/0.47  % (30575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (30575)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (30575)Memory used [KB]: 10618
% 0.21/0.47  % (30575)Time elapsed: 0.054 s
% 0.21/0.47  % (30575)------------------------------
% 0.21/0.47  % (30575)------------------------------
% 0.21/0.47  % (30568)Success in time 0.108 s
%------------------------------------------------------------------------------
