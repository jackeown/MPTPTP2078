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
% DateTime   : Thu Dec  3 12:30:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 141 expanded)
%              Number of leaves         :   16 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  227 ( 591 expanded)
%              Number of equality atoms :   24 (  49 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f491,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f54,f65,f70,f127,f131,f485])).

fof(f485,plain,
    ( spl5_10
    | spl5_11
    | spl5_1
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f472,f68,f44,f129,f125])).

fof(f125,plain,
    ( spl5_10
  <=> r2_hidden(sK3(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f129,plain,
    ( spl5_11
  <=> r2_hidden(sK3(sK0,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f44,plain,
    ( spl5_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f68,plain,
    ( spl5_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f472,plain,
    ( r2_hidden(sK3(sK0,sK2),k1_xboole_0)
    | r2_hidden(sK3(sK0,sK2),sK1)
    | spl5_1
    | ~ spl5_6 ),
    inference(superposition,[],[f463,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f463,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,sK2),k4_xboole_0(sK0,X0))
        | r2_hidden(sK3(sK0,sK2),X0) )
    | spl5_1 ),
    inference(resolution,[],[f107,f45])).

fof(f45,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),k4_xboole_0(X0,X2))
      | r2_hidden(sK3(X0,X1),X2) ) ),
    inference(resolution,[],[f40,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X1)
      | r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f131,plain,
    ( ~ spl5_11
    | spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f123,f48,f44,f129])).

fof(f48,plain,
    ( spl5_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f123,plain,
    ( ~ r2_hidden(sK3(sK0,sK2),k1_xboole_0)
    | spl5_1
    | ~ spl5_2 ),
    inference(superposition,[],[f119,f28])).

fof(f28,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f119,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK0,sK2),k4_xboole_0(sK1,X0))
    | spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f88,f45])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,sK2)
        | ~ r2_hidden(sK3(X0,sK2),k4_xboole_0(sK1,X1)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f77,f42])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(X1,sK2),sK1)
        | r1_xboole_0(X1,sK2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f74,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f31,f49])).

fof(f49,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f127,plain,
    ( ~ spl5_10
    | spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f122,f48,f44,f125])).

fof(f122,plain,
    ( ~ r2_hidden(sK3(sK0,sK2),sK1)
    | spl5_1
    | ~ spl5_2 ),
    inference(superposition,[],[f119,f27])).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f70,plain,
    ( spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f66,f63,f68])).

fof(f63,plain,
    ( spl5_5
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f66,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_5 ),
    inference(superposition,[],[f28,f64])).

fof(f64,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f65,plain,
    ( spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f61,f52,f63])).

fof(f52,plain,
    ( spl5_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f61,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f32,f53])).

fof(f53,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f54,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f50,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f25,f48])).

fof(f25,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f26,f44])).

fof(f26,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:00:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (18785)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (18794)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (18786)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (18779)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (18785)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f491,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f46,f50,f54,f65,f70,f127,f131,f485])).
% 0.20/0.49  fof(f485,plain,(
% 0.20/0.49    spl5_10 | spl5_11 | spl5_1 | ~spl5_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f472,f68,f44,f129,f125])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    spl5_10 <=> r2_hidden(sK3(sK0,sK2),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    spl5_11 <=> r2_hidden(sK3(sK0,sK2),k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    spl5_1 <=> r1_xboole_0(sK0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl5_6 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.49  fof(f472,plain,(
% 0.20/0.49    r2_hidden(sK3(sK0,sK2),k1_xboole_0) | r2_hidden(sK3(sK0,sK2),sK1) | (spl5_1 | ~spl5_6)),
% 0.20/0.49    inference(superposition,[],[f463,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl5_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f68])).
% 0.20/0.49  fof(f463,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK3(sK0,sK2),k4_xboole_0(sK0,X0)) | r2_hidden(sK3(sK0,sK2),X0)) ) | spl5_1),
% 0.20/0.49    inference(resolution,[],[f107,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,sK2) | spl5_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f44])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),k4_xboole_0(X0,X2)) | r2_hidden(sK3(X0,X1),X2)) )),
% 0.20/0.49    inference(resolution,[],[f40,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(rectify,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,X0) | r2_hidden(X4,X1) | r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(equality_resolution,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(rectify,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(flattening,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    ~spl5_11 | spl5_1 | ~spl5_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f123,f48,f44,f129])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    spl5_2 <=> r1_xboole_0(sK1,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    ~r2_hidden(sK3(sK0,sK2),k1_xboole_0) | (spl5_1 | ~spl5_2)),
% 0.20/0.49    inference(superposition,[],[f119,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(sK3(sK0,sK2),k4_xboole_0(sK1,X0))) ) | (spl5_1 | ~spl5_2)),
% 0.20/0.49    inference(resolution,[],[f88,f45])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,sK2) | ~r2_hidden(sK3(X0,sK2),k4_xboole_0(sK1,X1))) ) | ~spl5_2),
% 0.20/0.49    inference(resolution,[],[f77,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(equality_resolution,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X1] : (~r2_hidden(sK3(X1,sK2),sK1) | r1_xboole_0(X1,sK2)) ) | ~spl5_2),
% 0.20/0.49    inference(resolution,[],[f74,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1)) ) | ~spl5_2),
% 0.20/0.49    inference(resolution,[],[f31,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    r1_xboole_0(sK1,sK2) | ~spl5_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f48])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    ~spl5_10 | spl5_1 | ~spl5_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f122,f48,f44,f125])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    ~r2_hidden(sK3(sK0,sK2),sK1) | (spl5_1 | ~spl5_2)),
% 0.20/0.49    inference(superposition,[],[f119,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    spl5_6 | ~spl5_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f66,f63,f68])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    spl5_5 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl5_5),
% 0.20/0.49    inference(superposition,[],[f28,f64])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    sK1 = k2_xboole_0(sK0,sK1) | ~spl5_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f63])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    spl5_5 | ~spl5_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f61,f52,f63])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    spl5_3 <=> r1_tarski(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    sK1 = k2_xboole_0(sK0,sK1) | ~spl5_3),
% 0.20/0.49    inference(resolution,[],[f32,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    r1_tarski(sK0,sK1) | ~spl5_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f52])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    spl5_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f24,f52])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    r1_tarski(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.49    inference(negated_conjecture,[],[f7])).
% 0.20/0.49  fof(f7,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    spl5_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f25,f48])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    r1_xboole_0(sK1,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ~spl5_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f26,f44])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (18785)------------------------------
% 0.20/0.49  % (18785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18785)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (18785)Memory used [KB]: 11001
% 0.20/0.49  % (18785)Time elapsed: 0.031 s
% 0.20/0.49  % (18785)------------------------------
% 0.20/0.49  % (18785)------------------------------
% 0.20/0.49  % (18778)Success in time 0.128 s
%------------------------------------------------------------------------------
