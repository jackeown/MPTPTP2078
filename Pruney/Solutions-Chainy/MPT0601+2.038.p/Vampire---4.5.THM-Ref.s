%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 109 expanded)
%              Number of leaves         :   16 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  200 ( 372 expanded)
%              Number of equality atoms :   30 (  67 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f53,f57,f61,f106,f111,f120])).

fof(f120,plain,
    ( spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f119,f104,f48])).

fof(f48,plain,
    ( spl6_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f104,plain,
    ( spl6_10
  <=> v1_xboole_0(k11_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f119,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f105,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f105,plain,
    ( v1_xboole_0(k11_relat_1(sK1,sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f111,plain,
    ( ~ spl6_1
    | ~ spl6_4
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f108,f55,f48,f59,f45])).

fof(f45,plain,
    ( spl6_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f59,plain,
    ( spl6_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f55,plain,
    ( spl6_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f108,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(superposition,[],[f78,f49])).

fof(f49,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k11_relat_1(sK1,X0))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f77,f34])).

fof(f34,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f77,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK1,X0),k11_relat_1(sK1,X0))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f76,f43])).

fof(f43,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f24,f23,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

% (4154)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(X1,k11_relat_1(sK1,X0)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f40,f56])).

fof(f56,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f106,plain,
    ( spl6_10
    | spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f101,f55,f45,f104])).

fof(f101,plain,
    ( v1_xboole_0(k11_relat_1(sK1,sK0))
    | spl6_1
    | ~ spl6_3 ),
    inference(resolution,[],[f93,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f93,plain,
    ( ! [X0] : ~ r2_hidden(X0,k11_relat_1(sK1,sK0))
    | spl6_1
    | ~ spl6_3 ),
    inference(resolution,[],[f84,f46])).

fof(f46,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f84,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X3,k1_relat_1(sK1))
        | ~ r2_hidden(X2,k11_relat_1(sK1,X3)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f82,f42])).

fof(f42,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X1,X0),sK1)
        | ~ r2_hidden(X0,k11_relat_1(sK1,X1)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f41,f56])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f30,f59])).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f57,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f27,f55])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f53,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f28,f48,f45])).

fof(f28,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f29,f48,f45])).

fof(f29,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:58:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (4144)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (4140)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (4145)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (4145)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f50,f53,f57,f61,f106,f111,f120])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    spl6_2 | ~spl6_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f119,f104,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    spl6_2 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    spl6_10 <=> v1_xboole_0(k11_relat_1(sK1,sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl6_10),
% 0.22/0.49    inference(resolution,[],[f105,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    v1_xboole_0(k11_relat_1(sK1,sK0)) | ~spl6_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f104])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    ~spl6_1 | ~spl6_4 | ~spl6_2 | ~spl6_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f108,f55,f48,f59,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    spl6_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    spl6_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    spl6_3 <=> v1_relat_1(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    ~v1_xboole_0(k1_xboole_0) | ~r2_hidden(sK0,k1_relat_1(sK1)) | (~spl6_2 | ~spl6_3)),
% 0.22/0.49    inference(superposition,[],[f78,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl6_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f48])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(k11_relat_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl6_3),
% 0.22/0.49    inference(resolution,[],[f77,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.50    inference(rectify,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK5(sK1,X0),k11_relat_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl6_3),
% 0.22/0.50    inference(resolution,[],[f76,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 0.22/0.50    inference(equality_resolution,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f24,f23,f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  % (4154)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.50    inference(rectify,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X1,k11_relat_1(sK1,X0))) ) | ~spl6_3),
% 0.22/0.50    inference(resolution,[],[f40,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    v1_relat_1(sK1) | ~spl6_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f55])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    spl6_10 | spl6_1 | ~spl6_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f101,f55,f45,f104])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    v1_xboole_0(k11_relat_1(sK1,sK0)) | (spl6_1 | ~spl6_3)),
% 0.22/0.50    inference(resolution,[],[f93,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k11_relat_1(sK1,sK0))) ) | (spl6_1 | ~spl6_3)),
% 0.22/0.50    inference(resolution,[],[f84,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl6_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f45])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X2,X3] : (r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(X2,k11_relat_1(sK1,X3))) ) | ~spl6_3),
% 0.22/0.50    inference(resolution,[],[f82,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.22/0.50    inference(equality_resolution,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,X0),sK1) | ~r2_hidden(X0,k11_relat_1(sK1,X1))) ) | ~spl6_3),
% 0.22/0.50    inference(resolution,[],[f41,f56])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl6_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f59])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    spl6_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f27,f55])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    v1_relat_1(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.22/0.50    inference(negated_conjecture,[],[f7])).
% 0.22/0.50  fof(f7,conjecture,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    spl6_1 | ~spl6_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f48,f45])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ~spl6_1 | spl6_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f29,f48,f45])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (4145)------------------------------
% 0.22/0.50  % (4145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (4145)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (4145)Memory used [KB]: 10618
% 0.22/0.50  % (4145)Time elapsed: 0.065 s
% 0.22/0.50  % (4145)------------------------------
% 0.22/0.50  % (4145)------------------------------
% 0.22/0.50  % (4136)Success in time 0.137 s
%------------------------------------------------------------------------------
