%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 164 expanded)
%              Number of leaves         :   17 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  263 ( 727 expanded)
%              Number of equality atoms :   20 (  62 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f54,f60,f64,f68,f86,f112,f114,f128,f132])).

fof(f132,plain,
    ( ~ spl4_3
    | spl4_1
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f130,f103,f41,f52])).

fof(f52,plain,
    ( spl4_3
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f41,plain,
    ( spl4_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f103,plain,
    ( spl4_11
  <=> v2_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f130,plain,
    ( v3_ordinal1(sK0)
    | ~ v1_ordinal1(sK0)
    | ~ spl4_11 ),
    inference(resolution,[],[f104,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v2_ordinal1(X0)
      | v3_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
    <=> ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_ordinal1)).

fof(f104,plain,
    ( v2_ordinal1(sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f128,plain,
    ( spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f123,f106,f103])).

fof(f106,plain,
    ( spl4_12
  <=> sK3(sK0) = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f123,plain,
    ( v2_ordinal1(sK0)
    | ~ spl4_12 ),
    inference(trivial_inequality_removal,[],[f121])).

fof(f121,plain,
    ( sK2(sK0) != sK2(sK0)
    | v2_ordinal1(sK0)
    | ~ spl4_12 ),
    inference(superposition,[],[f35,f107])).

fof(f107,plain,
    ( sK3(sK0) = sK2(sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f35,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ( ~ r2_hidden(sK3(X0),sK2(X0))
          & sK2(X0) != sK3(X0)
          & ~ r2_hidden(sK2(X0),sK3(X0))
          & r2_hidden(sK3(X0),X0)
          & r2_hidden(sK2(X0),X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(sK3(X0),sK2(X0))
        & sK2(X0) != sK3(X0)
        & ~ r2_hidden(sK2(X0),sK3(X0))
        & r2_hidden(sK3(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1,X2] :
            ( r2_hidden(X2,X1)
            | X1 = X2
            | r2_hidden(X1,X2)
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).

fof(f114,plain,
    ( spl4_11
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f113,f110,f103])).

fof(f110,plain,
    ( spl4_13
  <=> r2_hidden(sK3(sK0),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f113,plain,
    ( v2_ordinal1(sK0)
    | ~ spl4_13 ),
    inference(resolution,[],[f111,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),sK2(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f111,plain,
    ( r2_hidden(sK3(sK0),sK2(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,
    ( spl4_11
    | spl4_12
    | ~ spl4_8
    | spl4_13
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f100,f49,f110,f84,f106,f103])).

fof(f84,plain,
    ( spl4_8
  <=> v3_ordinal1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f49,plain,
    ( spl4_2
  <=> v3_ordinal1(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f100,plain,
    ( r2_hidden(sK3(sK0),sK2(sK0))
    | ~ v3_ordinal1(sK2(sK0))
    | sK3(sK0) = sK2(sK0)
    | v2_ordinal1(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f97,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0),sK3(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f97,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK3(sK0))
        | r2_hidden(sK3(sK0),X0)
        | ~ v3_ordinal1(X0)
        | sK3(sK0) = X0 )
    | ~ spl4_2 ),
    inference(resolution,[],[f27,f50])).

fof(f50,plain,
    ( v3_ordinal1(sK3(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f86,plain,
    ( spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f82,f52,f84])).

fof(f82,plain,
    ( ~ v1_ordinal1(sK0)
    | v3_ordinal1(sK2(sK0)) ),
    inference(global_subsumption,[],[f26,f81])).

fof(f81,plain,
    ( ~ v1_ordinal1(sK0)
    | v3_ordinal1(sK0)
    | v3_ordinal1(sK2(sK0)) ),
    inference(resolution,[],[f45,f24])).

fof(f24,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ v3_ordinal1(sK0)
    & ! [X1] :
        ( ( r1_tarski(X1,sK0)
          & v3_ordinal1(X1) )
        | ~ r2_hidden(X1,sK0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ~ v3_ordinal1(X0)
        & ! [X1] :
            ( ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) )
            | ~ r2_hidden(X1,X0) ) )
   => ( ~ v3_ordinal1(sK0)
      & ! [X1] :
          ( ( r1_tarski(X1,sK0)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(X0)
      & ! [X1] :
          ( ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( r2_hidden(X1,X0)
           => ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) ) )
       => v3_ordinal1(X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) ) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_ordinal1)).

fof(f45,plain,(
    ! [X1] :
      ( r2_hidden(sK2(X1),X1)
      | ~ v1_ordinal1(X1)
      | v3_ordinal1(X1) ) ),
    inference(resolution,[],[f39,f32])).

fof(f32,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f26,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f68,plain,
    ( ~ spl4_5
    | spl4_4 ),
    inference(avatar_split_clause,[],[f65,f58,f62])).

fof(f62,plain,
    ( spl4_5
  <=> r2_hidden(sK1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f58,plain,
    ( spl4_4
  <=> r1_tarski(sK1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f65,plain,
    ( ~ r2_hidden(sK1(sK0),sK0)
    | spl4_4 ),
    inference(resolution,[],[f59,f25])).

fof(f25,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,
    ( ~ r1_tarski(sK1(sK0),sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f64,plain,
    ( spl4_5
    | spl4_3 ),
    inference(avatar_split_clause,[],[f56,f52,f62])).

fof(f56,plain,
    ( r2_hidden(sK1(sK0),sK0)
    | spl4_3 ),
    inference(resolution,[],[f53,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK1(X0),X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK1(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f53,plain,
    ( ~ v1_ordinal1(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f60,plain,
    ( ~ spl4_4
    | spl4_3 ),
    inference(avatar_split_clause,[],[f55,f52,f58])).

fof(f55,plain,
    ( ~ r1_tarski(sK1(sK0),sK0)
    | spl4_3 ),
    inference(resolution,[],[f53,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ r1_tarski(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,
    ( spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f47,f52,f49])).

fof(f47,plain,
    ( ~ v1_ordinal1(sK0)
    | v3_ordinal1(sK3(sK0)) ),
    inference(global_subsumption,[],[f26,f46])).

fof(f46,plain,
    ( ~ v1_ordinal1(sK0)
    | v3_ordinal1(sK0)
    | v3_ordinal1(sK3(sK0)) ),
    inference(resolution,[],[f44,f24])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | ~ v1_ordinal1(X0)
      | v3_ordinal1(X0) ) ),
    inference(resolution,[],[f39,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f26,f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (31251)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (31251)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (31262)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.47  % (31259)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f43,f54,f60,f64,f68,f86,f112,f114,f128,f132])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    ~spl4_3 | spl4_1 | ~spl4_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f130,f103,f41,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl4_3 <=> v1_ordinal1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    spl4_1 <=> v3_ordinal1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    spl4_11 <=> v2_ordinal1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    v3_ordinal1(sK0) | ~v1_ordinal1(sK0) | ~spl4_11),
% 0.21/0.47    inference(resolution,[],[f104,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_ordinal1(X0) | v3_ordinal1(X0) | ~v1_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : ((v3_ordinal1(X0) | ~v2_ordinal1(X0) | ~v1_ordinal1(X0)) & ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0)))),
% 0.21/0.47    inference(flattening,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : ((v3_ordinal1(X0) | (~v2_ordinal1(X0) | ~v1_ordinal1(X0))) & ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (v3_ordinal1(X0) <=> (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_ordinal1)).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    v2_ordinal1(sK0) | ~spl4_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f103])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    spl4_11 | ~spl4_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f123,f106,f103])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    spl4_12 <=> sK3(sK0) = sK2(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    v2_ordinal1(sK0) | ~spl4_12),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f121])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    sK2(sK0) != sK2(sK0) | v2_ordinal1(sK0) | ~spl4_12),
% 0.21/0.47    inference(superposition,[],[f35,f107])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    sK3(sK0) = sK2(sK0) | ~spl4_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f106])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0] : (sK2(X0) != sK3(X0) | v2_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : ((v2_ordinal1(X0) | (~r2_hidden(sK3(X0),sK2(X0)) & sK2(X0) != sK3(X0) & ~r2_hidden(sK2(X0),sK3(X0)) & r2_hidden(sK3(X0),X0) & r2_hidden(sK2(X0),X0))) & (! [X3,X4] : (r2_hidden(X4,X3) | X3 = X4 | r2_hidden(X3,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | ~v2_ordinal1(X0)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)) => (~r2_hidden(sK3(X0),sK2(X0)) & sK2(X0) != sK3(X0) & ~r2_hidden(sK2(X0),sK3(X0)) & r2_hidden(sK3(X0),X0) & r2_hidden(sK2(X0),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : ((v2_ordinal1(X0) | ? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0))) & (! [X3,X4] : (r2_hidden(X4,X3) | X3 = X4 | r2_hidden(X3,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | ~v2_ordinal1(X0)))),
% 0.21/0.47    inference(rectify,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : ((v2_ordinal1(X0) | ? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0))) & (! [X1,X2] : (r2_hidden(X2,X1) | X1 = X2 | r2_hidden(X1,X2) | ~r2_hidden(X2,X0) | ~r2_hidden(X1,X0)) | ~v2_ordinal1(X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (v2_ordinal1(X0) <=> ! [X1,X2] : (r2_hidden(X2,X1) | X1 = X2 | r2_hidden(X1,X2) | ~r2_hidden(X2,X0) | ~r2_hidden(X1,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (v2_ordinal1(X0) <=> ! [X1,X2] : ~(~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl4_11 | ~spl4_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f113,f110,f103])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    spl4_13 <=> r2_hidden(sK3(sK0),sK2(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    v2_ordinal1(sK0) | ~spl4_13),
% 0.21/0.47    inference(resolution,[],[f111,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK3(X0),sK2(X0)) | v2_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    r2_hidden(sK3(sK0),sK2(sK0)) | ~spl4_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f110])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    spl4_11 | spl4_12 | ~spl4_8 | spl4_13 | ~spl4_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f100,f49,f110,f84,f106,f103])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    spl4_8 <=> v3_ordinal1(sK2(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl4_2 <=> v3_ordinal1(sK3(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    r2_hidden(sK3(sK0),sK2(sK0)) | ~v3_ordinal1(sK2(sK0)) | sK3(sK0) = sK2(sK0) | v2_ordinal1(sK0) | ~spl4_2),
% 0.21/0.47    inference(resolution,[],[f97,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK2(X0),sK3(X0)) | v2_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(X0,sK3(sK0)) | r2_hidden(sK3(sK0),X0) | ~v3_ordinal1(X0) | sK3(sK0) = X0) ) | ~spl4_2),
% 0.21/0.47    inference(resolution,[],[f27,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    v3_ordinal1(sK3(sK0)) | ~spl4_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f49])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v3_ordinal1(X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | r2_hidden(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl4_8 | ~spl4_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f82,f52,f84])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ~v1_ordinal1(sK0) | v3_ordinal1(sK2(sK0))),
% 0.21/0.47    inference(global_subsumption,[],[f26,f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ~v1_ordinal1(sK0) | v3_ordinal1(sK0) | v3_ordinal1(sK2(sK0))),
% 0.21/0.47    inference(resolution,[],[f45,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_hidden(X1,sK0) | v3_ordinal1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ~v3_ordinal1(sK0) & ! [X1] : ((r1_tarski(X1,sK0) & v3_ordinal1(X1)) | ~r2_hidden(X1,sK0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0] : (~v3_ordinal1(X0) & ! [X1] : ((r1_tarski(X1,X0) & v3_ordinal1(X1)) | ~r2_hidden(X1,X0))) => (~v3_ordinal1(sK0) & ! [X1] : ((r1_tarski(X1,sK0) & v3_ordinal1(X1)) | ~r2_hidden(X1,sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : (~v3_ordinal1(X0) & ! [X1] : ((r1_tarski(X1,X0) & v3_ordinal1(X1)) | ~r2_hidden(X1,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (! [X1] : (r2_hidden(X1,X0) => (r1_tarski(X1,X0) & v3_ordinal1(X1))) => v3_ordinal1(X0))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => (r1_tarski(X1,X0) & v3_ordinal1(X1))) => v3_ordinal1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_ordinal1)).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X1] : (r2_hidden(sK2(X1),X1) | ~v1_ordinal1(X1) | v3_ordinal1(X1)) )),
% 0.21/0.47    inference(resolution,[],[f39,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0] : (v2_ordinal1(X0) | r2_hidden(sK2(X0),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ~v3_ordinal1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ~spl4_5 | spl4_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f65,f58,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    spl4_5 <=> r2_hidden(sK1(sK0),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl4_4 <=> r1_tarski(sK1(sK0),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ~r2_hidden(sK1(sK0),sK0) | spl4_4),
% 0.21/0.47    inference(resolution,[],[f59,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X1] : (r1_tarski(X1,sK0) | ~r2_hidden(X1,sK0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ~r1_tarski(sK1(sK0),sK0) | spl4_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl4_5 | spl4_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f56,f52,f62])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    r2_hidden(sK1(sK0),sK0) | spl4_3),
% 0.21/0.47    inference(resolution,[],[f53,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0] : (v1_ordinal1(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK1(X0),X0) & r2_hidden(sK1(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK1(X0),X0) & r2_hidden(sK1(X0),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.21/0.47    inference(rectify,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ~v1_ordinal1(sK0) | spl4_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f52])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ~spl4_4 | spl4_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f55,f52,f58])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ~r1_tarski(sK1(sK0),sK0) | spl4_3),
% 0.21/0.47    inference(resolution,[],[f53,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0] : (v1_ordinal1(X0) | ~r1_tarski(sK1(X0),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl4_2 | ~spl4_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f47,f52,f49])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ~v1_ordinal1(sK0) | v3_ordinal1(sK3(sK0))),
% 0.21/0.47    inference(global_subsumption,[],[f26,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ~v1_ordinal1(sK0) | v3_ordinal1(sK0) | v3_ordinal1(sK3(sK0))),
% 0.21/0.47    inference(resolution,[],[f44,f24])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK3(X0),X0) | ~v1_ordinal1(X0) | v3_ordinal1(X0)) )),
% 0.21/0.47    inference(resolution,[],[f39,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0] : (v2_ordinal1(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ~spl4_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f41])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (31251)------------------------------
% 0.21/0.47  % (31251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (31251)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (31251)Memory used [KB]: 10618
% 0.21/0.47  % (31251)Time elapsed: 0.067 s
% 0.21/0.47  % (31251)------------------------------
% 0.21/0.47  % (31251)------------------------------
% 0.21/0.48  % (31244)Success in time 0.118 s
%------------------------------------------------------------------------------
