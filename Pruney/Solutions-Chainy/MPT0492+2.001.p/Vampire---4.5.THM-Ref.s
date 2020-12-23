%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 109 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  186 ( 464 expanded)
%              Number of equality atoms :   22 (  72 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f99,f101,f103,f164,f188])).

fof(f188,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f16,f79,f82,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f82,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f81])).

% (8370)Refutation not found, incomplete strategy% (8370)------------------------------
% (8370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f81,plain,
    ( spl3_2
  <=> r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f79,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_1
  <=> r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != k3_xboole_0(k1_relat_1(sK1),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) != k3_xboole_0(k1_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( k1_relat_1(k7_relat_1(sK1,sK0)) != k3_xboole_0(k1_relat_1(sK1),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != k3_xboole_0(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f164,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl3_1
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f16,f93,f79,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_3
  <=> r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f103,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f102,f81,f91,f77])).

fof(f102,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0)
    | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2] :
      ( k1_relat_1(k7_relat_1(sK1,sK0)) != X2
      | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,X2),sK0)
      | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,X2),k1_relat_1(sK1))
      | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,X2),X2) ) ),
    inference(superposition,[],[f17,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f12])).

fof(f12,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

% (8370)Termination reason: Refutation not found, incomplete strategy

% (8370)Memory used [KB]: 10618
% (8370)Time elapsed: 0.076 s
% (8370)------------------------------
% (8370)------------------------------
fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f17,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) != k3_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f101,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f100,f91,f77])).

fof(f100,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_relat_1(k7_relat_1(sK1,sK0)) != X0
      | r2_hidden(sK2(k1_relat_1(sK1),sK0,X0),k1_relat_1(sK1))
      | r2_hidden(sK2(k1_relat_1(sK1),sK0,X0),X0) ) ),
    inference(superposition,[],[f17,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f99,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f86,f81,f91,f77])).

fof(f86,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl3_2 ),
    inference(resolution,[],[f83,f32])).

fof(f32,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | ~ r2_hidden(X4,k1_relat_1(sK1))
      | r2_hidden(X4,k1_relat_1(k7_relat_1(sK1,X5))) ) ),
    inference(resolution,[],[f16,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f84,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f75,f81,f77])).

fof(f75,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0)
    | r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X1] :
      ( k1_relat_1(k7_relat_1(sK1,sK0)) != X1
      | r2_hidden(sK2(k1_relat_1(sK1),sK0,X1),sK0)
      | r2_hidden(sK2(k1_relat_1(sK1),sK0,X1),X1) ) ),
    inference(superposition,[],[f17,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:08:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (8385)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.48  % (8377)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (8372)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (8378)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (8373)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (8370)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (8371)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (8377)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f84,f99,f101,f103,f164,f188])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    ~spl3_1 | spl3_2),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f182])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    $false | (~spl3_1 | spl3_2)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f16,f79,f82,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ~r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0) | spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f81])).
% 0.22/0.50  % (8370)Refutation not found, incomplete strategy% (8370)------------------------------
% 0.22/0.50  % (8370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    spl3_2 <=> r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) | ~spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    spl3_1 <=> r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    v1_relat_1(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    k1_relat_1(k7_relat_1(sK1,sK0)) != k3_xboole_0(k1_relat_1(sK1),sK0) & v1_relat_1(sK1)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f7])).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != k3_xboole_0(k1_relat_1(X1),X0) & v1_relat_1(X1)) => (k1_relat_1(k7_relat_1(sK1,sK0)) != k3_xboole_0(k1_relat_1(sK1),sK0) & v1_relat_1(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f5,plain,(
% 0.22/0.50    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != k3_xboole_0(k1_relat_1(X1),X0) & v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.50    inference(negated_conjecture,[],[f3])).
% 0.22/0.50  fof(f3,conjecture,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    ~spl3_1 | spl3_3),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f152])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    $false | (~spl3_1 | spl3_3)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f16,f93,f79,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ~r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f91])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    spl3_3 <=> r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ~spl3_1 | ~spl3_3 | ~spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f102,f81,f91,f77])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ~r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0) | ~r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | ~r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.22/0.50    inference(equality_resolution,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X2] : (k1_relat_1(k7_relat_1(sK1,sK0)) != X2 | ~r2_hidden(sK2(k1_relat_1(sK1),sK0,X2),sK0) | ~r2_hidden(sK2(k1_relat_1(sK1),sK0,X2),k1_relat_1(sK1)) | ~r2_hidden(sK2(k1_relat_1(sK1),sK0,X2),X2)) )),
% 0.22/0.50    inference(superposition,[],[f17,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.50    inference(rectify,[],[f10])).
% 0.22/0.50  % (8370)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (8370)Memory used [KB]: 10618
% 0.22/0.50  % (8370)Time elapsed: 0.076 s
% 0.22/0.50  % (8370)------------------------------
% 0.22/0.50  % (8370)------------------------------
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.50    inference(flattening,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    k1_relat_1(k7_relat_1(sK1,sK0)) != k3_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl3_1 | spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f100,f91,f77])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.22/0.50    inference(equality_resolution,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,sK0)) != X0 | r2_hidden(sK2(k1_relat_1(sK1),sK0,X0),k1_relat_1(sK1)) | r2_hidden(sK2(k1_relat_1(sK1),sK0,X0),X0)) )),
% 0.22/0.50    inference(superposition,[],[f17,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl3_1 | ~spl3_3 | ~spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f86,f81,f91,f77])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ~r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) | ~spl3_2),
% 0.22/0.50    inference(resolution,[],[f83,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X4,X5] : (~r2_hidden(X4,X5) | ~r2_hidden(X4,k1_relat_1(sK1)) | r2_hidden(X4,k1_relat_1(k7_relat_1(sK1,X5)))) )),
% 0.22/0.50    inference(resolution,[],[f16,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0) | ~spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f81])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl3_1 | spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f75,f81,f77])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0) | r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.22/0.50    inference(equality_resolution,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,sK0)) != X1 | r2_hidden(sK2(k1_relat_1(sK1),sK0,X1),sK0) | r2_hidden(sK2(k1_relat_1(sK1),sK0,X1),X1)) )),
% 0.22/0.50    inference(superposition,[],[f17,f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (8377)------------------------------
% 0.22/0.50  % (8377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (8377)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (8377)Memory used [KB]: 6140
% 0.22/0.50  % (8377)Time elapsed: 0.084 s
% 0.22/0.50  % (8377)------------------------------
% 0.22/0.50  % (8377)------------------------------
% 0.22/0.50  % (8366)Success in time 0.135 s
%------------------------------------------------------------------------------
