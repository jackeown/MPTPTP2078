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
% DateTime   : Thu Dec  3 12:29:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 118 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  217 ( 656 expanded)
%              Number of equality atoms :   13 (  53 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f302,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f285,f301])).

fof(f301,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f44,f49,f44,f287,f288,f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X5,X3] :
      ( ~ r2_hidden(X6,X5)
      | ~ r1_xboole_0(X4,X2)
      | ~ sQ5_eqProxy(X4,X5)
      | ~ r2_hidden(X6,X3)
      | ~ sQ5_eqProxy(X2,X3) ) ),
    inference(resolution,[],[f43,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
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

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X1,X3)
      | ~ sQ5_eqProxy(X2,X3)
      | ~ r1_xboole_0(X0,X2)
      | ~ sQ5_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f288,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f54,f33])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f54,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl6_2
  <=> r2_hidden(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f287,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f54,f34])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl6_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f44,plain,(
    ! [X0] : sQ5_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f35])).

fof(f285,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f283,f50])).

fof(f50,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f283,plain,
    ( r1_xboole_0(sK0,sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f279,f56])).

fof(f56,plain,
    ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK0,sK1))
    | spl6_1 ),
    inference(subsumption_resolution,[],[f22,f50])).

fof(f22,plain,(
    ! [X3] :
      ( r1_xboole_0(sK0,sK1)
      | ~ r2_hidden(X3,k3_xboole_0(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( r1_xboole_0(sK0,sK1)
      & r2_hidden(sK2,k3_xboole_0(sK0,sK1)) )
    | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK0,sK1))
      & ~ r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) )
   => ( ( r1_xboole_0(sK0,sK1)
        & ? [X2] : r2_hidden(X2,k3_xboole_0(sK0,sK1)) )
      | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK0,sK1))
        & ~ r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ? [X2] : r2_hidden(X2,k3_xboole_0(sK0,sK1))
   => r2_hidden(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f279,plain,
    ( r2_hidden(sK3(sK0,sK1),k3_xboole_0(sK0,sK1))
    | r1_xboole_0(sK0,sK1)
    | spl6_1 ),
    inference(resolution,[],[f252,f68])).

fof(f68,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK3(X3,X4),X5)
      | r2_hidden(sK3(X3,X4),k3_xboole_0(X5,X4))
      | r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f252,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | spl6_1 ),
    inference(resolution,[],[f247,f33])).

fof(f247,plain,
    ( r2_hidden(sK3(sK0,sK1),k3_xboole_0(sK1,sK0))
    | spl6_1 ),
    inference(resolution,[],[f203,f50])).

fof(f203,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X2,X3)
      | r2_hidden(sK3(X2,X3),k3_xboole_0(X3,X2)) ) ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X3),k3_xboole_0(X3,X2))
      | r1_xboole_0(X2,X3)
      | r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f67,f24])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X2)
      | r2_hidden(sK3(X0,X1),k3_xboole_0(X2,X0))
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f32,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f19,f52,f48])).

fof(f19,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK0,sK1))
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:47:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (6758)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (6753)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (6758)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (6766)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f302,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f55,f285,f301])).
% 0.20/0.48  fof(f301,plain,(
% 0.20/0.48    ~spl6_1 | ~spl6_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f296])).
% 0.20/0.48  fof(f296,plain,(
% 0.20/0.48    $false | (~spl6_1 | ~spl6_2)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f44,f49,f44,f287,f288,f72])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X5,X3] : (~r2_hidden(X6,X5) | ~r1_xboole_0(X4,X2) | ~sQ5_eqProxy(X4,X5) | ~r2_hidden(X6,X3) | ~sQ5_eqProxy(X2,X3)) )),
% 0.20/0.48    inference(resolution,[],[f43,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X1,X3) | ~sQ5_eqProxy(X2,X3) | ~r1_xboole_0(X0,X2) | ~sQ5_eqProxy(X0,X1)) )),
% 0.20/0.48    inference(equality_proxy_axiom,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.20/0.48  fof(f288,plain,(
% 0.20/0.48    r2_hidden(sK2,sK1) | ~spl6_2),
% 0.20/0.48    inference(resolution,[],[f54,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 0.20/0.48    inference(equality_resolution,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.20/0.48    inference(rectify,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    r2_hidden(sK2,k3_xboole_0(sK0,sK1)) | ~spl6_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    spl6_2 <=> r2_hidden(sK2,k3_xboole_0(sK0,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.48  fof(f287,plain,(
% 0.20/0.48    r2_hidden(sK2,sK0) | ~spl6_2),
% 0.20/0.48    inference(resolution,[],[f54,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    r1_xboole_0(sK0,sK1) | ~spl6_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    spl6_1 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0] : (sQ5_eqProxy(X0,X0)) )),
% 0.20/0.48    inference(equality_proxy_axiom,[],[f35])).
% 0.20/0.48  fof(f285,plain,(
% 0.20/0.48    spl6_1),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f284])).
% 0.20/0.48  fof(f284,plain,(
% 0.20/0.48    $false | spl6_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f283,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ~r1_xboole_0(sK0,sK1) | spl6_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f48])).
% 0.20/0.48  fof(f283,plain,(
% 0.20/0.48    r1_xboole_0(sK0,sK1) | spl6_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f279,f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X3] : (~r2_hidden(X3,k3_xboole_0(sK0,sK1))) ) | spl6_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f22,f50])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X3] : (r1_xboole_0(sK0,sK1) | ~r2_hidden(X3,k3_xboole_0(sK0,sK1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    (r1_xboole_0(sK0,sK1) & r2_hidden(sK2,k3_xboole_0(sK0,sK1))) | (! [X3] : ~r2_hidden(X3,k3_xboole_0(sK0,sK1)) & ~r1_xboole_0(sK0,sK1))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10,f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0,X1] : ((r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) | (! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1))) => ((r1_xboole_0(sK0,sK1) & ? [X2] : r2_hidden(X2,k3_xboole_0(sK0,sK1))) | (! [X3] : ~r2_hidden(X3,k3_xboole_0(sK0,sK1)) & ~r1_xboole_0(sK0,sK1)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X2] : r2_hidden(X2,k3_xboole_0(sK0,sK1)) => r2_hidden(sK2,k3_xboole_0(sK0,sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0,X1] : ((r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) | (! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,plain,(
% 0.20/0.48    ~! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f4])).
% 0.20/0.48  fof(f4,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(negated_conjecture,[],[f3])).
% 0.20/0.48  fof(f3,conjecture,(
% 0.20/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.48  fof(f279,plain,(
% 0.20/0.48    r2_hidden(sK3(sK0,sK1),k3_xboole_0(sK0,sK1)) | r1_xboole_0(sK0,sK1) | spl6_1),
% 0.20/0.48    inference(resolution,[],[f252,f68])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ( ! [X4,X5,X3] : (~r2_hidden(sK3(X3,X4),X5) | r2_hidden(sK3(X3,X4),k3_xboole_0(X5,X4)) | r1_xboole_0(X3,X4)) )),
% 0.20/0.48    inference(resolution,[],[f32,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f252,plain,(
% 0.20/0.48    r2_hidden(sK3(sK0,sK1),sK0) | spl6_1),
% 0.20/0.48    inference(resolution,[],[f247,f33])).
% 0.20/0.48  fof(f247,plain,(
% 0.20/0.48    r2_hidden(sK3(sK0,sK1),k3_xboole_0(sK1,sK0)) | spl6_1),
% 0.20/0.48    inference(resolution,[],[f203,f50])).
% 0.20/0.48  fof(f203,plain,(
% 0.20/0.48    ( ! [X2,X3] : (r1_xboole_0(X2,X3) | r2_hidden(sK3(X2,X3),k3_xboole_0(X3,X2))) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f202])).
% 0.20/0.48  fof(f202,plain,(
% 0.20/0.48    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3),k3_xboole_0(X3,X2)) | r1_xboole_0(X2,X3) | r1_xboole_0(X2,X3)) )),
% 0.20/0.48    inference(resolution,[],[f67,f24])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1),X2) | r2_hidden(sK3(X0,X1),k3_xboole_0(X2,X0)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(resolution,[],[f32,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ~spl6_1 | spl6_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f19,f52,f48])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    r2_hidden(sK2,k3_xboole_0(sK0,sK1)) | ~r1_xboole_0(sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (6758)------------------------------
% 0.20/0.48  % (6758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (6758)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (6758)Memory used [KB]: 6268
% 0.20/0.48  % (6758)Time elapsed: 0.051 s
% 0.20/0.48  % (6758)------------------------------
% 0.20/0.48  % (6758)------------------------------
% 0.20/0.48  % (6752)Success in time 0.123 s
%------------------------------------------------------------------------------
