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
% DateTime   : Thu Dec  3 12:58:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 105 expanded)
%              Number of leaves         :   16 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  243 ( 459 expanded)
%              Number of equality atoms :   25 (  50 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f283,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f94,f101,f182,f282])).

fof(f282,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | ~ spl6_4 ),
    inference(resolution,[],[f250,f226])).

fof(f226,plain,
    ( r2_hidden(sK1(sK3(sK0),sK0),sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f93,f47])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).

fof(f27,plain,(
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

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f93,plain,
    ( r2_hidden(sK1(sK3(sK0),sK0),k3_xboole_0(sK3(sK0),sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl6_4
  <=> r2_hidden(sK1(sK3(sK0),sK0),k3_xboole_0(sK3(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f250,plain,
    ( ~ r2_hidden(sK1(sK3(sK0),sK0),sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f225,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,sK3(X1)) ) ),
    inference(condensation,[],[f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK3(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK3(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f22])).

fof(f22,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK3(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f225,plain,
    ( r2_hidden(sK1(sK3(sK0),sK0),sK3(sK0))
    | ~ spl6_4 ),
    inference(resolution,[],[f93,f48])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f182,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl6_1 ),
    inference(resolution,[],[f174,f31])).

fof(f31,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f174,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl6_1 ),
    inference(resolution,[],[f143,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f143,plain,
    ( r2_hidden(sK2(k1_xboole_0,sK0),k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl6_1 ),
    inference(resolution,[],[f103,f65])).

fof(f65,plain,
    ( r2_hidden(sK2(k1_xboole_0,sK0),k1_xboole_0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_1
  <=> r2_hidden(sK2(k1_xboole_0,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k1_xboole_0,sK0),X0)
        | r2_hidden(sK2(k1_xboole_0,sK0),k3_xboole_0(k1_xboole_0,X0)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f65,f46])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f101,plain,
    ( ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f89,f69])).

fof(f69,plain,
    ( r2_hidden(sK2(k1_xboole_0,sK0),sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_2
  <=> r2_hidden(sK2(k1_xboole_0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f89,plain,
    ( ! [X6] : ~ r2_hidden(X6,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_3
  <=> ! [X6] : ~ r2_hidden(X6,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f94,plain,
    ( spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f86,f91,f88])).

fof(f86,plain,(
    ! [X6] :
      ( r2_hidden(sK1(sK3(sK0),sK0),k3_xboole_0(sK3(sK0),sK0))
      | ~ r2_hidden(X6,sK0) ) ),
    inference(resolution,[],[f75,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK1(X0,sK0),k3_xboole_0(X0,sK0)) ) ),
    inference(resolution,[],[f30,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK0)
          | ~ r2_hidden(X1,sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f70,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f60,f67,f63])).

fof(f60,plain,
    ( r2_hidden(sK2(k1_xboole_0,sK0),sK0)
    | r2_hidden(sK2(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(resolution,[],[f50,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sQ5_eqProxy(X0,X1)
      | r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f36,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f50,plain,(
    ~ sQ5_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f29,f49])).

fof(f29,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:31:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (2789)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (2788)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (2796)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (2804)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (2797)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (2804)Refutation not found, incomplete strategy% (2804)------------------------------
% 0.22/0.56  % (2804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (2805)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (2804)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (2804)Memory used [KB]: 10618
% 0.22/0.56  % (2804)Time elapsed: 0.132 s
% 0.22/0.56  % (2804)------------------------------
% 0.22/0.56  % (2804)------------------------------
% 0.22/0.56  % (2797)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f283,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f70,f94,f101,f182,f282])).
% 0.22/0.57  fof(f282,plain,(
% 0.22/0.57    ~spl6_4),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f279])).
% 0.22/0.57  fof(f279,plain,(
% 0.22/0.57    $false | ~spl6_4),
% 0.22/0.57    inference(resolution,[],[f250,f226])).
% 0.22/0.57  fof(f226,plain,(
% 0.22/0.57    r2_hidden(sK1(sK3(sK0),sK0),sK0) | ~spl6_4),
% 0.22/0.57    inference(resolution,[],[f93,f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(equality_resolution,[],[f41])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(rectify,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(flattening,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(nnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.57  fof(f93,plain,(
% 0.22/0.57    r2_hidden(sK1(sK3(sK0),sK0),k3_xboole_0(sK3(sK0),sK0)) | ~spl6_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f91])).
% 0.22/0.57  fof(f91,plain,(
% 0.22/0.57    spl6_4 <=> r2_hidden(sK1(sK3(sK0),sK0),k3_xboole_0(sK3(sK0),sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.57  fof(f250,plain,(
% 0.22/0.57    ~r2_hidden(sK1(sK3(sK0),sK0),sK0) | ~spl6_4),
% 0.22/0.57    inference(resolution,[],[f225,f59])).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,sK3(X1))) )),
% 0.22/0.57    inference(condensation,[],[f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK3(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK3(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK3(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X1),X1)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.22/0.57  fof(f225,plain,(
% 0.22/0.57    r2_hidden(sK1(sK3(sK0),sK0),sK3(sK0)) | ~spl6_4),
% 0.22/0.57    inference(resolution,[],[f93,f48])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(equality_resolution,[],[f40])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f28])).
% 0.22/0.57  fof(f182,plain,(
% 0.22/0.57    ~spl6_1),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f180])).
% 0.22/0.57  fof(f180,plain,(
% 0.22/0.57    $false | ~spl6_1),
% 0.22/0.57    inference(resolution,[],[f174,f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.57  fof(f174,plain,(
% 0.22/0.57    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl6_1),
% 0.22/0.57    inference(resolution,[],[f143,f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f12,plain,(
% 0.22/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,plain,(
% 0.22/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(rectify,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.57  fof(f143,plain,(
% 0.22/0.57    r2_hidden(sK2(k1_xboole_0,sK0),k3_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl6_1),
% 0.22/0.57    inference(resolution,[],[f103,f65])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    r2_hidden(sK2(k1_xboole_0,sK0),k1_xboole_0) | ~spl6_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f63])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    spl6_1 <=> r2_hidden(sK2(k1_xboole_0,sK0),k1_xboole_0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.57  fof(f103,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(sK2(k1_xboole_0,sK0),X0) | r2_hidden(sK2(k1_xboole_0,sK0),k3_xboole_0(k1_xboole_0,X0))) ) | ~spl6_1),
% 0.22/0.57    inference(resolution,[],[f65,f46])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.22/0.57    inference(equality_resolution,[],[f42])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f28])).
% 0.22/0.57  fof(f101,plain,(
% 0.22/0.57    ~spl6_2 | ~spl6_3),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f99])).
% 0.22/0.57  fof(f99,plain,(
% 0.22/0.57    $false | (~spl6_2 | ~spl6_3)),
% 0.22/0.57    inference(resolution,[],[f89,f69])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    r2_hidden(sK2(k1_xboole_0,sK0),sK0) | ~spl6_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f67])).
% 0.22/0.57  fof(f67,plain,(
% 0.22/0.57    spl6_2 <=> r2_hidden(sK2(k1_xboole_0,sK0),sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.57  fof(f89,plain,(
% 0.22/0.57    ( ! [X6] : (~r2_hidden(X6,sK0)) ) | ~spl6_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f88])).
% 0.22/0.57  fof(f88,plain,(
% 0.22/0.57    spl6_3 <=> ! [X6] : ~r2_hidden(X6,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.57  fof(f94,plain,(
% 0.22/0.57    spl6_3 | spl6_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f86,f91,f88])).
% 0.22/0.57  fof(f86,plain,(
% 0.22/0.57    ( ! [X6] : (r2_hidden(sK1(sK3(sK0),sK0),k3_xboole_0(sK3(sK0),sK0)) | ~r2_hidden(X6,sK0)) )),
% 0.22/0.57    inference(resolution,[],[f75,f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r2_hidden(sK3(X1),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f75,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(sK1(X0,sK0),k3_xboole_0(X0,sK0))) )),
% 0.22/0.57    inference(resolution,[],[f30,f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f18])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ( ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f11,plain,(
% 0.22/0.57    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,negated_conjecture,(
% 0.22/0.57    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.57    inference(negated_conjecture,[],[f8])).
% 0.22/0.57  fof(f8,conjecture,(
% 0.22/0.57    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.22/0.57  fof(f70,plain,(
% 0.22/0.57    spl6_1 | spl6_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f60,f67,f63])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    r2_hidden(sK2(k1_xboole_0,sK0),sK0) | r2_hidden(sK2(k1_xboole_0,sK0),k1_xboole_0)),
% 0.22/0.57    inference(resolution,[],[f50,f54])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    ( ! [X0,X1] : (sQ5_eqProxy(X0,X1) | r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.22/0.57    inference(equality_proxy_replacement,[],[f36,f49])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.57    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.22/0.57    inference(nnf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    ~sQ5_eqProxy(k1_xboole_0,sK0)),
% 0.22/0.57    inference(equality_proxy_replacement,[],[f29,f49])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    k1_xboole_0 != sK0),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (2797)------------------------------
% 0.22/0.57  % (2797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (2797)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (2797)Memory used [KB]: 6268
% 0.22/0.57  % (2797)Time elapsed: 0.138 s
% 0.22/0.57  % (2797)------------------------------
% 0.22/0.57  % (2797)------------------------------
% 0.22/0.57  % (2781)Success in time 0.202 s
%------------------------------------------------------------------------------
