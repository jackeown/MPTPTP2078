%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t60_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:09 EDT 2019

% Result     : Theorem 77.35s
% Output     : Refutation 77.35s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 248 expanded)
%              Number of leaves         :   20 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          :  422 (1170 expanded)
%              Number of equality atoms :  124 ( 387 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2390,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f226,f334,f429,f483,f2314,f2343,f2389])).

fof(f2389,plain,
    ( spl7_5
    | ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f2361])).

fof(f2361,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f71,f86,f87,f216,f482,f610])).

fof(f610,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ sQ6_eqProxy(k3_xboole_0(X8,k1_tarski(X5)),X9)
      | r2_hidden(X6,X7)
      | ~ r2_hidden(X5,X8)
      | ~ sQ6_eqProxy(X9,X7)
      | ~ sQ6_eqProxy(X5,X6) ) ),
    inference(resolution,[],[f296,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(X0,X2)
      | ~ sQ6_eqProxy(X1,X2)
      | ~ sQ6_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f81])).

fof(f81,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f296,plain,(
    ! [X28,X26,X27,X25] :
      ( ~ sQ6_eqProxy(k3_xboole_0(X25,k1_tarski(X26)),X27)
      | ~ sQ6_eqProxy(X26,X28)
      | r2_hidden(X28,X27)
      | ~ r2_hidden(X26,X25) ) ),
    inference(resolution,[],[f106,f150])).

fof(f150,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,k3_xboole_0(X2,k1_tarski(X1)))
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f73,f71])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
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

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t60_zfmisc_1.p',d4_xboole_0)).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ sQ6_eqProxy(X2,X3)
      | ~ sQ6_eqProxy(X0,X1)
      | r2_hidden(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f81])).

fof(f482,plain,
    ( sQ6_eqProxy(sK0,sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f481])).

fof(f481,plain,
    ( spl7_14
  <=> sQ6_eqProxy(sK0,sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f216,plain,
    ( ~ r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl7_5
  <=> ~ r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f87,plain,(
    ! [X0,X1] : sQ6_eqProxy(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
    inference(equality_proxy_replacement,[],[f49,f81])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t60_zfmisc_1.p',commutativity_k3_xboole_0)).

fof(f86,plain,(
    ! [X0] : sQ6_eqProxy(k3_xboole_0(X0,X0),X0) ),
    inference(equality_proxy_replacement,[],[f48,f81])).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t60_zfmisc_1.p',idempotence_k3_xboole_0)).

fof(f71,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t60_zfmisc_1.p',d1_tarski)).

fof(f2343,plain,
    ( ~ spl7_2
    | ~ spl7_12
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f2342])).

fof(f2342,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f2335,f476])).

fof(f476,plain,
    ( sQ6_eqProxy(sK2,sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f475])).

fof(f475,plain,
    ( spl7_12
  <=> sQ6_eqProxy(sK2,sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f2335,plain,
    ( ~ sQ6_eqProxy(sK2,sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)))
    | ~ spl7_2
    | ~ spl7_15 ),
    inference(resolution,[],[f122,f490])).

fof(f490,plain,
    ( ! [X0] :
        ( ~ sQ6_eqProxy(sK0,X0)
        | ~ sQ6_eqProxy(X0,sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0))) )
    | ~ spl7_15 ),
    inference(resolution,[],[f479,f110])).

fof(f479,plain,
    ( ~ sQ6_eqProxy(sK0,sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f478])).

fof(f478,plain,
    ( spl7_15
  <=> ~ sQ6_eqProxy(sK0,sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f122,plain,
    ( sQ6_eqProxy(sK0,sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl7_2
  <=> sQ6_eqProxy(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f2314,plain,
    ( spl7_1
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f2313])).

fof(f2313,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f2299,f116])).

fof(f116,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl7_1
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f2299,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(resolution,[],[f827,f476])).

fof(f827,plain,
    ( ! [X2] :
        ( ~ sQ6_eqProxy(X2,sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)))
        | r2_hidden(X2,sK1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f407,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( sQ6_eqProxy(X1,X0)
      | ~ sQ6_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f81])).

fof(f407,plain,
    ( ! [X0] :
        ( ~ sQ6_eqProxy(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),X0)
        | r2_hidden(X0,sK1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f338,f108])).

fof(f108,plain,(
    ! [X0] : sQ6_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f81])).

fof(f338,plain,
    ( ! [X0,X1] :
        ( ~ sQ6_eqProxy(sK1,X0)
        | ~ sQ6_eqProxy(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),X1)
        | r2_hidden(X1,X0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f225,f106])).

fof(f225,plain,
    ( r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl7_6
  <=> r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f483,plain,
    ( spl7_12
    | spl7_14
    | spl7_5 ),
    inference(avatar_split_clause,[],[f454,f215,f481,f475])).

fof(f454,plain,
    ( sQ6_eqProxy(sK0,sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)))
    | sQ6_eqProxy(sK2,sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)))
    | ~ spl7_5 ),
    inference(resolution,[],[f446,f99])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | sQ6_eqProxy(X0,X4)
      | sQ6_eqProxy(X1,X4) ) ),
    inference(equality_proxy_replacement,[],[f80,f81,f81])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK5(X0,X1,X2) != X1
              & sK5(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X1
            | sK5(X0,X1,X2) = X0
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X1
            & sK5(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X1
          | sK5(X0,X1,X2) = X0
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t60_zfmisc_1.p',d2_tarski)).

fof(f446,plain,
    ( r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k2_tarski(sK0,sK2))
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f185,f216])).

fof(f185,plain,
    ( r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k2_tarski(sK0,sK2))
    | r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(resolution,[],[f95,f82])).

fof(f82,plain,(
    ~ sQ6_eqProxy(k3_xboole_0(k2_tarski(sK0,sK2),sK1),k1_tarski(sK0)) ),
    inference(equality_proxy_replacement,[],[f44,f81])).

fof(f44,plain,(
    k3_xboole_0(k2_tarski(sK0,sK2),sK1) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k3_xboole_0(k2_tarski(sK0,sK2),sK1) != k1_tarski(sK0)
    & ( sK0 = sK2
      | ~ r2_hidden(sK2,sK1) )
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
        & ( X0 = X2
          | ~ r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) )
   => ( k3_xboole_0(k2_tarski(sK0,sK2),sK1) != k1_tarski(sK0)
      & ( sK0 = sK2
        | ~ r2_hidden(sK2,sK1) )
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
          | ( X0 != X2
            & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t60_zfmisc_1.p',t60_zfmisc_1)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f61,f81])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f429,plain,
    ( ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f79,f108,f228,f420,f106])).

fof(f420,plain,
    ( ~ r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k2_tarski(sK0,sK2))
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f335,f225])).

fof(f335,plain,
    ( ~ r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),sK1)
    | ~ r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k2_tarski(sK0,sK2))
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f227,f82])).

fof(f227,plain,
    ( ~ r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),sK1)
    | ~ r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k2_tarski(sK0,sK2))
    | sQ6_eqProxy(k3_xboole_0(k2_tarski(sK0,sK2),sK1),k1_tarski(sK0))
    | ~ spl7_4 ),
    inference(resolution,[],[f219,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | sQ6_eqProxy(k3_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f63,f81])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f219,plain,
    ( r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl7_4
  <=> r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f228,plain,
    ( sQ6_eqProxy(sK0,sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)))
    | ~ spl7_4 ),
    inference(resolution,[],[f219,f91])).

fof(f91,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | sQ6_eqProxy(X0,X3) ) ),
    inference(equality_proxy_replacement,[],[f72,f81])).

fof(f72,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f334,plain,
    ( ~ spl7_4
    | spl7_7 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f86,f154,f222,f228,f106])).

fof(f222,plain,
    ( ~ r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl7_7
  <=> ~ r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f154,plain,(
    r2_hidden(sK0,k3_xboole_0(sK1,sK1)) ),
    inference(resolution,[],[f149,f42])).

fof(f42,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f149,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | r2_hidden(sK0,k3_xboole_0(X0,sK1)) ) ),
    inference(resolution,[],[f73,f42])).

fof(f226,plain,
    ( spl7_4
    | spl7_6 ),
    inference(avatar_split_clause,[],[f178,f224,f218])).

fof(f178,plain,
    ( r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),sK1)
    | r2_hidden(sK4(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(resolution,[],[f94,f82])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f62,f81])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f123,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f83,f121,f115])).

fof(f83,plain,
    ( sQ6_eqProxy(sK0,sK2)
    | ~ r2_hidden(sK2,sK1) ),
    inference(equality_proxy_replacement,[],[f43,f81])).

fof(f43,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
