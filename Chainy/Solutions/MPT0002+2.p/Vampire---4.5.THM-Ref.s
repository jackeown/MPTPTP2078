%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0002+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 182 expanded)
%              Number of leaves         :   10 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  247 ( 849 expanded)
%              Number of equality atoms :   15 (  88 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f70,f71,f79,f109,f155,f176])).

fof(f176,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f174,f49])).

fof(f49,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl5_1
  <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f174,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f173,f40])).

fof(f40,plain,(
    ~ sQ4_eqProxy(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(equality_proxy_replacement,[],[f30,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f30,plain,(
    sK0 != k5_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK0 != k5_xboole_0(sK1,sK2)
    & ! [X3] :
        ( ( ~ r2_hidden(X3,sK0)
          | ( ( ~ r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) )
            & ( r2_hidden(X3,sK2)
              | r2_hidden(X3,sK1) ) ) )
        & ( ( ( r2_hidden(X3,sK1)
              | ~ r2_hidden(X3,sK2) )
            & ( r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) ) )
          | r2_hidden(X3,sK0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k5_xboole_0(X1,X2) != X0
        & ! [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) ) )
            & ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | r2_hidden(X3,X0) ) ) )
   => ( sK0 != k5_xboole_0(sK1,sK2)
      & ! [X3] :
          ( ( ~ r2_hidden(X3,sK0)
            | ( ( ~ r2_hidden(X3,sK2)
                | ~ r2_hidden(X3,sK1) )
              & ( r2_hidden(X3,sK2)
                | r2_hidden(X3,sK1) ) ) )
          & ( ( ( r2_hidden(X3,sK1)
                | ~ r2_hidden(X3,sK2) )
              & ( r2_hidden(X3,sK2)
                | ~ r2_hidden(X3,sK1) ) )
            | r2_hidden(X3,sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) ) ) )
          & ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) ) )
            | r2_hidden(X3,X0) ) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,X0)
          <=> ( r2_hidden(X3,X1)
            <=> r2_hidden(X3,X2) ) )
       => k5_xboole_0(X1,X2) = X0 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) )
     => k5_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_0)).

fof(f173,plain,
    ( sQ4_eqProxy(sK0,k5_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f163,f161])).

fof(f161,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f156,f49])).

fof(f156,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f64,f29])).

fof(f29,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_3
  <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f163,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)
    | sQ4_eqProxy(sK0,k5_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f158,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | sQ4_eqProxy(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f37,f39])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f158,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(X0,sK2))
        | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f64,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f155,plain,
    ( spl5_4
    | spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f110,f47,f63,f67])).

fof(f67,plain,
    ( spl5_4
  <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f110,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2)
    | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f49,f28])).

fof(f28,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f109,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f107,f84])).

fof(f84,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f80,f65])).

fof(f65,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f80,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2)
    | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f68,f26])).

fof(f26,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2)
      | r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f107,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f106,f40])).

fof(f106,plain,
    ( sQ4_eqProxy(sK0,k5_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f98,f65])).

fof(f98,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2)
    | sQ4_eqProxy(sK0,k5_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f82,f42])).

fof(f82,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,X1))
        | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f68,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f79,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f77,f61])).

fof(f61,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f55,f40])).

fof(f55,plain,
    ( sQ4_eqProxy(sK0,k5_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f53,f42])).

fof(f53,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl5_2
  <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f77,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f73,f69])).

fof(f69,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f73,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)
    | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f64,f27])).

fof(f27,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1)
      | r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,
    ( spl5_3
    | spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f57,f51,f67,f63])).

fof(f57,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)
    | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f53,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f56,f51,f67,f63])).

fof(f56,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f53,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f45,f51,f47])).

fof(f45,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK2))
    | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0) ),
    inference(resolution,[],[f43,f40])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X0,X1)
      | r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f36,f39])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
