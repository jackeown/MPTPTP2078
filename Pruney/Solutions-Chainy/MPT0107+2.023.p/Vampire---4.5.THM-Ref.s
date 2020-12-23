%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:12 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 196 expanded)
%              Number of leaves         :   13 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :  247 ( 899 expanded)
%              Number of equality atoms :   28 ( 128 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f316,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f92,f121,f150,f191,f208,f209,f233,f234,f315])).

fof(f315,plain,
    ( ~ spl4_2
    | spl4_3
    | spl4_6 ),
    inference(avatar_split_clause,[],[f306,f188,f88,f83])).

fof(f83,plain,
    ( spl4_2
  <=> r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f88,plain,
    ( spl4_3
  <=> r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f188,plain,
    ( spl4_6
  <=> r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f306,plain,
    ( r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK1)
    | ~ r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0)
    | spl4_6 ),
    inference(resolution,[],[f189,f58])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f20])).

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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f189,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f188])).

fof(f234,plain,
    ( ~ spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f226,f118,f188])).

fof(f118,plain,
    ( spl4_4
  <=> r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f226,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f120,f59])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f120,plain,
    ( r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f233,plain,
    ( spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl4_2
    | ~ spl4_4 ),
    inference(resolution,[],[f120,f132])).

fof(f132,plain,
    ( ! [X4] : ~ r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,X4))
    | spl4_2 ),
    inference(resolution,[],[f84,f60])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f84,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f209,plain,
    ( ~ spl4_2
    | ~ spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f143,f79,f118,f83])).

fof(f79,plain,
    ( spl4_1
  <=> r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f143,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f81,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f45,f33])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f81,plain,
    ( r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f208,plain,
    ( ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(resolution,[],[f190,f164])).

fof(f164,plain,
    ( ! [X4] : ~ r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(X4,sK1))
    | ~ spl4_3 ),
    inference(resolution,[],[f89,f59])).

fof(f89,plain,
    ( r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f190,plain,
    ( r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f188])).

fof(f191,plain,
    ( ~ spl4_2
    | spl4_6
    | spl4_4 ),
    inference(avatar_split_clause,[],[f180,f118,f188,f83])).

fof(f180,plain,
    ( r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0)
    | spl4_4 ),
    inference(resolution,[],[f119,f58])).

fof(f119,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f150,plain,
    ( spl4_2
    | spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f142,f79,f118,f83])).

fof(f142,plain,
    ( r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f81,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f44,f33])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f121,plain,
    ( ~ spl4_2
    | spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f109,f79,f118,f83])).

fof(f109,plain,
    ( r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0)
    | spl4_1 ),
    inference(resolution,[],[f80,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f33])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f80,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f92,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f77,f88,f83,f79])).

fof(f77,plain,
    ( r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK1)
    | ~ r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0)
    | ~ r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))) ),
    inference(resolution,[],[f63,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( sQ3_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f43,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ~ sQ3_eqProxy(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))) ),
    inference(equality_proxy_replacement,[],[f49,f61])).

fof(f49,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) ),
    inference(definition_unfolding,[],[f26,f33,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f91,plain,
    ( spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f76,f88,f79])).

fof(f76,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK1)
    | r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))) ),
    inference(resolution,[],[f63,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sQ3_eqProxy(k4_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f42,f61])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f75,f83,f79])).

fof(f75,plain,
    ( r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0)
    | r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))) ),
    inference(resolution,[],[f63,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sQ3_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f41,f61])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (2353)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (2353)Refutation not found, incomplete strategy% (2353)------------------------------
% 0.20/0.47  % (2353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (2377)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.47  % (2353)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (2353)Memory used [KB]: 6140
% 0.20/0.47  % (2353)Time elapsed: 0.058 s
% 0.20/0.47  % (2353)------------------------------
% 0.20/0.47  % (2353)------------------------------
% 0.20/0.54  % (2360)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (2352)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.55  % (2351)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.26/0.56  % (2355)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.26/0.56  % (2348)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.26/0.56  % (2369)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.26/0.56  % (2348)Refutation not found, incomplete strategy% (2348)------------------------------
% 1.26/0.56  % (2348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.56  % (2348)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.56  
% 1.26/0.56  % (2348)Memory used [KB]: 1663
% 1.26/0.56  % (2348)Time elapsed: 0.130 s
% 1.26/0.56  % (2348)------------------------------
% 1.26/0.56  % (2348)------------------------------
% 1.26/0.57  % (2375)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.26/0.57  % (2376)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.26/0.57  % (2376)Refutation not found, incomplete strategy% (2376)------------------------------
% 1.26/0.57  % (2376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.57  % (2376)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.57  
% 1.26/0.57  % (2376)Memory used [KB]: 6268
% 1.26/0.57  % (2376)Time elapsed: 0.168 s
% 1.26/0.57  % (2376)------------------------------
% 1.26/0.57  % (2376)------------------------------
% 1.26/0.57  % (2351)Refutation not found, incomplete strategy% (2351)------------------------------
% 1.26/0.57  % (2351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.57  % (2351)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.57  
% 1.26/0.57  % (2351)Memory used [KB]: 10618
% 1.26/0.57  % (2351)Time elapsed: 0.165 s
% 1.26/0.57  % (2351)------------------------------
% 1.26/0.57  % (2351)------------------------------
% 1.26/0.57  % (2362)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.26/0.57  % (2378)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.68/0.57  % (2373)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.68/0.57  % (2367)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.68/0.58  % (2367)Refutation not found, incomplete strategy% (2367)------------------------------
% 1.68/0.58  % (2367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (2367)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.58  
% 1.68/0.58  % (2367)Memory used [KB]: 10618
% 1.68/0.58  % (2367)Time elapsed: 0.178 s
% 1.68/0.58  % (2367)------------------------------
% 1.68/0.58  % (2367)------------------------------
% 1.68/0.58  % (2366)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.68/0.58  % (2373)Refutation not found, incomplete strategy% (2373)------------------------------
% 1.68/0.58  % (2373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (2373)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.58  
% 1.68/0.58  % (2373)Memory used [KB]: 10746
% 1.68/0.58  % (2373)Time elapsed: 0.176 s
% 1.68/0.58  % (2373)------------------------------
% 1.68/0.58  % (2373)------------------------------
% 1.68/0.58  % (2380)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.68/0.58  % (2358)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.68/0.58  % (2358)Refutation not found, incomplete strategy% (2358)------------------------------
% 1.68/0.58  % (2358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (2358)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.58  
% 1.68/0.58  % (2358)Memory used [KB]: 10618
% 1.68/0.58  % (2358)Time elapsed: 0.179 s
% 1.68/0.58  % (2358)------------------------------
% 1.68/0.58  % (2358)------------------------------
% 1.68/0.58  % (2363)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.68/0.58  % (2359)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.68/0.59  % (2359)Refutation not found, incomplete strategy% (2359)------------------------------
% 1.68/0.59  % (2359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.59  % (2359)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.59  
% 1.68/0.59  % (2359)Memory used [KB]: 10618
% 1.68/0.59  % (2359)Time elapsed: 0.189 s
% 1.68/0.59  % (2359)------------------------------
% 1.68/0.59  % (2359)------------------------------
% 1.68/0.59  % (2371)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.68/0.59  % (2371)Refutation not found, incomplete strategy% (2371)------------------------------
% 1.68/0.59  % (2371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.59  % (2371)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.59  
% 1.68/0.59  % (2371)Memory used [KB]: 10618
% 1.68/0.59  % (2371)Time elapsed: 0.188 s
% 1.68/0.59  % (2371)------------------------------
% 1.68/0.59  % (2371)------------------------------
% 1.68/0.59  % (2365)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.68/0.59  % (2356)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.68/0.60  % (2365)Refutation found. Thanks to Tanya!
% 1.68/0.60  % SZS status Theorem for theBenchmark
% 1.68/0.60  % SZS output start Proof for theBenchmark
% 1.68/0.60  fof(f316,plain,(
% 1.68/0.60    $false),
% 1.68/0.60    inference(avatar_sat_refutation,[],[f86,f91,f92,f121,f150,f191,f208,f209,f233,f234,f315])).
% 1.68/0.60  fof(f315,plain,(
% 1.68/0.60    ~spl4_2 | spl4_3 | spl4_6),
% 1.68/0.60    inference(avatar_split_clause,[],[f306,f188,f88,f83])).
% 1.68/0.60  fof(f83,plain,(
% 1.68/0.60    spl4_2 <=> r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0)),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.68/0.60  fof(f88,plain,(
% 1.68/0.60    spl4_3 <=> r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK1)),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.68/0.60  fof(f188,plain,(
% 1.68/0.60    spl4_6 <=> r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,sK1))),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.68/0.60  fof(f306,plain,(
% 1.68/0.60    r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK1) | ~r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0) | spl4_6),
% 1.68/0.60    inference(resolution,[],[f189,f58])).
% 1.68/0.60  fof(f58,plain,(
% 1.68/0.60    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.68/0.60    inference(equality_resolution,[],[f40])).
% 1.68/0.60  fof(f40,plain,(
% 1.68/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.68/0.60    inference(cnf_transformation,[],[f24])).
% 1.68/0.60  fof(f24,plain,(
% 1.68/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.68/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 1.68/0.60  fof(f23,plain,(
% 1.68/0.60    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.68/0.60    introduced(choice_axiom,[])).
% 1.68/0.60  fof(f22,plain,(
% 1.68/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.68/0.60    inference(rectify,[],[f21])).
% 1.68/0.60  fof(f21,plain,(
% 1.68/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.68/0.60    inference(flattening,[],[f20])).
% 1.68/0.60  fof(f20,plain,(
% 1.68/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.68/0.60    inference(nnf_transformation,[],[f2])).
% 1.68/0.60  fof(f2,axiom,(
% 1.68/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.68/0.60  fof(f189,plain,(
% 1.68/0.60    ~r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,sK1)) | spl4_6),
% 1.68/0.60    inference(avatar_component_clause,[],[f188])).
% 1.68/0.60  fof(f234,plain,(
% 1.68/0.60    ~spl4_6 | ~spl4_4),
% 1.68/0.60    inference(avatar_split_clause,[],[f226,f118,f188])).
% 1.68/0.60  fof(f118,plain,(
% 1.68/0.60    spl4_4 <=> r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.68/0.60  fof(f226,plain,(
% 1.68/0.60    ~r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,sK1)) | ~spl4_4),
% 1.68/0.60    inference(resolution,[],[f120,f59])).
% 1.68/0.60  fof(f59,plain,(
% 1.68/0.60    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.68/0.60    inference(equality_resolution,[],[f39])).
% 1.68/0.60  fof(f39,plain,(
% 1.68/0.60    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.68/0.60    inference(cnf_transformation,[],[f24])).
% 1.68/0.60  fof(f120,plain,(
% 1.68/0.60    r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl4_4),
% 1.68/0.60    inference(avatar_component_clause,[],[f118])).
% 1.68/0.60  fof(f233,plain,(
% 1.68/0.60    spl4_2 | ~spl4_4),
% 1.68/0.60    inference(avatar_contradiction_clause,[],[f224])).
% 1.68/0.60  fof(f224,plain,(
% 1.68/0.60    $false | (spl4_2 | ~spl4_4)),
% 1.68/0.60    inference(resolution,[],[f120,f132])).
% 1.68/0.60  fof(f132,plain,(
% 1.68/0.60    ( ! [X4] : (~r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,X4))) ) | spl4_2),
% 1.68/0.60    inference(resolution,[],[f84,f60])).
% 1.68/0.60  fof(f60,plain,(
% 1.68/0.60    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.68/0.60    inference(equality_resolution,[],[f38])).
% 1.68/0.60  fof(f38,plain,(
% 1.68/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.68/0.60    inference(cnf_transformation,[],[f24])).
% 1.68/0.60  fof(f84,plain,(
% 1.68/0.60    ~r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0) | spl4_2),
% 1.68/0.60    inference(avatar_component_clause,[],[f83])).
% 1.68/0.60  fof(f209,plain,(
% 1.68/0.60    ~spl4_2 | ~spl4_4 | ~spl4_1),
% 1.68/0.60    inference(avatar_split_clause,[],[f143,f79,f118,f83])).
% 1.68/0.60  fof(f79,plain,(
% 1.68/0.60    spl4_1 <=> r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)))),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.68/0.60  fof(f143,plain,(
% 1.68/0.60    ~r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0) | ~spl4_1),
% 1.68/0.60    inference(resolution,[],[f81,f56])).
% 1.68/0.60  fof(f56,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))) )),
% 1.68/0.60    inference(definition_unfolding,[],[f45,f33])).
% 1.68/0.60  fof(f33,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.68/0.60    inference(cnf_transformation,[],[f3])).
% 1.68/0.60  fof(f3,axiom,(
% 1.68/0.60    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.68/0.60  fof(f45,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.68/0.60    inference(cnf_transformation,[],[f25])).
% 1.68/0.60  fof(f25,plain,(
% 1.68/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.68/0.60    inference(nnf_transformation,[],[f16])).
% 1.68/0.60  fof(f16,plain,(
% 1.68/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.68/0.60    inference(ennf_transformation,[],[f4])).
% 1.68/0.60  fof(f4,axiom,(
% 1.68/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.68/0.60  fof(f81,plain,(
% 1.68/0.60    r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))) | ~spl4_1),
% 1.68/0.60    inference(avatar_component_clause,[],[f79])).
% 1.68/0.60  fof(f208,plain,(
% 1.68/0.60    ~spl4_3 | ~spl4_6),
% 1.68/0.60    inference(avatar_contradiction_clause,[],[f199])).
% 1.68/0.60  fof(f199,plain,(
% 1.68/0.60    $false | (~spl4_3 | ~spl4_6)),
% 1.68/0.60    inference(resolution,[],[f190,f164])).
% 1.68/0.60  fof(f164,plain,(
% 1.68/0.60    ( ! [X4] : (~r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(X4,sK1))) ) | ~spl4_3),
% 1.68/0.60    inference(resolution,[],[f89,f59])).
% 1.68/0.60  fof(f89,plain,(
% 1.68/0.60    r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK1) | ~spl4_3),
% 1.68/0.60    inference(avatar_component_clause,[],[f88])).
% 1.68/0.60  fof(f190,plain,(
% 1.68/0.60    r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,sK1)) | ~spl4_6),
% 1.68/0.60    inference(avatar_component_clause,[],[f188])).
% 1.68/0.60  fof(f191,plain,(
% 1.68/0.60    ~spl4_2 | spl4_6 | spl4_4),
% 1.68/0.60    inference(avatar_split_clause,[],[f180,f118,f188,f83])).
% 1.68/0.60  fof(f180,plain,(
% 1.68/0.60    r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0) | spl4_4),
% 1.68/0.60    inference(resolution,[],[f119,f58])).
% 1.68/0.60  fof(f119,plain,(
% 1.68/0.60    ~r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl4_4),
% 1.68/0.60    inference(avatar_component_clause,[],[f118])).
% 1.68/0.60  fof(f150,plain,(
% 1.68/0.60    spl4_2 | spl4_4 | ~spl4_1),
% 1.68/0.60    inference(avatar_split_clause,[],[f142,f79,f118,f83])).
% 1.68/0.60  fof(f142,plain,(
% 1.68/0.60    r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0) | ~spl4_1),
% 1.68/0.60    inference(resolution,[],[f81,f57])).
% 1.68/0.60  fof(f57,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))) )),
% 1.68/0.60    inference(definition_unfolding,[],[f44,f33])).
% 1.68/0.60  fof(f44,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.68/0.60    inference(cnf_transformation,[],[f25])).
% 1.68/0.60  fof(f121,plain,(
% 1.68/0.60    ~spl4_2 | spl4_4 | spl4_1),
% 1.68/0.60    inference(avatar_split_clause,[],[f109,f79,f118,f83])).
% 1.68/0.60  fof(f109,plain,(
% 1.68/0.60    r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0) | spl4_1),
% 1.68/0.60    inference(resolution,[],[f80,f55])).
% 1.68/0.60  fof(f55,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.68/0.60    inference(definition_unfolding,[],[f46,f33])).
% 1.68/0.60  fof(f46,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f25])).
% 1.68/0.60  fof(f80,plain,(
% 1.68/0.60    ~r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))) | spl4_1),
% 1.68/0.60    inference(avatar_component_clause,[],[f79])).
% 1.68/0.60  fof(f92,plain,(
% 1.68/0.60    ~spl4_1 | ~spl4_2 | spl4_3),
% 1.68/0.60    inference(avatar_split_clause,[],[f77,f88,f83,f79])).
% 1.68/0.60  fof(f77,plain,(
% 1.68/0.60    r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK1) | ~r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0) | ~r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)))),
% 1.68/0.60    inference(resolution,[],[f63,f71])).
% 1.68/0.60  fof(f71,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (sQ3_eqProxy(k4_xboole_0(X0,X1),X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.68/0.60    inference(equality_proxy_replacement,[],[f43,f61])).
% 1.68/0.60  fof(f61,plain,(
% 1.68/0.60    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 1.68/0.60    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 1.68/0.60  fof(f43,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f24])).
% 1.68/0.60  fof(f63,plain,(
% 1.68/0.60    ~sQ3_eqProxy(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)))),
% 1.68/0.60    inference(equality_proxy_replacement,[],[f49,f61])).
% 1.68/0.60  fof(f49,plain,(
% 1.68/0.60    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),
% 1.68/0.60    inference(definition_unfolding,[],[f26,f33,f31])).
% 1.68/0.60  fof(f31,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.68/0.60    inference(cnf_transformation,[],[f8])).
% 1.68/0.60  fof(f8,axiom,(
% 1.68/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.68/0.60  fof(f26,plain,(
% 1.68/0.60    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.68/0.60    inference(cnf_transformation,[],[f18])).
% 1.68/0.60  fof(f18,plain,(
% 1.68/0.60    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.68/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 1.68/0.60  fof(f17,plain,(
% 1.68/0.60    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.68/0.60    introduced(choice_axiom,[])).
% 1.68/0.60  fof(f15,plain,(
% 1.68/0.60    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.68/0.60    inference(ennf_transformation,[],[f14])).
% 1.68/0.60  fof(f14,negated_conjecture,(
% 1.68/0.60    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.68/0.60    inference(negated_conjecture,[],[f13])).
% 1.68/0.60  fof(f13,conjecture,(
% 1.68/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.68/0.60  fof(f91,plain,(
% 1.68/0.60    spl4_1 | ~spl4_3),
% 1.68/0.60    inference(avatar_split_clause,[],[f76,f88,f79])).
% 1.68/0.60  fof(f76,plain,(
% 1.68/0.60    ~r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK1) | r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)))),
% 1.68/0.60    inference(resolution,[],[f63,f72])).
% 1.68/0.60  fof(f72,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (sQ3_eqProxy(k4_xboole_0(X0,X1),X2) | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.68/0.60    inference(equality_proxy_replacement,[],[f42,f61])).
% 1.68/0.60  fof(f42,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f24])).
% 1.68/0.60  fof(f86,plain,(
% 1.68/0.60    spl4_1 | spl4_2),
% 1.68/0.60    inference(avatar_split_clause,[],[f75,f83,f79])).
% 1.68/0.60  fof(f75,plain,(
% 1.68/0.60    r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),sK0) | r2_hidden(sK2(sK0,sK1,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)))),
% 1.68/0.60    inference(resolution,[],[f63,f73])).
% 1.68/0.60  fof(f73,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (sQ3_eqProxy(k4_xboole_0(X0,X1),X2) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.68/0.60    inference(equality_proxy_replacement,[],[f41,f61])).
% 1.68/0.60  fof(f41,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f24])).
% 1.68/0.60  % SZS output end Proof for theBenchmark
% 1.68/0.60  % (2365)------------------------------
% 1.68/0.60  % (2365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.60  % (2365)Termination reason: Refutation
% 1.68/0.60  
% 1.68/0.60  % (2365)Memory used [KB]: 6268
% 1.68/0.60  % (2365)Time elapsed: 0.193 s
% 1.68/0.60  % (2365)------------------------------
% 1.68/0.60  % (2365)------------------------------
% 1.68/0.60  % (2346)Success in time 0.24 s
%------------------------------------------------------------------------------
