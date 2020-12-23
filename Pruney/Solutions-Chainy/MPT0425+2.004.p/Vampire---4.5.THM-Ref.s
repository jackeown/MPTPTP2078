%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 150 expanded)
%              Number of leaves         :   25 (  66 expanded)
%              Depth                    :    7
%              Number of atoms          :  277 ( 495 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f38,f43,f47,f51,f55,f59,f63,f67,f71,f87,f97,f108,f113,f125,f146,f169,f172])).

fof(f172,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_27 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f170,f33])).

fof(f33,plain,
    ( ~ r1_tarski(sK2,k3_tarski(sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl5_1
  <=> r1_tarski(sK2,k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f170,plain,
    ( r1_tarski(sK2,k3_tarski(sK0))
    | ~ spl5_3
    | ~ spl5_27 ),
    inference(resolution,[],[f168,f42])).

fof(f42,plain,
    ( r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl5_3
  <=> r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f168,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,k3_tarski(k2_xboole_0(X0,sK1)))
        | r1_tarski(sK2,k3_tarski(X0)) )
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl5_27
  <=> ! [X0] :
        ( ~ r1_tarski(sK2,k3_tarski(k2_xboole_0(X0,sK1)))
        | r1_tarski(sK2,k3_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f169,plain,
    ( spl5_27
    | ~ spl5_18
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f165,f143,f111,f167])).

fof(f111,plain,
    ( spl5_18
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))
        | ~ r1_xboole_0(X2,k3_tarski(X1))
        | r1_tarski(X2,k3_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f143,plain,
    ( spl5_24
  <=> r1_xboole_0(sK2,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,k3_tarski(k2_xboole_0(X0,sK1)))
        | r1_tarski(sK2,k3_tarski(X0)) )
    | ~ spl5_18
    | ~ spl5_24 ),
    inference(resolution,[],[f112,f145])).

fof(f145,plain,
    ( r1_xboole_0(sK2,k3_tarski(sK1))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f143])).

fof(f112,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X2,k3_tarski(X1))
        | ~ r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))
        | r1_tarski(X2,k3_tarski(X0)) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f111])).

fof(f146,plain,
    ( spl5_24
    | ~ spl5_17
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f129,f123,f105,f143])).

fof(f105,plain,
    ( spl5_17
  <=> r1_xboole_0(k3_tarski(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f123,plain,
    ( spl5_20
  <=> ! [X3,X2] :
        ( ~ r1_xboole_0(X2,X3)
        | r1_xboole_0(X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f129,plain,
    ( r1_xboole_0(sK2,k3_tarski(sK1))
    | ~ spl5_17
    | ~ spl5_20 ),
    inference(resolution,[],[f124,f107])).

fof(f107,plain,
    ( r1_xboole_0(k3_tarski(sK1),sK2)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f105])).

fof(f124,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(X2,X3)
        | r1_xboole_0(X3,X2) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f123])).

fof(f125,plain,
    ( spl5_20
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f116,f85,f57,f123])).

fof(f57,plain,
    ( spl5_7
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(X0,X1),X0)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f85,plain,
    ( spl5_13
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK3(X0,X1),X2)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f116,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(X2,X3)
        | r1_xboole_0(X3,X2) )
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(X2,X3)
        | r1_xboole_0(X3,X2)
        | r1_xboole_0(X3,X2) )
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(resolution,[],[f86,f58])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X0)
        | r1_xboole_0(X0,X1) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f86,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK3(X0,X1),X2)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X1) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f113,plain,
    ( spl5_18
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f109,f69,f45,f111])).

fof(f45,plain,
    ( spl5_4
  <=> ! [X1,X0] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f69,plain,
    ( spl5_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X1)
        | ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f109,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))
        | ~ r1_xboole_0(X2,k3_tarski(X1))
        | r1_tarski(X2,k3_tarski(X0)) )
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(superposition,[],[f70,f46])).

fof(f46,plain,
    ( ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,X2)
        | r1_tarski(X0,X1) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f108,plain,
    ( spl5_17
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f103,f95,f61,f105])).

fof(f61,plain,
    ( spl5_8
  <=> ! [X1,X0] :
        ( r1_xboole_0(k3_tarski(X0),X1)
        | ~ r1_xboole_0(sK4(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f95,plain,
    ( spl5_15
  <=> ! [X0] :
        ( r1_xboole_0(k3_tarski(sK1),X0)
        | r1_xboole_0(sK4(sK1,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f103,plain,
    ( r1_xboole_0(k3_tarski(sK1),sK2)
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,
    ( r1_xboole_0(k3_tarski(sK1),sK2)
    | r1_xboole_0(k3_tarski(sK1),sK2)
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(resolution,[],[f96,f62])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(sK4(X0,X1),X1)
        | r1_xboole_0(k3_tarski(X0),X1) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f96,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK4(sK1,X0),sK2)
        | r1_xboole_0(k3_tarski(sK1),X0) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f97,plain,
    ( spl5_15
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f92,f65,f36,f95])).

fof(f36,plain,
    ( spl5_2
  <=> ! [X3] :
        ( r1_xboole_0(X3,sK2)
        | ~ r2_hidden(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f65,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( r1_xboole_0(k3_tarski(X0),X1)
        | r2_hidden(sK4(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f92,plain,
    ( ! [X0] :
        ( r1_xboole_0(k3_tarski(sK1),X0)
        | r1_xboole_0(sK4(sK1,X0),sK2) )
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(resolution,[],[f66,f37])).

fof(f37,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | r1_xboole_0(X3,sK2) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1),X0)
        | r1_xboole_0(k3_tarski(X0),X1) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f65])).

fof(f87,plain,
    ( spl5_13
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f82,f53,f49,f85])).

fof(f49,plain,
    ( spl5_5
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f53,plain,
    ( spl5_6
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(X0,X1),X1)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f82,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK3(X0,X1),X2)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X1) )
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f50,f54])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f50,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f71,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f29,f69])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f67,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f27,f65])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ( ~ r1_xboole_0(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_xboole_0(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(f63,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ~ r1_xboole_0(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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

fof(f55,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f25,f53])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f26,f49])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f43,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f20,f40])).

fof(f20,plain,(
    r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_tarski(sK2,k3_tarski(sK0))
    & ! [X3] :
        ( r1_xboole_0(X3,sK2)
        | ~ r2_hidden(X3,sK1) )
    & r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X2,k3_tarski(X0))
        & ! [X3] :
            ( r1_xboole_0(X3,X2)
            | ~ r2_hidden(X3,X1) )
        & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
   => ( ~ r1_tarski(sK2,k3_tarski(sK0))
      & ! [X3] :
          ( r1_xboole_0(X3,sK2)
          | ~ r2_hidden(X3,sK1) )
      & r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,k3_tarski(X0))
      & ! [X3] :
          ( r1_xboole_0(X3,X2)
          | ~ r2_hidden(X3,X1) )
      & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,k3_tarski(X0))
      & ! [X3] :
          ( r1_xboole_0(X3,X2)
          | ~ r2_hidden(X3,X1) )
      & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( r2_hidden(X3,X1)
             => r1_xboole_0(X3,X2) )
          & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
       => r1_tarski(X2,k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r1_xboole_0(X3,X2) )
        & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
     => r1_tarski(X2,k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_setfam_1)).

fof(f38,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f21,f36])).

fof(f21,plain,(
    ! [X3] :
      ( r1_xboole_0(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f22,f31])).

fof(f22,plain,(
    ~ r1_tarski(sK2,k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:42 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.41  % (18771)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.41  % (18764)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.42  % (18769)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (18770)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (18769)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f173,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f34,f38,f43,f47,f51,f55,f59,f63,f67,f71,f87,f97,f108,f113,f125,f146,f169,f172])).
% 0.21/0.42  fof(f172,plain,(
% 0.21/0.42    spl5_1 | ~spl5_3 | ~spl5_27),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.42  fof(f171,plain,(
% 0.21/0.42    $false | (spl5_1 | ~spl5_3 | ~spl5_27)),
% 0.21/0.42    inference(subsumption_resolution,[],[f170,f33])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ~r1_tarski(sK2,k3_tarski(sK0)) | spl5_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    spl5_1 <=> r1_tarski(sK2,k3_tarski(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.42  fof(f170,plain,(
% 0.21/0.42    r1_tarski(sK2,k3_tarski(sK0)) | (~spl5_3 | ~spl5_27)),
% 0.21/0.42    inference(resolution,[],[f168,f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) | ~spl5_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f40])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl5_3 <=> r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.42  fof(f168,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(sK2,k3_tarski(k2_xboole_0(X0,sK1))) | r1_tarski(sK2,k3_tarski(X0))) ) | ~spl5_27),
% 0.21/0.42    inference(avatar_component_clause,[],[f167])).
% 0.21/0.42  fof(f167,plain,(
% 0.21/0.42    spl5_27 <=> ! [X0] : (~r1_tarski(sK2,k3_tarski(k2_xboole_0(X0,sK1))) | r1_tarski(sK2,k3_tarski(X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.42  fof(f169,plain,(
% 0.21/0.42    spl5_27 | ~spl5_18 | ~spl5_24),
% 0.21/0.42    inference(avatar_split_clause,[],[f165,f143,f111,f167])).
% 0.21/0.42  fof(f111,plain,(
% 0.21/0.42    spl5_18 <=> ! [X1,X0,X2] : (~r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) | ~r1_xboole_0(X2,k3_tarski(X1)) | r1_tarski(X2,k3_tarski(X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.42  fof(f143,plain,(
% 0.21/0.42    spl5_24 <=> r1_xboole_0(sK2,k3_tarski(sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.42  fof(f165,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(sK2,k3_tarski(k2_xboole_0(X0,sK1))) | r1_tarski(sK2,k3_tarski(X0))) ) | (~spl5_18 | ~spl5_24)),
% 0.21/0.42    inference(resolution,[],[f112,f145])).
% 0.21/0.42  fof(f145,plain,(
% 0.21/0.42    r1_xboole_0(sK2,k3_tarski(sK1)) | ~spl5_24),
% 0.21/0.42    inference(avatar_component_clause,[],[f143])).
% 0.21/0.42  fof(f112,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X2,k3_tarski(X1)) | ~r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) | r1_tarski(X2,k3_tarski(X0))) ) | ~spl5_18),
% 0.21/0.42    inference(avatar_component_clause,[],[f111])).
% 0.21/0.42  fof(f146,plain,(
% 0.21/0.42    spl5_24 | ~spl5_17 | ~spl5_20),
% 0.21/0.42    inference(avatar_split_clause,[],[f129,f123,f105,f143])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    spl5_17 <=> r1_xboole_0(k3_tarski(sK1),sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.42  fof(f123,plain,(
% 0.21/0.42    spl5_20 <=> ! [X3,X2] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.42  fof(f129,plain,(
% 0.21/0.42    r1_xboole_0(sK2,k3_tarski(sK1)) | (~spl5_17 | ~spl5_20)),
% 0.21/0.42    inference(resolution,[],[f124,f107])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    r1_xboole_0(k3_tarski(sK1),sK2) | ~spl5_17),
% 0.21/0.42    inference(avatar_component_clause,[],[f105])).
% 0.21/0.42  fof(f124,plain,(
% 0.21/0.42    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) ) | ~spl5_20),
% 0.21/0.42    inference(avatar_component_clause,[],[f123])).
% 0.21/0.42  fof(f125,plain,(
% 0.21/0.42    spl5_20 | ~spl5_7 | ~spl5_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f116,f85,f57,f123])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    spl5_7 <=> ! [X1,X0] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    spl5_13 <=> ! [X1,X0,X2] : (~r2_hidden(sK3(X0,X1),X2) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.42  fof(f116,plain,(
% 0.21/0.42    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) ) | (~spl5_7 | ~spl5_13)),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f115])).
% 0.21/0.42  fof(f115,plain,(
% 0.21/0.42    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) ) | (~spl5_7 | ~spl5_13)),
% 0.21/0.42    inference(resolution,[],[f86,f58])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) ) | ~spl5_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f57])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1),X2) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X1)) ) | ~spl5_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f85])).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    spl5_18 | ~spl5_4 | ~spl5_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f109,f69,f45,f111])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    spl5_4 <=> ! [X1,X0] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    spl5_10 <=> ! [X1,X0,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.42  fof(f109,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) | ~r1_xboole_0(X2,k3_tarski(X1)) | r1_tarski(X2,k3_tarski(X0))) ) | (~spl5_4 | ~spl5_10)),
% 0.21/0.42    inference(superposition,[],[f70,f46])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) ) | ~spl5_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f45])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) ) | ~spl5_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f69])).
% 0.21/0.42  fof(f108,plain,(
% 0.21/0.42    spl5_17 | ~spl5_8 | ~spl5_15),
% 0.21/0.42    inference(avatar_split_clause,[],[f103,f95,f61,f105])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    spl5_8 <=> ! [X1,X0] : (r1_xboole_0(k3_tarski(X0),X1) | ~r1_xboole_0(sK4(X0,X1),X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.42  fof(f95,plain,(
% 0.21/0.42    spl5_15 <=> ! [X0] : (r1_xboole_0(k3_tarski(sK1),X0) | r1_xboole_0(sK4(sK1,X0),sK2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    r1_xboole_0(k3_tarski(sK1),sK2) | (~spl5_8 | ~spl5_15)),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f102])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    r1_xboole_0(k3_tarski(sK1),sK2) | r1_xboole_0(k3_tarski(sK1),sK2) | (~spl5_8 | ~spl5_15)),
% 0.21/0.42    inference(resolution,[],[f96,f62])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(sK4(X0,X1),X1) | r1_xboole_0(k3_tarski(X0),X1)) ) | ~spl5_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f61])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(sK4(sK1,X0),sK2) | r1_xboole_0(k3_tarski(sK1),X0)) ) | ~spl5_15),
% 0.21/0.42    inference(avatar_component_clause,[],[f95])).
% 0.21/0.42  fof(f97,plain,(
% 0.21/0.42    spl5_15 | ~spl5_2 | ~spl5_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f92,f65,f36,f95])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl5_2 <=> ! [X3] : (r1_xboole_0(X3,sK2) | ~r2_hidden(X3,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    spl5_9 <=> ! [X1,X0] : (r1_xboole_0(k3_tarski(X0),X1) | r2_hidden(sK4(X0,X1),X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(k3_tarski(sK1),X0) | r1_xboole_0(sK4(sK1,X0),sK2)) ) | (~spl5_2 | ~spl5_9)),
% 0.21/0.42    inference(resolution,[],[f66,f37])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    ( ! [X3] : (~r2_hidden(X3,sK1) | r1_xboole_0(X3,sK2)) ) | ~spl5_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f36])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(k3_tarski(X0),X1)) ) | ~spl5_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f65])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    spl5_13 | ~spl5_5 | ~spl5_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f82,f53,f49,f85])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    spl5_5 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    spl5_6 <=> ! [X1,X0] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1),X2) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X1)) ) | (~spl5_5 | ~spl5_6)),
% 0.21/0.43    inference(resolution,[],[f50,f54])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) ) | ~spl5_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f53])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) ) | ~spl5_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f49])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    spl5_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f29,f69])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.43    inference(flattening,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    spl5_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f65])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | (~r1_xboole_0(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X1,X0] : (? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)) => (~r1_xboole_0(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | ? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_xboole_0(X2,X1)) => r1_xboole_0(k3_tarski(X0),X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    spl5_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f61])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | ~r1_xboole_0(sK4(X0,X1),X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    spl5_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f57])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(rectify,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl5_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f25,f53])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    spl5_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f26,f49])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl5_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f45])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    spl5_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f40])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1)))),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ~r1_tarski(sK2,k3_tarski(sK0)) & ! [X3] : (r1_xboole_0(X3,sK2) | ~r2_hidden(X3,sK1)) & r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_tarski(X2,k3_tarski(X0)) & ! [X3] : (r1_xboole_0(X3,X2) | ~r2_hidden(X3,X1)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))) => (~r1_tarski(sK2,k3_tarski(sK0)) & ! [X3] : (r1_xboole_0(X3,sK2) | ~r2_hidden(X3,sK1)) & r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_tarski(X2,k3_tarski(X0)) & ! [X3] : (r1_xboole_0(X3,X2) | ~r2_hidden(X3,X1)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))))),
% 0.21/0.43    inference(flattening,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_tarski(X2,k3_tarski(X0)) & (! [X3] : (r1_xboole_0(X3,X2) | ~r2_hidden(X3,X1)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : ((! [X3] : (r2_hidden(X3,X1) => r1_xboole_0(X3,X2)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))) => r1_tarski(X2,k3_tarski(X0)))),
% 0.21/0.43    inference(negated_conjecture,[],[f5])).
% 0.21/0.43  fof(f5,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : ((! [X3] : (r2_hidden(X3,X1) => r1_xboole_0(X3,X2)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))) => r1_tarski(X2,k3_tarski(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_setfam_1)).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    spl5_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f21,f36])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X3] : (r1_xboole_0(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ~spl5_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f31])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ~r1_tarski(sK2,k3_tarski(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (18769)------------------------------
% 0.21/0.43  % (18769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (18769)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (18769)Memory used [KB]: 10618
% 0.21/0.43  % (18769)Time elapsed: 0.008 s
% 0.21/0.43  % (18769)------------------------------
% 0.21/0.43  % (18769)------------------------------
% 0.21/0.43  % (18763)Success in time 0.077 s
%------------------------------------------------------------------------------
