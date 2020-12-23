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
% DateTime   : Thu Dec  3 12:47:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 113 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  230 ( 321 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f103,f121,f124,f147,f152,f161])).

fof(f161,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | ~ spl8_3 ),
    inference(resolution,[],[f158,f32])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f158,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_3 ),
    inference(resolution,[],[f154,f31])).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f154,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f72,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f72,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_relat_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl8_3
  <=> r2_hidden(sK0(k1_xboole_0,k1_relat_1(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f152,plain,
    ( spl8_3
    | spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f96,f74,f59,f70])).

fof(f59,plain,
    ( spl8_1
  <=> sQ7_eqProxy(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f74,plain,
    ( spl8_4
  <=> r2_hidden(sK0(k1_xboole_0,k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f96,plain,
    ( sQ7_eqProxy(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | r2_hidden(sK0(k1_xboole_0,k1_relat_1(k1_xboole_0)),k1_xboole_0)
    | spl8_4 ),
    inference(resolution,[],[f75,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sQ7_eqProxy(X0,X1)
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f33,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f75,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f147,plain,(
    ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl8_4 ),
    inference(resolution,[],[f141,f32])).

fof(f141,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_4 ),
    inference(resolution,[],[f139,f31])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )
    | ~ spl8_4 ),
    inference(resolution,[],[f128,f44])).

fof(f128,plain,
    ( r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_relat_1(k1_xboole_0)),sK6(k1_xboole_0,sK0(k1_xboole_0,k1_relat_1(k1_xboole_0)))),k1_xboole_0)
    | ~ spl8_4 ),
    inference(resolution,[],[f76,f48])).

fof(f48,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f76,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f124,plain,
    ( spl8_5
    | spl8_2
    | spl8_6 ),
    inference(avatar_split_clause,[],[f98,f86,f63,f82])).

fof(f82,plain,
    ( spl8_5
  <=> r2_hidden(sK0(k1_xboole_0,k2_relat_1(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f63,plain,
    ( spl8_2
  <=> sQ7_eqProxy(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f86,plain,
    ( spl8_6
  <=> r2_hidden(sK0(k1_xboole_0,k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f98,plain,
    ( sQ7_eqProxy(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | r2_hidden(sK0(k1_xboole_0,k2_relat_1(k1_xboole_0)),k1_xboole_0)
    | spl8_6 ),
    inference(resolution,[],[f87,f52])).

fof(f87,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f121,plain,(
    ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl8_6 ),
    inference(resolution,[],[f115,f32])).

fof(f115,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_6 ),
    inference(resolution,[],[f113,f31])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )
    | ~ spl8_6 ),
    inference(resolution,[],[f106,f44])).

fof(f106,plain,
    ( r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0(k1_xboole_0,k2_relat_1(k1_xboole_0))),sK0(k1_xboole_0,k2_relat_1(k1_xboole_0))),k1_xboole_0)
    | ~ spl8_6 ),
    inference(resolution,[],[f88,f46])).

fof(f46,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22,f21,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f88,plain,
    ( r2_hidden(sK0(k1_xboole_0,k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f103,plain,(
    ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | ~ spl8_5 ),
    inference(resolution,[],[f95,f32])).

fof(f95,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_5 ),
    inference(resolution,[],[f93,f31])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )
    | ~ spl8_5 ),
    inference(resolution,[],[f84,f44])).

fof(f84,plain,
    ( r2_hidden(sK0(k1_xboole_0,k2_relat_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f66,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f50,f63,f59])).

fof(f50,plain,
    ( ~ sQ7_eqProxy(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ sQ7_eqProxy(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(equality_proxy_replacement,[],[f30,f49,f49])).

fof(f30,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:36:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (452)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (462)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (461)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (461)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f66,f103,f121,f124,f147,f152,f161])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    ~spl8_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f159])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    $false | ~spl8_3),
% 0.21/0.53    inference(resolution,[],[f158,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl8_3),
% 0.21/0.53    inference(resolution,[],[f154,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl8_3),
% 0.21/0.53    inference(resolution,[],[f72,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    r2_hidden(sK0(k1_xboole_0,k1_relat_1(k1_xboole_0)),k1_xboole_0) | ~spl8_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    spl8_3 <=> r2_hidden(sK0(k1_xboole_0,k1_relat_1(k1_xboole_0)),k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    spl8_3 | spl8_1 | spl8_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f96,f74,f59,f70])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    spl8_1 <=> sQ7_eqProxy(k1_xboole_0,k1_relat_1(k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    spl8_4 <=> r2_hidden(sK0(k1_xboole_0,k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    sQ7_eqProxy(k1_xboole_0,k1_relat_1(k1_xboole_0)) | r2_hidden(sK0(k1_xboole_0,k1_relat_1(k1_xboole_0)),k1_xboole_0) | spl8_4),
% 0.21/0.53    inference(resolution,[],[f75,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sQ7_eqProxy(X0,X1) | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 0.21/0.53    inference(equality_proxy_replacement,[],[f33,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ! [X1,X0] : (sQ7_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.53    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.21/0.53    inference(nnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ~r2_hidden(sK0(k1_xboole_0,k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)) | spl8_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f74])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    ~spl8_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f145])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    $false | ~spl8_4),
% 0.21/0.53    inference(resolution,[],[f141,f32])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl8_4),
% 0.21/0.53    inference(resolution,[],[f139,f31])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl8_4),
% 0.21/0.53    inference(resolution,[],[f128,f44])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_relat_1(k1_xboole_0)),sK6(k1_xboole_0,sK0(k1_xboole_0,k1_relat_1(k1_xboole_0)))),k1_xboole_0) | ~spl8_4),
% 0.21/0.53    inference(resolution,[],[f76,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 0.21/0.53    inference(equality_resolution,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.53    inference(rectify,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    r2_hidden(sK0(k1_xboole_0,k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)) | ~spl8_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f74])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    spl8_5 | spl8_2 | spl8_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f98,f86,f63,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    spl8_5 <=> r2_hidden(sK0(k1_xboole_0,k2_relat_1(k1_xboole_0)),k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    spl8_2 <=> sQ7_eqProxy(k1_xboole_0,k2_relat_1(k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl8_6 <=> r2_hidden(sK0(k1_xboole_0,k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    sQ7_eqProxy(k1_xboole_0,k2_relat_1(k1_xboole_0)) | r2_hidden(sK0(k1_xboole_0,k2_relat_1(k1_xboole_0)),k1_xboole_0) | spl8_6),
% 0.21/0.53    inference(resolution,[],[f87,f52])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ~r2_hidden(sK0(k1_xboole_0,k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) | spl8_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f86])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    ~spl8_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f119])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    $false | ~spl8_6),
% 0.21/0.53    inference(resolution,[],[f115,f32])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl8_6),
% 0.21/0.53    inference(resolution,[],[f113,f31])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl8_6),
% 0.21/0.53    inference(resolution,[],[f106,f44])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0(k1_xboole_0,k2_relat_1(k1_xboole_0))),sK0(k1_xboole_0,k2_relat_1(k1_xboole_0))),k1_xboole_0) | ~spl8_6),
% 0.21/0.53    inference(resolution,[],[f88,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 0.21/0.53    inference(equality_resolution,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22,f21,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) => r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.53    inference(rectify,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    r2_hidden(sK0(k1_xboole_0,k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) | ~spl8_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f86])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ~spl8_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f101])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    $false | ~spl8_5),
% 0.21/0.53    inference(resolution,[],[f95,f32])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl8_5),
% 0.21/0.53    inference(resolution,[],[f93,f31])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl8_5),
% 0.21/0.53    inference(resolution,[],[f84,f44])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    r2_hidden(sK0(k1_xboole_0,k2_relat_1(k1_xboole_0)),k1_xboole_0) | ~spl8_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f82])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ~spl8_1 | ~spl8_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f50,f63,f59])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ~sQ7_eqProxy(k1_xboole_0,k2_relat_1(k1_xboole_0)) | ~sQ7_eqProxy(k1_xboole_0,k1_relat_1(k1_xboole_0))),
% 0.21/0.53    inference(equality_proxy_replacement,[],[f30,f49,f49])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,negated_conjecture,(
% 0.21/0.53    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.21/0.53    inference(negated_conjecture,[],[f8])).
% 0.21/0.53  fof(f8,conjecture,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (461)------------------------------
% 0.21/0.53  % (461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (461)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (461)Memory used [KB]: 6268
% 0.21/0.53  % (461)Time elapsed: 0.116 s
% 0.21/0.53  % (461)------------------------------
% 0.21/0.53  % (461)------------------------------
% 0.21/0.53  % (445)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (450)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (470)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (448)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (453)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (463)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (475)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.55  % (444)Success in time 0.186 s
%------------------------------------------------------------------------------
