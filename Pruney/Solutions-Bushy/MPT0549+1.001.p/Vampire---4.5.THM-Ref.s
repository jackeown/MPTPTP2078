%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0549+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:10 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 285 expanded)
%              Number of leaves         :   26 (  98 expanded)
%              Depth                    :   15
%              Number of atoms          :  380 (1060 expanded)
%              Number of equality atoms :   48 ( 132 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f517,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f69,f73,f126,f132,f137,f158,f167,f179,f410,f496,f516])).

fof(f516,plain,
    ( spl8_1
    | ~ spl8_14
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f506,f494,f165,f61])).

fof(f61,plain,
    ( spl8_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f165,plain,
    ( spl8_14
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f494,plain,
    ( spl8_40
  <=> ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f506,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl8_14
    | ~ spl8_40 ),
    inference(resolution,[],[f495,f265])).

fof(f265,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k1_xboole_0,X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f258,f166])).

fof(f166,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f258,plain,(
    ! [X0] :
      ( k1_relat_1(k1_xboole_0) = X0
      | r2_hidden(sK4(k1_xboole_0,X0),X0) ) ),
    inference(resolution,[],[f52,f97])).

fof(f97,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f81,f43])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f81,plain,(
    ! [X2,X3,X1] :
      ( k1_xboole_0 != k3_xboole_0(X3,X2)
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f46,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
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

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

% (9946)Refutation not found, incomplete strategy% (9946)------------------------------
% (9946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9946)Termination reason: Refutation not found, incomplete strategy

% (9946)Memory used [KB]: 6140
% (9946)Time elapsed: 0.081 s
% (9946)------------------------------
% (9946)------------------------------
fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).

fof(f30,plain,(
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

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f495,plain,
    ( ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK1,sK0))
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f494])).

fof(f496,plain,
    ( ~ spl8_3
    | spl8_40
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f491,f71,f64,f494,f71])).

fof(f64,plain,
    ( spl8_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f71,plain,
    ( spl8_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f491,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK1,sK0))
        | ~ v1_relat_1(sK1) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f488])).

fof(f488,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK1,sK0))
        | ~ r2_hidden(X0,k9_relat_1(sK1,sK0))
        | ~ v1_relat_1(sK1) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f425,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
            & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
        & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f425,plain,
    ( ! [X5] :
        ( ~ r2_hidden(sK7(X5,sK0,sK1),k1_relat_1(sK1))
        | ~ r2_hidden(X5,k9_relat_1(sK1,sK0)) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f415,f111])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK7(X0,X1,sK1),X1)
        | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f56,f72])).

fof(f72,plain,
    ( v1_relat_1(sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK7(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f415,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f68,f46])).

fof(f68,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f410,plain,
    ( spl8_2
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f409,f71,f61,f64])).

fof(f409,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f406])).

fof(f406,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(resolution,[],[f332,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f332,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK3(X4,sK0),k1_relat_1(sK1))
        | r1_xboole_0(X4,sK0) )
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(resolution,[],[f327,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f327,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(resolution,[],[f325,f97])).

fof(f325,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(sK1,X0),k1_xboole_0)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(superposition,[],[f309,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f309,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK6(sK1,X3),k9_relat_1(sK1,X4))
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | ~ r2_hidden(X3,X4) )
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,X4)
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | r2_hidden(sK6(sK1,X3),k9_relat_1(sK1,X4))
        | ~ r2_hidden(X3,k1_relat_1(sK1)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f304,f59])).

fof(f59,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f304,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X2),sK1)
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(X2,k9_relat_1(sK1,X1)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f57,f72])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f179,plain,(
    ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl8_13 ),
    inference(resolution,[],[f157,f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f3,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f157,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k1_relat_1(k1_xboole_0))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl8_13
  <=> ! [X2] : ~ m1_subset_1(X2,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f167,plain,
    ( spl8_14
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f163,f153,f165])).

fof(f153,plain,
    ( spl8_12
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f163,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_12 ),
    inference(resolution,[],[f154,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f154,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f153])).

fof(f158,plain,
    ( spl8_12
    | spl8_13
    | ~ spl8_3
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f151,f135,f71,f156,f153])).

fof(f135,plain,
    ( spl8_11
  <=> k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f151,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_relat_1(k1_xboole_0))
        | v1_xboole_0(k1_relat_1(k1_xboole_0)) )
    | ~ spl8_3
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f150,f136])).

fof(f136,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f150,plain,
    ( ! [X2] :
        ( v1_xboole_0(k1_relat_1(k1_xboole_0))
        | ~ m1_subset_1(X2,k1_relat_1(k9_relat_1(sK1,k1_xboole_0))) )
    | ~ spl8_3
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f144,f136])).

fof(f144,plain,
    ( ! [X2] :
        ( v1_xboole_0(k1_relat_1(k9_relat_1(sK1,k1_xboole_0)))
        | ~ m1_subset_1(X2,k1_relat_1(k9_relat_1(sK1,k1_xboole_0))) )
    | ~ spl8_3 ),
    inference(resolution,[],[f116,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f116,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_relat_1(k9_relat_1(sK1,k1_xboole_0)))
    | ~ spl8_3 ),
    inference(resolution,[],[f114,f59])).

fof(f114,plain,
    ( ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK1,k1_xboole_0))
    | ~ spl8_3 ),
    inference(resolution,[],[f111,f97])).

fof(f137,plain,
    ( spl8_11
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f133,f124,f135])).

fof(f124,plain,
    ( spl8_10
  <=> v1_xboole_0(k9_relat_1(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f133,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)
    | ~ spl8_10 ),
    inference(resolution,[],[f125,f41])).

fof(f125,plain,
    ( v1_xboole_0(k9_relat_1(sK1,k1_xboole_0))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f132,plain,(
    ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl8_9 ),
    inference(resolution,[],[f122,f42])).

fof(f122,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k9_relat_1(sK1,k1_xboole_0))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl8_9
  <=> ! [X0] : ~ m1_subset_1(X0,k9_relat_1(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f126,plain,
    ( spl8_9
    | spl8_10
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f115,f71,f124,f121])).

fof(f115,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK1,k1_xboole_0))
        | ~ m1_subset_1(X0,k9_relat_1(sK1,k1_xboole_0)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f114,f47])).

fof(f73,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f38,f71])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k9_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k9_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k9_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k9_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k9_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f69,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f39,f64,f61])).

fof(f39,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f40,f64,f61])).

fof(f40,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
