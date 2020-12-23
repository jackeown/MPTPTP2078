%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 149 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  305 ( 497 expanded)
%              Number of equality atoms :   48 (  92 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f71,f75,f79,f130,f137,f151,f182,f195,f201])).

fof(f201,plain,(
    ~ spl10_18 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | ~ spl10_18 ),
    inference(resolution,[],[f194,f85])).

fof(f85,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f84,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f84,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f45,f42])).

fof(f42,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f194,plain,
    ( r2_hidden(sK8(sK1,sK0),k1_xboole_0)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl10_18
  <=> r2_hidden(sK8(sK1,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f195,plain,
    ( ~ spl10_3
    | spl10_18
    | ~ spl10_2
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f191,f180,f66,f193,f73])).

fof(f73,plain,
    ( spl10_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f66,plain,
    ( spl10_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f180,plain,
    ( spl10_17
  <=> r2_hidden(k4_tarski(sK0,sK8(sK1,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f191,plain,
    ( r2_hidden(sK8(sK1,sK0),k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ spl10_2
    | ~ spl10_17 ),
    inference(forward_demodulation,[],[f188,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f188,plain,
    ( r2_hidden(sK8(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl10_17 ),
    inference(resolution,[],[f181,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f181,plain,
    ( r2_hidden(k4_tarski(sK0,sK8(sK1,sK0)),sK1)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( spl10_17
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f174,f63,f180])).

fof(f63,plain,
    ( spl10_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f174,plain,
    ( r2_hidden(k4_tarski(sK0,sK8(sK1,sK0)),sK1)
    | ~ spl10_1 ),
    inference(resolution,[],[f69,f61])).

fof(f61,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f69,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f151,plain,(
    ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl10_8 ),
    inference(resolution,[],[f136,f85])).

fof(f136,plain,
    ( r2_hidden(k4_tarski(sK4(k1_xboole_0,k11_relat_1(sK1,sK0)),sK3(k1_xboole_0,k11_relat_1(sK1,sK0))),k1_xboole_0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl10_8
  <=> r2_hidden(k4_tarski(sK4(k1_xboole_0,k11_relat_1(sK1,sK0)),sK3(k1_xboole_0,k11_relat_1(sK1,sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f137,plain,
    ( spl10_8
    | ~ spl10_4
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f133,f128,f77,f135])).

fof(f77,plain,
    ( spl10_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

% (3815)Refutation not found, incomplete strategy% (3815)------------------------------
% (3815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3815)Termination reason: Refutation not found, incomplete strategy

% (3815)Memory used [KB]: 10618
% (3815)Time elapsed: 0.060 s
% (3815)------------------------------
% (3815)------------------------------
fof(f128,plain,
    ( spl10_7
  <=> ! [X0] :
        ( k1_xboole_0 != k2_relat_1(X0)
        | r2_hidden(k4_tarski(sK4(X0,k11_relat_1(sK1,sK0)),sK3(X0,k11_relat_1(sK1,sK0))),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f133,plain,
    ( r2_hidden(k4_tarski(sK4(k1_xboole_0,k11_relat_1(sK1,sK0)),sK3(k1_xboole_0,k11_relat_1(sK1,sK0))),k1_xboole_0)
    | ~ spl10_4
    | ~ spl10_7 ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(k4_tarski(sK4(k1_xboole_0,k11_relat_1(sK1,sK0)),sK3(k1_xboole_0,k11_relat_1(sK1,sK0))),k1_xboole_0)
    | ~ spl10_4
    | ~ spl10_7 ),
    inference(superposition,[],[f129,f78])).

fof(f78,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f129,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_relat_1(X0)
        | r2_hidden(k4_tarski(sK4(X0,k11_relat_1(sK1,sK0)),sK3(X0,k11_relat_1(sK1,sK0))),X0) )
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f128])).

fof(f130,plain,
    ( spl10_1
    | spl10_7
    | spl10_2
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f122,f73,f66,f128,f63])).

fof(f122,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_relat_1(X0)
        | r2_hidden(k4_tarski(sK4(X0,k11_relat_1(sK1,sK0)),sK3(X0,k11_relat_1(sK1,sK0))),X0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
    | spl10_2
    | ~ spl10_3 ),
    inference(superposition,[],[f70,f111])).

fof(f111,plain,
    ( ! [X2,X3] :
        ( k2_relat_1(X3) = k11_relat_1(sK1,X2)
        | r2_hidden(k4_tarski(sK4(X3,k11_relat_1(sK1,X2)),sK3(X3,k11_relat_1(sK1,X2))),X3)
        | r2_hidden(X2,k1_relat_1(sK1)) )
    | ~ spl10_3 ),
    inference(resolution,[],[f106,f60])).

fof(f60,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f106,plain,
    ( ! [X12,X13] :
        ( r2_hidden(k4_tarski(X13,sK9(k11_relat_1(sK1,X13))),sK1)
        | k11_relat_1(sK1,X13) = k2_relat_1(X12)
        | r2_hidden(k4_tarski(sK4(X12,k11_relat_1(sK1,X13)),sK3(X12,k11_relat_1(sK1,X13))),X12) )
    | ~ spl10_3 ),
    inference(resolution,[],[f48,f94])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k11_relat_1(sK1,X0))
        | r2_hidden(k4_tarski(X0,sK9(k11_relat_1(sK1,X0))),sK1) )
    | ~ spl10_3 ),
    inference(resolution,[],[f93,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK9(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK9(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f14,f34])).

fof(f34,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK9(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK9(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k11_relat_1(sK1,X1))
        | r2_hidden(k4_tarski(X1,X0),sK1) )
    | ~ spl10_3 ),
    inference(resolution,[],[f57,f74])).

fof(f74,plain,
    ( v1_relat_1(sK1)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f26,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f70,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f79,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f41,f77])).

fof(f41,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f75,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f37,f73])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f71,plain,
    ( spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f38,f66,f63])).

fof(f38,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f39,f66,f63])).

fof(f39,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (3814)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (3814)Refutation not found, incomplete strategy% (3814)------------------------------
% 0.21/0.46  % (3814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (3814)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (3814)Memory used [KB]: 6140
% 0.21/0.46  % (3814)Time elapsed: 0.049 s
% 0.21/0.46  % (3814)------------------------------
% 0.21/0.46  % (3814)------------------------------
% 0.21/0.46  % (3820)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (3833)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.47  % (3815)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (3820)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f202,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f68,f71,f75,f79,f130,f137,f151,f182,f195,f201])).
% 0.21/0.47  fof(f201,plain,(
% 0.21/0.47    ~spl10_18),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f200])).
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    $false | ~spl10_18),
% 0.21/0.47    inference(resolution,[],[f194,f85])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f84,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 0.21/0.47    inference(resolution,[],[f45,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(rectify,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.47  fof(f194,plain,(
% 0.21/0.47    r2_hidden(sK8(sK1,sK0),k1_xboole_0) | ~spl10_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f193])).
% 0.21/0.47  fof(f193,plain,(
% 0.21/0.47    spl10_18 <=> r2_hidden(sK8(sK1,sK0),k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.21/0.47  fof(f195,plain,(
% 0.21/0.47    ~spl10_3 | spl10_18 | ~spl10_2 | ~spl10_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f191,f180,f66,f193,f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl10_3 <=> v1_relat_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    spl10_2 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.47  fof(f180,plain,(
% 0.21/0.47    spl10_17 <=> r2_hidden(k4_tarski(sK0,sK8(sK1,sK0)),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.21/0.47  fof(f191,plain,(
% 0.21/0.47    r2_hidden(sK8(sK1,sK0),k1_xboole_0) | ~v1_relat_1(sK1) | (~spl10_2 | ~spl10_17)),
% 0.21/0.47    inference(forward_demodulation,[],[f188,f67])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl10_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f66])).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    r2_hidden(sK8(sK1,sK0),k11_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~spl10_17),
% 0.21/0.47    inference(resolution,[],[f181,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(nnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.21/0.47  fof(f181,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK0,sK8(sK1,sK0)),sK1) | ~spl10_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f180])).
% 0.21/0.47  fof(f182,plain,(
% 0.21/0.47    spl10_17 | ~spl10_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f174,f63,f180])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl10_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.47  fof(f174,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK0,sK8(sK1,sK0)),sK1) | ~spl10_1),
% 0.21/0.47    inference(resolution,[],[f69,f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X0,X5] : (~r2_hidden(X5,k1_relat_1(X0)) | r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f29,f32,f31,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.47    inference(rectify,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl10_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f63])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    ~spl10_8),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f149])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    $false | ~spl10_8),
% 0.21/0.47    inference(resolution,[],[f136,f85])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK4(k1_xboole_0,k11_relat_1(sK1,sK0)),sK3(k1_xboole_0,k11_relat_1(sK1,sK0))),k1_xboole_0) | ~spl10_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f135])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    spl10_8 <=> r2_hidden(k4_tarski(sK4(k1_xboole_0,k11_relat_1(sK1,sK0)),sK3(k1_xboole_0,k11_relat_1(sK1,sK0))),k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    spl10_8 | ~spl10_4 | ~spl10_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f133,f128,f77,f135])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl10_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.47  % (3815)Refutation not found, incomplete strategy% (3815)------------------------------
% 0.21/0.47  % (3815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (3815)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (3815)Memory used [KB]: 10618
% 0.21/0.47  % (3815)Time elapsed: 0.060 s
% 0.21/0.47  % (3815)------------------------------
% 0.21/0.47  % (3815)------------------------------
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    spl10_7 <=> ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | r2_hidden(k4_tarski(sK4(X0,k11_relat_1(sK1,sK0)),sK3(X0,k11_relat_1(sK1,sK0))),X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK4(k1_xboole_0,k11_relat_1(sK1,sK0)),sK3(k1_xboole_0,k11_relat_1(sK1,sK0))),k1_xboole_0) | (~spl10_4 | ~spl10_7)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f131])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | r2_hidden(k4_tarski(sK4(k1_xboole_0,k11_relat_1(sK1,sK0)),sK3(k1_xboole_0,k11_relat_1(sK1,sK0))),k1_xboole_0) | (~spl10_4 | ~spl10_7)),
% 0.21/0.47    inference(superposition,[],[f129,f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl10_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f77])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | r2_hidden(k4_tarski(sK4(X0,k11_relat_1(sK1,sK0)),sK3(X0,k11_relat_1(sK1,sK0))),X0)) ) | ~spl10_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f128])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    spl10_1 | spl10_7 | spl10_2 | ~spl10_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f122,f73,f66,f128,f63])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | r2_hidden(k4_tarski(sK4(X0,k11_relat_1(sK1,sK0)),sK3(X0,k11_relat_1(sK1,sK0))),X0) | r2_hidden(sK0,k1_relat_1(sK1))) ) | (spl10_2 | ~spl10_3)),
% 0.21/0.47    inference(superposition,[],[f70,f111])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ( ! [X2,X3] : (k2_relat_1(X3) = k11_relat_1(sK1,X2) | r2_hidden(k4_tarski(sK4(X3,k11_relat_1(sK1,X2)),sK3(X3,k11_relat_1(sK1,X2))),X3) | r2_hidden(X2,k1_relat_1(sK1))) ) | ~spl10_3),
% 0.21/0.47    inference(resolution,[],[f106,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.21/0.47    inference(equality_resolution,[],[f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    ( ! [X12,X13] : (r2_hidden(k4_tarski(X13,sK9(k11_relat_1(sK1,X13))),sK1) | k11_relat_1(sK1,X13) = k2_relat_1(X12) | r2_hidden(k4_tarski(sK4(X12,k11_relat_1(sK1,X13)),sK3(X12,k11_relat_1(sK1,X13))),X12)) ) | ~spl10_3),
% 0.21/0.47    inference(resolution,[],[f48,f94])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X1,k11_relat_1(sK1,X0)) | r2_hidden(k4_tarski(X0,sK9(k11_relat_1(sK1,X0))),sK1)) ) | ~spl10_3),
% 0.21/0.47    inference(resolution,[],[f93,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK9(X1),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK9(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK9(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f14,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK9(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK9(X1),X1)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k11_relat_1(sK1,X1)) | r2_hidden(k4_tarski(X1,X0),sK1)) ) | ~spl10_3),
% 0.21/0.47    inference(resolution,[],[f57,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    v1_relat_1(sK1) | ~spl10_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f73])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f36])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | k2_relat_1(X0) = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f26,f25,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.47    inference(rectify,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    k1_xboole_0 != k11_relat_1(sK1,sK0) | spl10_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f66])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl10_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f41,f77])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    spl10_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f37,f73])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    v1_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.47    inference(negated_conjecture,[],[f9])).
% 0.21/0.47  fof(f9,conjecture,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl10_1 | ~spl10_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f38,f66,f63])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ~spl10_1 | spl10_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f39,f66,f63])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (3820)------------------------------
% 0.21/0.47  % (3820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (3820)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (3820)Memory used [KB]: 10746
% 0.21/0.47  % (3820)Time elapsed: 0.067 s
% 0.21/0.47  % (3820)------------------------------
% 0.21/0.47  % (3820)------------------------------
% 0.21/0.47  % (3813)Success in time 0.117 s
%------------------------------------------------------------------------------
