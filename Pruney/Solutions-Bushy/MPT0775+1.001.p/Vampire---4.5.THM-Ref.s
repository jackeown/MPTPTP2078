%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0775+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 282 expanded)
%              Number of leaves         :   22 ( 102 expanded)
%              Depth                    :   13
%              Number of atoms          :  397 (1270 expanded)
%              Number of equality atoms :   16 (  98 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f216,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f55,f59,f67,f70,f75,f86,f90,f100,f106,f124,f166,f178,f204])).

fof(f204,plain,
    ( ~ spl6_10
    | ~ spl6_3
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f199,f176,f121,f104,f57,f98])).

fof(f98,plain,
    ( spl6_10
  <=> r2_hidden(sK2(k2_wellord1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f57,plain,
    ( spl6_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f104,plain,
    ( spl6_11
  <=> r2_hidden(sK4(k2_wellord1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f121,plain,
    ( spl6_12
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f176,plain,
    ( spl6_14
  <=> r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f199,plain,
    ( ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),sK0)
    | ~ spl6_3
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(resolution,[],[f195,f105])).

fof(f105,plain,
    ( r2_hidden(sK4(k2_wellord1(sK1,sK0)),sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k2_wellord1(sK1,sK0)),X0)
        | ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),X0) )
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(resolution,[],[f194,f122])).

fof(f122,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,X0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f194,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,X0))
        | ~ r2_hidden(sK4(k2_wellord1(sK1,sK0)),X0)
        | ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),X0) )
    | ~ spl6_3
    | ~ spl6_14 ),
    inference(resolution,[],[f181,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f181,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),k2_zfmisc_1(X3,X3))
        | r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,X3)) )
    | ~ spl6_3
    | ~ spl6_14 ),
    inference(resolution,[],[f177,f110])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,k2_zfmisc_1(X0,X0))
        | r2_hidden(X1,k2_wellord1(sK1,X0)) )
    | ~ spl6_3 ),
    inference(superposition,[],[f45,f76])).

fof(f76,plain,
    ( ! [X0] : k2_wellord1(sK1,X0) = k3_xboole_0(sK1,k2_zfmisc_1(X0,X0))
    | ~ spl6_3 ),
    inference(resolution,[],[f34,f58])).

fof(f58,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f177,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),sK1)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f176])).

fof(f178,plain,
    ( spl6_14
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f173,f164,f73,f65,f57,f176])).

fof(f65,plain,
    ( spl6_5
  <=> r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f73,plain,
    ( spl6_6
  <=> r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f164,plain,
    ( spl6_13
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(k4_tarski(X2,X1),sK1)
        | ~ r2_hidden(k4_tarski(X2,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f173,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),sK1)
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13 ),
    inference(resolution,[],[f170,f66])).

fof(f66,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f170,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,sK3(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,X3))
        | r2_hidden(k4_tarski(X2,sK4(k2_wellord1(sK1,sK0))),sK1) )
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_13 ),
    inference(resolution,[],[f168,f74])).

fof(f74,plain,
    ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f168,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X2,X1),k2_wellord1(sK1,X3))
        | r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(k4_tarski(X0,X2),k2_wellord1(sK1,X4)) )
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(resolution,[],[f167,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,k2_wellord1(sK1,X0)) )
    | ~ spl6_3 ),
    inference(superposition,[],[f47,f76])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f167,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X2),sK1)
        | r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(k4_tarski(X2,X1),k2_wellord1(sK1,X3)) )
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(resolution,[],[f165,f78])).

fof(f165,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(k4_tarski(X2,X1),sK1)
        | ~ r2_hidden(k4_tarski(X2,X0),sK1) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f164])).

fof(f166,plain,
    ( ~ spl6_2
    | spl6_13
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f160,f57,f164,f53])).

fof(f53,plain,
    ( spl6_2
  <=> v8_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f160,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(k4_tarski(X2,X0),sK1)
        | ~ v8_relat_2(sK1)
        | r2_hidden(k4_tarski(X2,X1),sK1) )
    | ~ spl6_3 ),
    inference(resolution,[],[f30,f58])).

fof(f30,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ v8_relat_2(X0)
      | r2_hidden(k4_tarski(X4,X6),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0)
            & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
            & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0)
        & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
        & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2,X3] :
              ( r2_hidden(k4_tarski(X1,X3),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).

fof(f124,plain,
    ( ~ spl6_4
    | ~ spl6_11
    | spl6_12
    | ~ spl6_10
    | spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f118,f57,f49,f98,f121,f104,f62])).

fof(f62,plain,
    ( spl6_4
  <=> v1_relat_1(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f49,plain,
    ( spl6_1
  <=> v8_relat_2(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),sK0)
        | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,X0))
        | ~ r2_hidden(sK4(k2_wellord1(sK1,sK0)),sK0)
        | ~ v1_relat_1(k2_wellord1(sK1,sK0)) )
    | spl6_1
    | ~ spl6_3 ),
    inference(resolution,[],[f116,f50])).

fof(f50,plain,
    ( ~ v8_relat_2(k2_wellord1(sK1,sK0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f116,plain,
    ( ! [X8,X9] :
        ( v8_relat_2(k2_wellord1(sK1,X8))
        | ~ r2_hidden(sK2(k2_wellord1(sK1,X8)),X8)
        | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,X8)),sK4(k2_wellord1(sK1,X8))),k2_wellord1(sK1,X9))
        | ~ r2_hidden(sK4(k2_wellord1(sK1,X8)),X8)
        | ~ v1_relat_1(k2_wellord1(sK1,X8)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f44,f113])).

fof(f113,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,X3)),sK4(k2_wellord1(sK1,X3))),k2_zfmisc_1(X3,X3))
        | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,X3)),sK4(k2_wellord1(sK1,X3))),k2_wellord1(sK1,X4))
        | v8_relat_2(k2_wellord1(sK1,X3))
        | ~ v1_relat_1(k2_wellord1(sK1,X3)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f111,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0)
      | v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f111,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,k2_wellord1(sK1,X1))
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X1))
        | ~ r2_hidden(X0,k2_wellord1(sK1,X2)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f110,f78])).

fof(f106,plain,
    ( spl6_11
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f101,f88,f104])).

fof(f88,plain,
    ( spl6_8
  <=> r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f101,plain,
    ( r2_hidden(sK4(k2_wellord1(sK1,sK0)),sK0)
    | ~ spl6_8 ),
    inference(resolution,[],[f89,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f89,plain,
    ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),k2_zfmisc_1(sK0,sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f100,plain,
    ( spl6_10
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f92,f84,f98])).

fof(f84,plain,
    ( spl6_7
  <=> r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f92,plain,
    ( r2_hidden(sK2(k2_wellord1(sK1,sK0)),sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f85,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_zfmisc_1(sK0,sK0))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f90,plain,
    ( spl6_8
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f82,f73,f57,f88])).

fof(f82,plain,
    ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),k2_zfmisc_1(sK0,sK0))
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(resolution,[],[f79,f74])).

fof(f79,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k2_wellord1(sK1,X2))
        | r2_hidden(X3,k2_zfmisc_1(X2,X2)) )
    | ~ spl6_3 ),
    inference(superposition,[],[f46,f76])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,
    ( spl6_7
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f81,f65,f57,f84])).

fof(f81,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_zfmisc_1(sK0,sK0))
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(resolution,[],[f79,f66])).

fof(f75,plain,
    ( ~ spl6_4
    | spl6_6
    | spl6_1 ),
    inference(avatar_split_clause,[],[f71,f49,f73,f62])).

fof(f71,plain,
    ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))
    | ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | spl6_1 ),
    inference(resolution,[],[f32,f50])).

fof(f32,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,
    ( ~ spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f68,f62,f57])).

fof(f68,plain,
    ( ~ v1_relat_1(sK1)
    | spl6_4 ),
    inference(resolution,[],[f63,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f63,plain,
    ( ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f67,plain,
    ( ~ spl6_4
    | spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f60,f49,f65,f62])).

fof(f60,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))
    | ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | spl6_1 ),
    inference(resolution,[],[f31,f50])).

fof(f31,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ v8_relat_2(k2_wellord1(sK1,sK0))
    & v8_relat_2(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ~ v8_relat_2(k2_wellord1(X1,X0))
        & v8_relat_2(X1)
        & v1_relat_1(X1) )
   => ( ~ v8_relat_2(k2_wellord1(sK1,sK0))
      & v8_relat_2(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ v8_relat_2(k2_wellord1(X1,X0))
      & v8_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ v8_relat_2(k2_wellord1(X1,X0))
      & v8_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v8_relat_2(X1)
         => v8_relat_2(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
       => v8_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_wellord1)).

fof(f55,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f28,f53])).

fof(f28,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f29,f49])).

fof(f29,plain,(
    ~ v8_relat_2(k2_wellord1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f15])).

%------------------------------------------------------------------------------
