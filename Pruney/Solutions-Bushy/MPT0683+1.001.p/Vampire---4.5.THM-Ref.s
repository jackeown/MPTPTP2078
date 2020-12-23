%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0683+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 324 expanded)
%              Number of leaves         :   18 ( 115 expanded)
%              Depth                    :   11
%              Number of atoms          :  437 (1951 expanded)
%              Number of equality atoms :   38 ( 246 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f344,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f99,f105,f107,f116,f121,f122,f252,f263,f266,f272,f277,f309,f330,f341,f343])).

fof(f343,plain,
    ( spl6_17
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f194,f109,f269])).

fof(f269,plain,
    ( spl6_17
  <=> r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f109,plain,
    ( spl6_9
  <=> r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f194,plain,
    ( r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_9 ),
    inference(resolution,[],[f111,f40])).

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).

fof(f19,plain,(
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

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f111,plain,
    ( r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f341,plain,
    ( ~ spl6_8
    | ~ spl6_1
    | ~ spl6_17
    | spl6_20 ),
    inference(avatar_split_clause,[],[f338,f327,f269,f58,f92])).

fof(f92,plain,
    ( spl6_8
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f58,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f327,plain,
    ( spl6_20
  <=> r2_hidden(k1_funct_1(sK2,sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f338,plain,
    ( ~ r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl6_20 ),
    inference(resolution,[],[f329,f37])).

fof(f37,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

% (6147)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
                | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
                  & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(f329,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | spl6_20 ),
    inference(avatar_component_clause,[],[f327])).

fof(f330,plain,
    ( ~ spl6_16
    | ~ spl6_20
    | spl6_11 ),
    inference(avatar_split_clause,[],[f322,f118,f327,f260])).

fof(f260,plain,
    ( spl6_16
  <=> r2_hidden(k1_funct_1(sK2,sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f118,plain,
    ( spl6_11
  <=> r2_hidden(k1_funct_1(sK2,sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f322,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ r2_hidden(k1_funct_1(sK2,sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | spl6_11 ),
    inference(resolution,[],[f119,f39])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f119,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k3_xboole_0(sK0,sK1))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f309,plain,
    ( ~ spl6_18
    | ~ spl6_17
    | spl6_9 ),
    inference(avatar_split_clause,[],[f306,f109,f269,f274])).

fof(f274,plain,
    ( spl6_18
  <=> r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f306,plain,
    ( ~ r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | spl6_9 ),
    inference(resolution,[],[f110,f39])).

fof(f110,plain,
    ( ~ r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f277,plain,
    ( ~ spl6_8
    | ~ spl6_1
    | ~ spl6_10
    | spl6_18
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f240,f118,f274,f113,f58,f92])).

fof(f113,plain,
    ( spl6_10
  <=> r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f240,plain,
    ( r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_11 ),
    inference(resolution,[],[f177,f36])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f177,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl6_11 ),
    inference(resolution,[],[f120,f41])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f120,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k3_xboole_0(sK0,sK1))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f272,plain,
    ( ~ spl6_8
    | ~ spl6_1
    | ~ spl6_10
    | spl6_17
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f243,f118,f269,f113,f58,f92])).

fof(f243,plain,
    ( r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_11 ),
    inference(resolution,[],[f178,f36])).

fof(f178,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ spl6_11 ),
    inference(resolution,[],[f120,f40])).

fof(f266,plain,
    ( spl6_11
    | spl6_9
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f189,f78,f109,f118])).

fof(f78,plain,
    ( spl6_6
  <=> ! [X9,X8] :
        ( sQ5_eqProxy(k10_relat_1(sK2,X8),X9)
        | r2_hidden(sK3(sK2,X8,X9),X9)
        | r2_hidden(k1_funct_1(sK2,sK3(sK2,X8,X9)),X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f189,plain,
    ( r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | r2_hidden(k1_funct_1(sK2,sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k3_xboole_0(sK0,sK1))
    | ~ spl6_6 ),
    inference(resolution,[],[f79,f43])).

fof(f43,plain,(
    ~ sQ5_eqProxy(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    inference(equality_proxy_replacement,[],[f23,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f23,plain,(
    k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( k10_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

fof(f79,plain,
    ( ! [X8,X9] :
        ( sQ5_eqProxy(k10_relat_1(sK2,X8),X9)
        | r2_hidden(sK3(sK2,X8,X9),X9)
        | r2_hidden(k1_funct_1(sK2,sK3(sK2,X8,X9)),X8) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f263,plain,
    ( ~ spl6_8
    | ~ spl6_1
    | spl6_16
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f249,f109,f260,f58,f92])).

fof(f249,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_9 ),
    inference(resolution,[],[f193,f37])).

fof(f193,plain,
    ( r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_9 ),
    inference(resolution,[],[f111,f41])).

fof(f252,plain,
    ( ~ spl6_2
    | ~ spl6_9
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_9
    | spl6_10 ),
    inference(resolution,[],[f193,f170])).

fof(f170,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,X0))
    | ~ spl6_2
    | spl6_10 ),
    inference(resolution,[],[f114,f63])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k10_relat_1(sK2,X1)) )
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_2
  <=> ! [X1,X0] :
        ( r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k10_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f114,plain,
    ( ~ r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f122,plain,
    ( ~ spl6_8
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f103,f118,f113,f109,f58,f92])).

fof(f103,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f43,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k10_relat_1(X0,X1),X2)
      | ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f29,f42])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f121,plain,
    ( ~ spl6_8
    | ~ spl6_1
    | spl6_9
    | spl6_11 ),
    inference(avatar_split_clause,[],[f102,f118,f109,f58,f92])).

fof(f102,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f43,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k10_relat_1(X0,X1),X2)
      | r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f28,f42])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f116,plain,
    ( ~ spl6_8
    | ~ spl6_1
    | spl6_9
    | spl6_10 ),
    inference(avatar_split_clause,[],[f101,f113,f109,f58,f92])).

fof(f101,plain,
    ( r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | r2_hidden(sK3(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f43,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k10_relat_1(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f27,f42])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f107,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | spl6_8 ),
    inference(resolution,[],[f94,f21])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f94,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f105,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl6_1 ),
    inference(resolution,[],[f60,f22])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f99,plain,
    ( ~ spl6_8
    | spl6_6 ),
    inference(avatar_split_clause,[],[f89,f78,f92])).

fof(f89,plain,(
    ! [X8,X9] :
      ( sQ5_eqProxy(k10_relat_1(sK2,X8),X9)
      | r2_hidden(k1_funct_1(sK2,sK3(sK2,X8,X9)),X8)
      | r2_hidden(sK3(sK2,X8,X9),X9)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f22,f45])).

fof(f95,plain,
    ( ~ spl6_8
    | spl6_2 ),
    inference(avatar_split_clause,[],[f85,f62,f92])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(sK2))
      | ~ r2_hidden(X0,k10_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f22,f38])).

fof(f38,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

%------------------------------------------------------------------------------
