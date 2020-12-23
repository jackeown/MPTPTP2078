%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 260 expanded)
%              Number of leaves         :   17 ( 101 expanded)
%              Depth                    :   10
%              Number of atoms          :  405 (1467 expanded)
%              Number of equality atoms :   36 ( 174 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f345,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f114,f115,f118,f121,f123,f174,f186,f187,f214,f260,f299,f302,f341,f344])).

fof(f344,plain,
    ( spl7_10
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f337,f257,f167])).

fof(f167,plain,
    ( spl7_10
  <=> r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f257,plain,
    ( spl7_16
  <=> r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f337,plain,
    ( r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK1)
    | ~ spl7_16 ),
    inference(resolution,[],[f258,f40])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f258,plain,
    ( r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK1))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f257])).

fof(f341,plain,
    ( spl7_8
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | spl7_8
    | ~ spl7_16 ),
    inference(resolution,[],[f258,f125])).

fof(f125,plain,
    ( ! [X0] : ~ r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,X0))
    | spl7_8 ),
    inference(resolution,[],[f107,f41])).

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

fof(f107,plain,
    ( ~ r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK0)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl7_8
  <=> r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f302,plain,
    ( ~ spl7_1
    | ~ spl7_6
    | spl7_16
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f208,f102,f257,f98,f75])).

fof(f75,plain,
    ( spl7_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f98,plain,
    ( spl7_6
  <=> v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f102,plain,
    ( spl7_7
  <=> r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f208,plain,
    ( r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl7_7 ),
    inference(resolution,[],[f104,f38])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK4(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)
                    & r2_hidden(sK4(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(f104,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f299,plain,
    ( ~ spl7_8
    | ~ spl7_10
    | spl7_16 ),
    inference(avatar_split_clause,[],[f295,f257,f167,f106])).

fof(f295,plain,
    ( ~ r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK1)
    | ~ r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK0)
    | spl7_16 ),
    inference(resolution,[],[f259,f39])).

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

fof(f259,plain,
    ( ~ r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK1))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f257])).

fof(f260,plain,
    ( ~ spl7_1
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_11
    | spl7_7 ),
    inference(avatar_split_clause,[],[f251,f102,f171,f257,f98,f75])).

fof(f171,plain,
    ( spl7_11
  <=> r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f251,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),sK2)
    | ~ r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(sK2)
    | spl7_7 ),
    inference(resolution,[],[f103,f36])).

fof(f36,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f103,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f214,plain,
    ( ~ spl7_1
    | ~ spl7_6
    | spl7_11
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f209,f102,f171,f98,f75])).

fof(f209,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),sK2)
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl7_7 ),
    inference(resolution,[],[f104,f37])).

fof(f37,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f187,plain,
    ( ~ spl7_1
    | ~ spl7_5
    | spl7_11
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f181,f111,f171,f94,f75])).

fof(f94,plain,
    ( spl7_5
  <=> v1_relat_1(k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f111,plain,
    ( spl7_9
  <=> r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f181,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),sK2)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl7_9 ),
    inference(resolution,[],[f113,f37])).

fof(f113,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(sK1,sK2))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f186,plain,
    ( ~ spl7_1
    | ~ spl7_5
    | spl7_10
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f180,f111,f167,f94,f75])).

fof(f180,plain,
    ( r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK1)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl7_9 ),
    inference(resolution,[],[f113,f38])).

fof(f174,plain,
    ( ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_11
    | spl7_9 ),
    inference(avatar_split_clause,[],[f161,f111,f171,f167,f94,f75])).

fof(f161,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),sK2)
    | ~ r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK1)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | spl7_9 ),
    inference(resolution,[],[f112,f36])).

fof(f112,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(sK1,sK2))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f123,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl7_1 ),
    inference(resolution,[],[f77,f21])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(k3_xboole_0(sK0,sK1),sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(k3_xboole_0(X0,X1),X2)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(k3_xboole_0(sK0,sK1),sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(k3_xboole_0(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

fof(f77,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f121,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl7_6 ),
    inference(resolution,[],[f100,f51])).

fof(f51,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK2)) ),
    inference(resolution,[],[f21,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f100,plain,
    ( ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f118,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl7_5 ),
    inference(resolution,[],[f96,f51])).

fof(f96,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f115,plain,
    ( ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f92,f111,f106,f102,f98,f94])).

fof(f92,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(sK1,sK2))
    | ~ r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK0)
    | ~ r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f43,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k8_relat_1(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f29,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ~ sQ6_eqProxy(k8_relat_1(sK0,k8_relat_1(sK1,sK2)),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(equality_proxy_replacement,[],[f22,f42])).

fof(f22,plain,(
    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(k3_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f114,plain,
    ( ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | spl7_9 ),
    inference(avatar_split_clause,[],[f91,f111,f102,f98,f94])).

fof(f91,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(sK1,sK2))
    | r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f43,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k8_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f28,f42])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f109,plain,
    ( ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f90,f106,f102,f98,f94])).

fof(f90,plain,
    ( r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK0)
    | r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f43,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k8_relat_1(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f27,f42])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (6060)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (6068)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (6054)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (6054)Refutation not found, incomplete strategy% (6054)------------------------------
% 0.20/0.48  % (6054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (6054)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (6054)Memory used [KB]: 10490
% 0.20/0.48  % (6054)Time elapsed: 0.061 s
% 0.20/0.48  % (6054)------------------------------
% 0.20/0.48  % (6054)------------------------------
% 0.20/0.49  % (6064)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (6061)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (6055)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (6067)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (6066)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (6056)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (6071)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (6070)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (6058)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (6056)Refutation not found, incomplete strategy% (6056)------------------------------
% 0.20/0.50  % (6056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (6056)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (6056)Memory used [KB]: 10618
% 0.20/0.50  % (6056)Time elapsed: 0.083 s
% 0.20/0.50  % (6056)------------------------------
% 0.20/0.50  % (6056)------------------------------
% 0.20/0.50  % (6063)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (6069)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  % (6053)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (6057)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (6072)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (6065)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (6073)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.52  % (6073)Refutation not found, incomplete strategy% (6073)------------------------------
% 0.20/0.52  % (6073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (6073)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (6073)Memory used [KB]: 10490
% 0.20/0.52  % (6073)Time elapsed: 0.105 s
% 0.20/0.52  % (6073)------------------------------
% 0.20/0.52  % (6073)------------------------------
% 0.20/0.52  % (6059)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.52  % (6062)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.52  % (6065)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f345,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f109,f114,f115,f118,f121,f123,f174,f186,f187,f214,f260,f299,f302,f341,f344])).
% 0.20/0.53  fof(f344,plain,(
% 0.20/0.53    spl7_10 | ~spl7_16),
% 0.20/0.53    inference(avatar_split_clause,[],[f337,f257,f167])).
% 0.20/0.53  fof(f167,plain,(
% 0.20/0.53    spl7_10 <=> r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.53  fof(f257,plain,(
% 0.20/0.53    spl7_16 <=> r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.20/0.53  fof(f337,plain,(
% 0.20/0.53    r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK1) | ~spl7_16),
% 0.20/0.53    inference(resolution,[],[f258,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.20/0.53    inference(rectify,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.20/0.53    inference(flattening,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.20/0.53  fof(f258,plain,(
% 0.20/0.53    r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK1)) | ~spl7_16),
% 0.20/0.53    inference(avatar_component_clause,[],[f257])).
% 0.20/0.53  fof(f341,plain,(
% 0.20/0.53    spl7_8 | ~spl7_16),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f335])).
% 0.20/0.53  fof(f335,plain,(
% 0.20/0.53    $false | (spl7_8 | ~spl7_16)),
% 0.20/0.53    inference(resolution,[],[f258,f125])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,X0))) ) | spl7_8),
% 0.20/0.53    inference(resolution,[],[f107,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    ~r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK0) | spl7_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f106])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    spl7_8 <=> r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.53  fof(f302,plain,(
% 0.20/0.53    ~spl7_1 | ~spl7_6 | spl7_16 | ~spl7_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f208,f102,f257,f98,f75])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    spl7_1 <=> v1_relat_1(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    spl7_6 <=> v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    spl7_7 <=> r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.53  fof(f208,plain,(
% 0.20/0.53    r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK1)) | ~v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) | ~v1_relat_1(sK2) | ~spl7_7),
% 0.20/0.53    inference(resolution,[],[f104,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X6,X0,X5,X1] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f13,f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(rectify,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0))) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) | ~spl7_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f102])).
% 0.20/0.53  fof(f299,plain,(
% 0.20/0.53    ~spl7_8 | ~spl7_10 | spl7_16),
% 0.20/0.53    inference(avatar_split_clause,[],[f295,f257,f167,f106])).
% 0.20/0.53  fof(f295,plain,(
% 0.20/0.53    ~r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK1) | ~r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK0) | spl7_16),
% 0.20/0.53    inference(resolution,[],[f259,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f259,plain,(
% 0.20/0.53    ~r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK1)) | spl7_16),
% 0.20/0.53    inference(avatar_component_clause,[],[f257])).
% 0.20/0.53  fof(f260,plain,(
% 0.20/0.53    ~spl7_1 | ~spl7_6 | ~spl7_16 | ~spl7_11 | spl7_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f251,f102,f171,f257,f98,f75])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    spl7_11 <=> r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.53  fof(f251,plain,(
% 0.20/0.53    ~r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),sK2) | ~r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK1)) | ~v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) | ~v1_relat_1(sK2) | spl7_7),
% 0.20/0.53    inference(resolution,[],[f103,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    ~r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) | spl7_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f102])).
% 0.20/0.53  fof(f214,plain,(
% 0.20/0.53    ~spl7_1 | ~spl7_6 | spl7_11 | ~spl7_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f209,f102,f171,f98,f75])).
% 0.20/0.53  fof(f209,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),sK2) | ~v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) | ~v1_relat_1(sK2) | ~spl7_7),
% 0.20/0.53    inference(resolution,[],[f104,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f187,plain,(
% 0.20/0.53    ~spl7_1 | ~spl7_5 | spl7_11 | ~spl7_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f181,f111,f171,f94,f75])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    spl7_5 <=> v1_relat_1(k8_relat_1(sK1,sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    spl7_9 <=> r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(sK1,sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.53  fof(f181,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),sK2) | ~v1_relat_1(k8_relat_1(sK1,sK2)) | ~v1_relat_1(sK2) | ~spl7_9),
% 0.20/0.53    inference(resolution,[],[f113,f37])).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(sK1,sK2)) | ~spl7_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f111])).
% 0.20/0.53  fof(f186,plain,(
% 0.20/0.53    ~spl7_1 | ~spl7_5 | spl7_10 | ~spl7_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f180,f111,f167,f94,f75])).
% 0.20/0.53  fof(f180,plain,(
% 0.20/0.53    r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK1) | ~v1_relat_1(k8_relat_1(sK1,sK2)) | ~v1_relat_1(sK2) | ~spl7_9),
% 0.20/0.53    inference(resolution,[],[f113,f38])).
% 0.20/0.53  fof(f174,plain,(
% 0.20/0.53    ~spl7_1 | ~spl7_5 | ~spl7_10 | ~spl7_11 | spl7_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f161,f111,f171,f167,f94,f75])).
% 0.20/0.53  fof(f161,plain,(
% 0.20/0.53    ~r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),sK2) | ~r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK1) | ~v1_relat_1(k8_relat_1(sK1,sK2)) | ~v1_relat_1(sK2) | spl7_9),
% 0.20/0.53    inference(resolution,[],[f112,f36])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    ~r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(sK1,sK2)) | spl7_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f111])).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    spl7_1),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f122])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    $false | spl7_1),
% 0.20/0.53    inference(resolution,[],[f77,f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    v1_relat_1(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(k3_xboole_0(sK0,sK1),sK2) & v1_relat_1(sK2)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).
% 0.20/0.53  fof(f9,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(k3_xboole_0(X0,X1),X2) & v1_relat_1(X2)) => (k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(k3_xboole_0(sK0,sK1),sK2) & v1_relat_1(sK2))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f6,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(k3_xboole_0(X0,X1),X2) & v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 0.20/0.53    inference(negated_conjecture,[],[f4])).
% 0.20/0.53  fof(f4,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ~v1_relat_1(sK2) | spl7_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f75])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    spl7_6),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f119])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    $false | spl7_6),
% 0.20/0.53    inference(resolution,[],[f100,f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK2))) )),
% 0.20/0.53    inference(resolution,[],[f21,f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,plain,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    ~v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) | spl7_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f98])).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    spl7_5),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f116])).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    $false | spl7_5),
% 0.20/0.54    inference(resolution,[],[f96,f51])).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    ~v1_relat_1(k8_relat_1(sK1,sK2)) | spl7_5),
% 0.20/0.54    inference(avatar_component_clause,[],[f94])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9),
% 0.20/0.54    inference(avatar_split_clause,[],[f92,f111,f106,f102,f98,f94])).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    ~r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(sK1,sK2)) | ~r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK0) | ~r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) | ~v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) | ~v1_relat_1(k8_relat_1(sK1,sK2))),
% 0.20/0.54    inference(resolution,[],[f43,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (sQ6_eqProxy(k8_relat_1(X0,X1),X2) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(equality_proxy_replacement,[],[f29,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ! [X1,X0] : (sQ6_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.54    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k8_relat_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ~sQ6_eqProxy(k8_relat_1(sK0,k8_relat_1(sK1,sK2)),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),
% 0.20/0.54    inference(equality_proxy_replacement,[],[f22,f42])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f10])).
% 0.20/0.54  fof(f114,plain,(
% 0.20/0.54    ~spl7_5 | ~spl7_6 | spl7_7 | spl7_9),
% 0.20/0.54    inference(avatar_split_clause,[],[f91,f111,f102,f98,f94])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(sK1,sK2)) | r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) | ~v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) | ~v1_relat_1(k8_relat_1(sK1,sK2))),
% 0.20/0.54    inference(resolution,[],[f43,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (sQ6_eqProxy(k8_relat_1(X0,X1),X2) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(equality_proxy_replacement,[],[f28,f42])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k8_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    ~spl7_5 | ~spl7_6 | spl7_7 | spl7_8),
% 0.20/0.54    inference(avatar_split_clause,[],[f90,f106,f102,f98,f94])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK0) | r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))),k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) | ~v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) | ~v1_relat_1(k8_relat_1(sK1,sK2))),
% 0.20/0.54    inference(resolution,[],[f43,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (sQ6_eqProxy(k8_relat_1(X0,X1),X2) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(equality_proxy_replacement,[],[f27,f42])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k8_relat_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (6065)------------------------------
% 0.20/0.54  % (6065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6065)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (6065)Memory used [KB]: 6268
% 0.20/0.54  % (6065)Time elapsed: 0.115 s
% 0.20/0.54  % (6065)------------------------------
% 0.20/0.54  % (6065)------------------------------
% 0.20/0.54  % (6052)Success in time 0.181 s
%------------------------------------------------------------------------------
