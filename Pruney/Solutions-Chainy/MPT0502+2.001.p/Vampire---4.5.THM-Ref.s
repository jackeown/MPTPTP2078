%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:33 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
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
    inference(avatar_split_clause,[],[f336,f257,f167])).

fof(f167,plain,
    ( spl7_10
  <=> r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f257,plain,
    ( spl7_16
  <=> r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f336,plain,
    ( r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl7_16 ),
    inference(resolution,[],[f258,f41])).

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
    ( r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
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
    inference(resolution,[],[f258,f126])).

fof(f126,plain,
    ( ! [X1] : ~ r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(X1,sK1))
    | spl7_8 ),
    inference(resolution,[],[f107,f40])).

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

fof(f107,plain,
    ( ~ r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK1)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl7_8
  <=> r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK1) ),
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
  <=> v1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f102,plain,
    ( spl7_7
  <=> r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f208,plain,
    ( r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | ~ spl7_7 ),
    inference(resolution,[],[f104,f38])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK3(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                    & r2_hidden(sK3(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
            & r2_hidden(sK3(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f104,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f299,plain,
    ( ~ spl7_10
    | ~ spl7_8
    | spl7_16 ),
    inference(avatar_split_clause,[],[f295,f257,f106,f167])).

fof(f295,plain,
    ( ~ r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK1)
    | ~ r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK0)
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
    ( ~ r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
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
  <=> r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f251,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),sK2)
    | ~ r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | spl7_7 ),
    inference(resolution,[],[f103,f36])).

fof(f36,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f103,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f214,plain,
    ( ~ spl7_1
    | ~ spl7_6
    | spl7_11
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f209,f102,f171,f98,f75])).

fof(f209,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | ~ spl7_7 ),
    inference(resolution,[],[f104,f37])).

fof(f37,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f187,plain,
    ( ~ spl7_1
    | ~ spl7_5
    | spl7_11
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f181,f111,f171,f94,f75])).

fof(f94,plain,
    ( spl7_5
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f111,plain,
    ( spl7_9
  <=> r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f181,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl7_9 ),
    inference(resolution,[],[f113,f37])).

fof(f113,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,sK0))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f186,plain,
    ( ~ spl7_1
    | ~ spl7_5
    | spl7_10
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f180,f111,f167,f94,f75])).

fof(f180,plain,
    ( r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK0)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
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
    ( ~ r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),sK2)
    | ~ r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK0)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | spl7_9 ),
    inference(resolution,[],[f112,f36])).

fof(f112,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,sK0))
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
    ( k7_relat_1(k7_relat_1(sK2,sK0),sK1) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) != k7_relat_1(X2,k3_xboole_0(X0,X1))
        & v1_relat_1(X2) )
   => ( k7_relat_1(k7_relat_1(sK2,sK0),sK1) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) != k7_relat_1(X2,k3_xboole_0(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

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
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f21,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f100,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))
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
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
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
    ( ~ r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,sK0))
    | ~ r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK1)
    | ~ r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f43,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k7_relat_1(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f28,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ~ sQ6_eqProxy(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    inference(equality_proxy_replacement,[],[f22,f42])).

fof(f22,plain,(
    k7_relat_1(k7_relat_1(sK2,sK0),sK1) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f114,plain,
    ( ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | spl7_9 ),
    inference(avatar_split_clause,[],[f91,f111,f102,f98,f94])).

fof(f91,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,sK0))
    | r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f43,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k7_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f27,f42])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f109,plain,
    ( ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f90,f106,f102,f98,f94])).

fof(f90,plain,
    ( r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK1)
    | r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f43,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k7_relat_1(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f26,f42])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:50:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (31670)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (31675)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (31685)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.52  % (31668)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (31668)Refutation not found, incomplete strategy% (31668)------------------------------
% 0.22/0.52  % (31668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (31668)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (31668)Memory used [KB]: 10490
% 0.22/0.52  % (31668)Time elapsed: 0.093 s
% 0.22/0.52  % (31668)------------------------------
% 0.22/0.52  % (31668)------------------------------
% 0.22/0.52  % (31678)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.53  % (31673)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.53  % (31672)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (31677)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.53  % (31671)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.53  % (31686)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.54  % (31667)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (31669)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.55  % (31682)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.55  % (31676)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.44/0.56  % (31674)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.44/0.56  % (31687)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.44/0.56  % (31687)Refutation not found, incomplete strategy% (31687)------------------------------
% 1.44/0.56  % (31687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (31687)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (31687)Memory used [KB]: 10490
% 1.44/0.56  % (31687)Time elapsed: 0.129 s
% 1.44/0.56  % (31687)------------------------------
% 1.44/0.56  % (31687)------------------------------
% 1.44/0.56  % (31683)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.44/0.56  % (31680)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.44/0.57  % (31679)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.64/0.57  % (31684)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.64/0.57  % (31681)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 1.64/0.59  % (31679)Refutation found. Thanks to Tanya!
% 1.64/0.59  % SZS status Theorem for theBenchmark
% 1.64/0.59  % SZS output start Proof for theBenchmark
% 1.64/0.59  fof(f345,plain,(
% 1.64/0.59    $false),
% 1.64/0.59    inference(avatar_sat_refutation,[],[f109,f114,f115,f118,f121,f123,f174,f186,f187,f214,f260,f299,f302,f341,f344])).
% 1.64/0.59  fof(f344,plain,(
% 1.64/0.59    spl7_10 | ~spl7_16),
% 1.64/0.59    inference(avatar_split_clause,[],[f336,f257,f167])).
% 1.64/0.59  fof(f167,plain,(
% 1.64/0.59    spl7_10 <=> r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.64/0.59  fof(f257,plain,(
% 1.64/0.59    spl7_16 <=> r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.64/0.59  fof(f336,plain,(
% 1.64/0.59    r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK0) | ~spl7_16),
% 1.64/0.59    inference(resolution,[],[f258,f41])).
% 1.64/0.59  fof(f41,plain,(
% 1.64/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 1.64/0.59    inference(equality_resolution,[],[f30])).
% 1.64/0.59  fof(f30,plain,(
% 1.64/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.64/0.59    inference(cnf_transformation,[],[f20])).
% 1.64/0.59  fof(f20,plain,(
% 1.64/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.64/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f19])).
% 1.64/0.59  fof(f19,plain,(
% 1.64/0.59    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.64/0.59    introduced(choice_axiom,[])).
% 1.64/0.59  fof(f18,plain,(
% 1.64/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.64/0.59    inference(rectify,[],[f17])).
% 1.64/0.59  fof(f17,plain,(
% 1.64/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.64/0.59    inference(flattening,[],[f16])).
% 1.64/0.59  fof(f16,plain,(
% 1.64/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.64/0.59    inference(nnf_transformation,[],[f1])).
% 1.64/0.59  fof(f1,axiom,(
% 1.64/0.59    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.64/0.59  fof(f258,plain,(
% 1.64/0.59    r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) | ~spl7_16),
% 1.64/0.59    inference(avatar_component_clause,[],[f257])).
% 1.64/0.59  fof(f341,plain,(
% 1.64/0.59    spl7_8 | ~spl7_16),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f335])).
% 1.64/0.59  fof(f335,plain,(
% 1.64/0.59    $false | (spl7_8 | ~spl7_16)),
% 1.64/0.59    inference(resolution,[],[f258,f126])).
% 1.64/0.59  fof(f126,plain,(
% 1.64/0.59    ( ! [X1] : (~r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(X1,sK1))) ) | spl7_8),
% 1.64/0.59    inference(resolution,[],[f107,f40])).
% 1.64/0.59  fof(f40,plain,(
% 1.64/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 1.64/0.59    inference(equality_resolution,[],[f31])).
% 1.64/0.59  fof(f31,plain,(
% 1.64/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.64/0.59    inference(cnf_transformation,[],[f20])).
% 1.64/0.59  fof(f107,plain,(
% 1.64/0.59    ~r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK1) | spl7_8),
% 1.64/0.59    inference(avatar_component_clause,[],[f106])).
% 1.64/0.59  fof(f106,plain,(
% 1.64/0.59    spl7_8 <=> r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK1)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.64/0.59  fof(f302,plain,(
% 1.64/0.59    ~spl7_1 | ~spl7_6 | spl7_16 | ~spl7_7),
% 1.64/0.59    inference(avatar_split_clause,[],[f208,f102,f257,f98,f75])).
% 1.64/0.59  fof(f75,plain,(
% 1.64/0.59    spl7_1 <=> v1_relat_1(sK2)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.64/0.59  fof(f98,plain,(
% 1.64/0.59    spl7_6 <=> v1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.64/0.59  fof(f102,plain,(
% 1.64/0.59    spl7_7 <=> r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.64/0.59  fof(f208,plain,(
% 1.64/0.59    r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) | ~v1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) | ~v1_relat_1(sK2) | ~spl7_7),
% 1.64/0.59    inference(resolution,[],[f104,f38])).
% 1.64/0.59  fof(f38,plain,(
% 1.64/0.59    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.64/0.59    inference(equality_resolution,[],[f23])).
% 1.64/0.59  fof(f23,plain,(
% 1.64/0.59    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f15])).
% 1.64/0.59  fof(f15,plain,(
% 1.64/0.59    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 1.64/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f13,f14])).
% 1.64/0.59  fof(f14,plain,(
% 1.64/0.59    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 1.64/0.59    introduced(choice_axiom,[])).
% 1.64/0.59  fof(f13,plain,(
% 1.64/0.59    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 1.64/0.59    inference(rectify,[],[f12])).
% 1.64/0.59  fof(f12,plain,(
% 1.64/0.59    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 1.64/0.59    inference(flattening,[],[f11])).
% 1.64/0.59  fof(f11,plain,(
% 1.64/0.59    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 1.64/0.59    inference(nnf_transformation,[],[f7])).
% 1.64/0.59  fof(f7,plain,(
% 1.64/0.59    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 1.64/0.59    inference(ennf_transformation,[],[f2])).
% 1.64/0.59  fof(f2,axiom,(
% 1.64/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).
% 1.64/0.59  fof(f104,plain,(
% 1.64/0.59    r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) | ~spl7_7),
% 1.64/0.59    inference(avatar_component_clause,[],[f102])).
% 1.64/0.59  fof(f299,plain,(
% 1.64/0.59    ~spl7_10 | ~spl7_8 | spl7_16),
% 1.64/0.59    inference(avatar_split_clause,[],[f295,f257,f106,f167])).
% 1.64/0.59  fof(f295,plain,(
% 1.64/0.59    ~r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK1) | ~r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK0) | spl7_16),
% 1.64/0.59    inference(resolution,[],[f259,f39])).
% 1.64/0.59  fof(f39,plain,(
% 1.64/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.64/0.59    inference(equality_resolution,[],[f32])).
% 1.64/0.59  fof(f32,plain,(
% 1.64/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 1.64/0.59    inference(cnf_transformation,[],[f20])).
% 1.64/0.61  fof(f259,plain,(
% 1.64/0.61    ~r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) | spl7_16),
% 1.64/0.61    inference(avatar_component_clause,[],[f257])).
% 1.64/0.61  fof(f260,plain,(
% 1.64/0.61    ~spl7_1 | ~spl7_6 | ~spl7_16 | ~spl7_11 | spl7_7),
% 1.64/0.61    inference(avatar_split_clause,[],[f251,f102,f171,f257,f98,f75])).
% 1.64/0.61  fof(f171,plain,(
% 1.64/0.61    spl7_11 <=> r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),sK2)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.64/0.61  fof(f251,plain,(
% 1.64/0.61    ~r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),sK2) | ~r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) | ~v1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) | ~v1_relat_1(sK2) | spl7_7),
% 1.64/0.61    inference(resolution,[],[f103,f36])).
% 1.64/0.61  fof(f36,plain,(
% 1.64/0.61    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.64/0.61    inference(equality_resolution,[],[f25])).
% 1.64/0.61  fof(f25,plain,(
% 1.64/0.61    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f15])).
% 1.64/0.61  fof(f103,plain,(
% 1.64/0.61    ~r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) | spl7_7),
% 1.64/0.61    inference(avatar_component_clause,[],[f102])).
% 1.64/0.61  fof(f214,plain,(
% 1.64/0.61    ~spl7_1 | ~spl7_6 | spl7_11 | ~spl7_7),
% 1.64/0.61    inference(avatar_split_clause,[],[f209,f102,f171,f98,f75])).
% 1.64/0.61  fof(f209,plain,(
% 1.64/0.61    r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),sK2) | ~v1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) | ~v1_relat_1(sK2) | ~spl7_7),
% 1.64/0.61    inference(resolution,[],[f104,f37])).
% 1.64/0.61  fof(f37,plain,(
% 1.64/0.61    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.64/0.61    inference(equality_resolution,[],[f24])).
% 1.64/0.61  fof(f24,plain,(
% 1.64/0.61    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f15])).
% 1.64/0.61  fof(f187,plain,(
% 1.64/0.61    ~spl7_1 | ~spl7_5 | spl7_11 | ~spl7_9),
% 1.64/0.61    inference(avatar_split_clause,[],[f181,f111,f171,f94,f75])).
% 1.64/0.61  fof(f94,plain,(
% 1.64/0.61    spl7_5 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.64/0.61  fof(f111,plain,(
% 1.64/0.61    spl7_9 <=> r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,sK0))),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.64/0.61  fof(f181,plain,(
% 1.64/0.61    r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),sK2) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2) | ~spl7_9),
% 1.64/0.61    inference(resolution,[],[f113,f37])).
% 1.64/0.61  fof(f113,plain,(
% 1.64/0.61    r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,sK0)) | ~spl7_9),
% 1.64/0.61    inference(avatar_component_clause,[],[f111])).
% 1.64/0.61  fof(f186,plain,(
% 1.64/0.61    ~spl7_1 | ~spl7_5 | spl7_10 | ~spl7_9),
% 1.64/0.61    inference(avatar_split_clause,[],[f180,f111,f167,f94,f75])).
% 1.64/0.61  fof(f180,plain,(
% 1.64/0.61    r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK0) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2) | ~spl7_9),
% 1.64/0.61    inference(resolution,[],[f113,f38])).
% 1.64/0.61  fof(f174,plain,(
% 1.64/0.61    ~spl7_1 | ~spl7_5 | ~spl7_10 | ~spl7_11 | spl7_9),
% 1.64/0.61    inference(avatar_split_clause,[],[f161,f111,f171,f167,f94,f75])).
% 1.64/0.61  fof(f161,plain,(
% 1.64/0.61    ~r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),sK2) | ~r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK0) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2) | spl7_9),
% 1.64/0.61    inference(resolution,[],[f112,f36])).
% 1.64/0.61  fof(f112,plain,(
% 1.64/0.61    ~r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,sK0)) | spl7_9),
% 1.64/0.61    inference(avatar_component_clause,[],[f111])).
% 1.64/0.61  fof(f123,plain,(
% 1.64/0.61    spl7_1),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f122])).
% 1.64/0.61  fof(f122,plain,(
% 1.64/0.61    $false | spl7_1),
% 1.64/0.61    inference(resolution,[],[f77,f21])).
% 1.64/0.61  fof(f21,plain,(
% 1.64/0.61    v1_relat_1(sK2)),
% 1.64/0.61    inference(cnf_transformation,[],[f10])).
% 1.64/0.61  fof(f10,plain,(
% 1.64/0.61    k7_relat_1(k7_relat_1(sK2,sK0),sK1) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) & v1_relat_1(sK2)),
% 1.64/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).
% 1.64/0.61  fof(f9,plain,(
% 1.64/0.61    ? [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) != k7_relat_1(X2,k3_xboole_0(X0,X1)) & v1_relat_1(X2)) => (k7_relat_1(k7_relat_1(sK2,sK0),sK1) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) & v1_relat_1(sK2))),
% 1.64/0.61    introduced(choice_axiom,[])).
% 1.64/0.61  fof(f6,plain,(
% 1.64/0.61    ? [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) != k7_relat_1(X2,k3_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 1.64/0.61    inference(ennf_transformation,[],[f5])).
% 1.64/0.61  fof(f5,negated_conjecture,(
% 1.64/0.61    ~! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.64/0.61    inference(negated_conjecture,[],[f4])).
% 1.64/0.61  fof(f4,conjecture,(
% 1.64/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 1.64/0.61  fof(f77,plain,(
% 1.64/0.61    ~v1_relat_1(sK2) | spl7_1),
% 1.64/0.61    inference(avatar_component_clause,[],[f75])).
% 1.64/0.61  fof(f121,plain,(
% 1.64/0.61    spl7_6),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f119])).
% 1.64/0.61  fof(f119,plain,(
% 1.64/0.61    $false | spl7_6),
% 1.64/0.61    inference(resolution,[],[f100,f51])).
% 1.64/0.61  fof(f51,plain,(
% 1.64/0.61    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 1.64/0.61    inference(resolution,[],[f21,f29])).
% 1.64/0.61  fof(f29,plain,(
% 1.64/0.61    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f8])).
% 1.64/0.61  fof(f8,plain,(
% 1.64/0.61    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.64/0.61    inference(ennf_transformation,[],[f3])).
% 1.64/0.61  fof(f3,axiom,(
% 1.64/0.61    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.64/0.61  fof(f100,plain,(
% 1.64/0.61    ~v1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) | spl7_6),
% 1.64/0.61    inference(avatar_component_clause,[],[f98])).
% 1.64/0.61  fof(f118,plain,(
% 1.64/0.61    spl7_5),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f116])).
% 1.64/0.61  fof(f116,plain,(
% 1.64/0.61    $false | spl7_5),
% 1.64/0.61    inference(resolution,[],[f96,f51])).
% 1.64/0.61  fof(f96,plain,(
% 1.64/0.61    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl7_5),
% 1.64/0.61    inference(avatar_component_clause,[],[f94])).
% 1.64/0.61  fof(f115,plain,(
% 1.64/0.61    ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9),
% 1.64/0.61    inference(avatar_split_clause,[],[f92,f111,f106,f102,f98,f94])).
% 1.64/0.61  fof(f92,plain,(
% 1.64/0.61    ~r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,sK0)) | ~r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK1) | ~r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) | ~v1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 1.64/0.61    inference(resolution,[],[f43,f44])).
% 1.64/0.61  fof(f44,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (sQ6_eqProxy(k7_relat_1(X0,X1),X2) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 1.64/0.61    inference(equality_proxy_replacement,[],[f28,f42])).
% 1.64/0.61  fof(f42,plain,(
% 1.64/0.61    ! [X1,X0] : (sQ6_eqProxy(X0,X1) <=> X0 = X1)),
% 1.64/0.61    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).
% 1.64/0.61  fof(f28,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f15])).
% 1.64/0.61  fof(f43,plain,(
% 1.64/0.61    ~sQ6_eqProxy(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),
% 1.64/0.61    inference(equality_proxy_replacement,[],[f22,f42])).
% 1.64/0.61  fof(f22,plain,(
% 1.64/0.61    k7_relat_1(k7_relat_1(sK2,sK0),sK1) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 1.64/0.61    inference(cnf_transformation,[],[f10])).
% 1.64/0.61  fof(f114,plain,(
% 1.64/0.61    ~spl7_5 | ~spl7_6 | spl7_7 | spl7_9),
% 1.64/0.61    inference(avatar_split_clause,[],[f91,f111,f102,f98,f94])).
% 1.64/0.61  fof(f91,plain,(
% 1.64/0.61    r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,sK0)) | r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) | ~v1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 1.64/0.61    inference(resolution,[],[f43,f45])).
% 1.64/0.61  fof(f45,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (sQ6_eqProxy(k7_relat_1(X0,X1),X2) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 1.64/0.61    inference(equality_proxy_replacement,[],[f27,f42])).
% 1.64/0.61  fof(f27,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f15])).
% 1.64/0.61  fof(f109,plain,(
% 1.64/0.61    ~spl7_5 | ~spl7_6 | spl7_7 | spl7_8),
% 1.64/0.61    inference(avatar_split_clause,[],[f90,f106,f102,f98,f94])).
% 1.64/0.61  fof(f90,plain,(
% 1.64/0.61    r2_hidden(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK1) | r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),sK4(k7_relat_1(sK2,sK0),sK1,k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) | ~v1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 1.64/0.61    inference(resolution,[],[f43,f46])).
% 1.64/0.61  fof(f46,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (sQ6_eqProxy(k7_relat_1(X0,X1),X2) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 1.64/0.61    inference(equality_proxy_replacement,[],[f26,f42])).
% 1.64/0.61  fof(f26,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f15])).
% 1.64/0.61  % SZS output end Proof for theBenchmark
% 1.64/0.61  % (31679)------------------------------
% 1.64/0.61  % (31679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.61  % (31679)Termination reason: Refutation
% 1.64/0.61  
% 1.64/0.61  % (31679)Memory used [KB]: 6396
% 1.64/0.61  % (31679)Time elapsed: 0.169 s
% 1.64/0.61  % (31679)------------------------------
% 1.64/0.61  % (31679)------------------------------
% 1.64/0.61  % (31666)Success in time 0.248 s
%------------------------------------------------------------------------------
