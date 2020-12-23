%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 226 expanded)
%              Number of leaves         :   16 (  86 expanded)
%              Depth                    :   10
%              Number of atoms          :  332 (1195 expanded)
%              Number of equality atoms :   25 ( 146 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f84,f117,f119,f122,f176,f181,f217,f252,f264,f276])).

fof(f276,plain,
    ( ~ spl7_6
    | ~ spl7_1
    | spl7_14
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f272,f80,f178,f63,f100])).

fof(f100,plain,
    ( spl7_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f63,plain,
    ( spl7_1
  <=> v1_relat_1(k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f178,plain,
    ( spl7_14
  <=> r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f80,plain,
    ( spl7_5
  <=> r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f272,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),sK2)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl7_5 ),
    inference(resolution,[],[f82,f39])).

fof(f39,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f18])).

fof(f18,plain,(
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

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

fof(f82,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK1,sK2))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f264,plain,
    ( ~ spl7_6
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | spl7_3 ),
    inference(avatar_split_clause,[],[f260,f71,f178,f75,f67,f100])).

fof(f67,plain,
    ( spl7_2
  <=> v1_relat_1(k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f75,plain,
    ( spl7_4
  <=> r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f71,plain,
    ( spl7_3
  <=> r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f260,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),sK2)
    | ~ r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK0)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | spl7_3 ),
    inference(resolution,[],[f72,f38])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK2))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f252,plain,
    ( ~ spl7_4
    | spl7_19 ),
    inference(avatar_split_clause,[],[f249,f214,f75])).

fof(f214,plain,
    ( spl7_19
  <=> r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f249,plain,
    ( ~ r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK0)
    | spl7_19 ),
    inference(resolution,[],[f216,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f25,f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f25,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).

fof(f216,plain,
    ( ~ r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK1)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f214])).

fof(f217,plain,
    ( ~ spl7_6
    | ~ spl7_1
    | ~ spl7_19
    | ~ spl7_14
    | spl7_5 ),
    inference(avatar_split_clause,[],[f209,f80,f178,f214,f63,f100])).

fof(f209,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),sK2)
    | ~ r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK1)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | spl7_5 ),
    inference(resolution,[],[f81,f38])).

fof(f81,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK1,sK2))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f181,plain,
    ( ~ spl7_6
    | ~ spl7_2
    | spl7_14
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f172,f71,f178,f67,f100])).

fof(f172,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f73,f39])).

fof(f73,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK2))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f176,plain,
    ( ~ spl7_6
    | ~ spl7_2
    | spl7_4
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f171,f71,f75,f67,f100])).

fof(f171,plain,
    ( r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK0)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f73,f40])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f122,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl7_2 ),
    inference(resolution,[],[f69,f47])).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK2)) ),
    inference(resolution,[],[f24,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f119,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl7_6 ),
    inference(resolution,[],[f102,f24])).

fof(f102,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f117,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl7_1 ),
    inference(resolution,[],[f65,f47])).

fof(f65,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f84,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f61,f80,f75,f71,f67,f63])).

fof(f61,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK1,sK2))
    | ~ r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK0)
    | ~ r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f42,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k8_relat_1(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f34,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ~ sQ6_eqProxy(k8_relat_1(sK0,k8_relat_1(sK1,sK2)),k8_relat_1(sK0,sK2)) ),
    inference(equality_proxy_replacement,[],[f26,f41])).

fof(f26,plain,(
    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f83,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_3
    | spl7_5 ),
    inference(avatar_split_clause,[],[f60,f80,f71,f67,f63])).

fof(f60,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK1,sK2))
    | r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f42,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k8_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f33,f41])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f78,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f59,f75,f71,f67,f63])).

fof(f59,plain,
    ( r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK0)
    | r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f42,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k8_relat_1(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f32,f41])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (32644)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (32635)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (32652)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (32652)Refutation not found, incomplete strategy% (32652)------------------------------
% 0.22/0.52  % (32652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32652)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (32652)Memory used [KB]: 10618
% 0.22/0.52  % (32652)Time elapsed: 0.118 s
% 0.22/0.52  % (32652)------------------------------
% 0.22/0.52  % (32652)------------------------------
% 0.22/0.52  % (32649)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (32632)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (32634)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (32640)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (32648)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (32651)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (32657)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (32645)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (32643)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (32637)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (32639)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (32631)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (32638)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (32631)Refutation not found, incomplete strategy% (32631)------------------------------
% 0.22/0.55  % (32631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32631)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32631)Memory used [KB]: 10618
% 0.22/0.55  % (32631)Time elapsed: 0.125 s
% 0.22/0.55  % (32631)------------------------------
% 0.22/0.55  % (32631)------------------------------
% 0.22/0.55  % (32647)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (32654)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (32647)Refutation not found, incomplete strategy% (32647)------------------------------
% 0.22/0.55  % (32647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32647)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32647)Memory used [KB]: 10618
% 0.22/0.55  % (32647)Time elapsed: 0.148 s
% 0.22/0.55  % (32647)------------------------------
% 0.22/0.55  % (32647)------------------------------
% 0.22/0.56  % (32655)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (32630)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.56  % (32653)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (32633)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.56  % (32646)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.57  % (32642)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (32658)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (32645)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (32659)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.57  % (32629)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f281,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(avatar_sat_refutation,[],[f78,f83,f84,f117,f119,f122,f176,f181,f217,f252,f264,f276])).
% 0.22/0.58  fof(f276,plain,(
% 0.22/0.58    ~spl7_6 | ~spl7_1 | spl7_14 | ~spl7_5),
% 0.22/0.58    inference(avatar_split_clause,[],[f272,f80,f178,f63,f100])).
% 0.22/0.58  fof(f100,plain,(
% 0.22/0.58    spl7_6 <=> v1_relat_1(sK2)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.58  fof(f63,plain,(
% 0.22/0.58    spl7_1 <=> v1_relat_1(k8_relat_1(sK1,sK2))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.58  fof(f178,plain,(
% 0.22/0.58    spl7_14 <=> r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),sK2)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.58  fof(f80,plain,(
% 0.22/0.58    spl7_5 <=> r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK1,sK2))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.58  fof(f272,plain,(
% 0.22/0.58    r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),sK2) | ~v1_relat_1(k8_relat_1(sK1,sK2)) | ~v1_relat_1(sK2) | ~spl7_5),
% 0.22/0.58    inference(resolution,[],[f82,f39])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.58    inference(equality_resolution,[],[f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f18])).
% 0.22/0.58  fof(f18,plain,(
% 0.22/0.58    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f17,plain,(
% 0.22/0.58    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(rectify,[],[f16])).
% 0.22/0.58  fof(f16,plain,(
% 0.22/0.58    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(flattening,[],[f15])).
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0))) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(nnf_transformation,[],[f11])).
% 0.22/0.58  fof(f11,plain,(
% 0.22/0.58    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0))))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).
% 0.22/0.58  fof(f82,plain,(
% 0.22/0.58    r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK1,sK2)) | ~spl7_5),
% 0.22/0.58    inference(avatar_component_clause,[],[f80])).
% 0.22/0.58  fof(f264,plain,(
% 0.22/0.58    ~spl7_6 | ~spl7_2 | ~spl7_4 | ~spl7_14 | spl7_3),
% 0.22/0.58    inference(avatar_split_clause,[],[f260,f71,f178,f75,f67,f100])).
% 0.22/0.58  fof(f67,plain,(
% 0.22/0.58    spl7_2 <=> v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.58  fof(f75,plain,(
% 0.22/0.58    spl7_4 <=> r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.58  fof(f71,plain,(
% 0.22/0.58    spl7_3 <=> r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK2))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.58  fof(f260,plain,(
% 0.22/0.58    ~r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),sK2) | ~r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK0) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(sK2) | spl7_3),
% 0.22/0.58    inference(resolution,[],[f72,f38])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.58    inference(equality_resolution,[],[f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f72,plain,(
% 0.22/0.58    ~r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK2)) | spl7_3),
% 0.22/0.58    inference(avatar_component_clause,[],[f71])).
% 0.22/0.58  fof(f252,plain,(
% 0.22/0.58    ~spl7_4 | spl7_19),
% 0.22/0.58    inference(avatar_split_clause,[],[f249,f214,f75])).
% 0.22/0.58  fof(f214,plain,(
% 0.22/0.58    spl7_19 <=> r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.22/0.58  fof(f249,plain,(
% 0.22/0.58    ~r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK0) | spl7_19),
% 0.22/0.58    inference(resolution,[],[f216,f58])).
% 0.22/0.58  fof(f58,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.22/0.58    inference(resolution,[],[f25,f35])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.58    inference(rectify,[],[f20])).
% 0.22/0.58  fof(f20,plain,(
% 0.22/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.58    inference(nnf_transformation,[],[f12])).
% 0.22/0.58  fof(f12,plain,(
% 0.22/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    r1_tarski(sK0,sK1)),
% 0.22/0.58    inference(cnf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).
% 0.22/0.58  fof(f13,plain,(
% 0.22/0.58    ? [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f8,plain,(
% 0.22/0.58    ? [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.22/0.58    inference(flattening,[],[f7])).
% 0.22/0.58  fof(f7,plain,(
% 0.22/0.58    ? [X0,X1,X2] : ((k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.22/0.58    inference(ennf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,negated_conjecture,(
% 0.22/0.58    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)))),
% 0.22/0.58    inference(negated_conjecture,[],[f5])).
% 0.22/0.58  fof(f5,conjecture,(
% 0.22/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).
% 0.22/0.58  fof(f216,plain,(
% 0.22/0.58    ~r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK1) | spl7_19),
% 0.22/0.58    inference(avatar_component_clause,[],[f214])).
% 0.22/0.58  fof(f217,plain,(
% 0.22/0.58    ~spl7_6 | ~spl7_1 | ~spl7_19 | ~spl7_14 | spl7_5),
% 0.22/0.58    inference(avatar_split_clause,[],[f209,f80,f178,f214,f63,f100])).
% 0.22/0.58  fof(f209,plain,(
% 0.22/0.58    ~r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),sK2) | ~r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK1) | ~v1_relat_1(k8_relat_1(sK1,sK2)) | ~v1_relat_1(sK2) | spl7_5),
% 0.22/0.58    inference(resolution,[],[f81,f38])).
% 0.22/0.58  fof(f81,plain,(
% 0.22/0.58    ~r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK1,sK2)) | spl7_5),
% 0.22/0.58    inference(avatar_component_clause,[],[f80])).
% 0.22/0.58  fof(f181,plain,(
% 0.22/0.58    ~spl7_6 | ~spl7_2 | spl7_14 | ~spl7_3),
% 0.22/0.58    inference(avatar_split_clause,[],[f172,f71,f178,f67,f100])).
% 0.22/0.58  fof(f172,plain,(
% 0.22/0.58    r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),sK2) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(sK2) | ~spl7_3),
% 0.22/0.58    inference(resolution,[],[f73,f39])).
% 0.22/0.58  fof(f73,plain,(
% 0.22/0.58    r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK2)) | ~spl7_3),
% 0.22/0.58    inference(avatar_component_clause,[],[f71])).
% 0.22/0.58  fof(f176,plain,(
% 0.22/0.58    ~spl7_6 | ~spl7_2 | spl7_4 | ~spl7_3),
% 0.22/0.58    inference(avatar_split_clause,[],[f171,f71,f75,f67,f100])).
% 0.22/0.58  fof(f171,plain,(
% 0.22/0.58    r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK0) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(sK2) | ~spl7_3),
% 0.22/0.58    inference(resolution,[],[f73,f40])).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    ( ! [X6,X0,X5,X1] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.58    inference(equality_resolution,[],[f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f122,plain,(
% 0.22/0.58    spl7_2),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f120])).
% 0.22/0.58  fof(f120,plain,(
% 0.22/0.58    $false | spl7_2),
% 0.22/0.58    inference(resolution,[],[f69,f47])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK2))) )),
% 0.22/0.58    inference(resolution,[],[f24,f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f9])).
% 0.22/0.58  fof(f9,plain,(
% 0.22/0.58    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    v1_relat_1(sK2)),
% 0.22/0.58    inference(cnf_transformation,[],[f14])).
% 0.22/0.58  fof(f69,plain,(
% 0.22/0.58    ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl7_2),
% 0.22/0.58    inference(avatar_component_clause,[],[f67])).
% 0.22/0.58  fof(f119,plain,(
% 0.22/0.58    spl7_6),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f118])).
% 0.22/0.58  fof(f118,plain,(
% 0.22/0.58    $false | spl7_6),
% 0.22/0.58    inference(resolution,[],[f102,f24])).
% 0.22/0.58  fof(f102,plain,(
% 0.22/0.58    ~v1_relat_1(sK2) | spl7_6),
% 0.22/0.58    inference(avatar_component_clause,[],[f100])).
% 0.22/0.58  fof(f117,plain,(
% 0.22/0.58    spl7_1),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f115])).
% 0.22/0.58  fof(f115,plain,(
% 0.22/0.58    $false | spl7_1),
% 0.22/0.58    inference(resolution,[],[f65,f47])).
% 0.22/0.58  fof(f65,plain,(
% 0.22/0.58    ~v1_relat_1(k8_relat_1(sK1,sK2)) | spl7_1),
% 0.22/0.58    inference(avatar_component_clause,[],[f63])).
% 0.22/0.58  fof(f84,plain,(
% 0.22/0.58    ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5),
% 0.22/0.58    inference(avatar_split_clause,[],[f61,f80,f75,f71,f67,f63])).
% 0.22/0.58  fof(f61,plain,(
% 0.22/0.58    ~r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK1,sK2)) | ~r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK0) | ~r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK2)) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(k8_relat_1(sK1,sK2))),
% 0.22/0.58    inference(resolution,[],[f42,f43])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (sQ6_eqProxy(k8_relat_1(X0,X1),X2) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.58    inference(equality_proxy_replacement,[],[f34,f41])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    ! [X1,X0] : (sQ6_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.58    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k8_relat_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    ~sQ6_eqProxy(k8_relat_1(sK0,k8_relat_1(sK1,sK2)),k8_relat_1(sK0,sK2))),
% 0.22/0.58    inference(equality_proxy_replacement,[],[f26,f41])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)),
% 0.22/0.58    inference(cnf_transformation,[],[f14])).
% 0.22/0.58  fof(f83,plain,(
% 0.22/0.58    ~spl7_1 | ~spl7_2 | spl7_3 | spl7_5),
% 0.22/0.58    inference(avatar_split_clause,[],[f60,f80,f71,f67,f63])).
% 0.22/0.58  fof(f60,plain,(
% 0.22/0.58    r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK1,sK2)) | r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK2)) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(k8_relat_1(sK1,sK2))),
% 0.22/0.58    inference(resolution,[],[f42,f44])).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (sQ6_eqProxy(k8_relat_1(X0,X1),X2) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.58    inference(equality_proxy_replacement,[],[f33,f41])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k8_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f78,plain,(
% 0.22/0.58    ~spl7_1 | ~spl7_2 | spl7_3 | spl7_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f59,f75,f71,f67,f63])).
% 0.22/0.58  fof(f59,plain,(
% 0.22/0.58    r2_hidden(sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK0) | r2_hidden(k4_tarski(sK3(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2)),sK4(sK0,k8_relat_1(sK1,sK2),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK2)) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(k8_relat_1(sK1,sK2))),
% 0.22/0.58    inference(resolution,[],[f42,f45])).
% 0.22/0.58  fof(f45,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (sQ6_eqProxy(k8_relat_1(X0,X1),X2) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.58    inference(equality_proxy_replacement,[],[f32,f41])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k8_relat_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (32645)------------------------------
% 0.22/0.58  % (32645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (32645)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (32645)Memory used [KB]: 6396
% 0.22/0.58  % (32645)Time elapsed: 0.116 s
% 0.22/0.58  % (32645)------------------------------
% 0.22/0.58  % (32645)------------------------------
% 0.22/0.58  % (32624)Success in time 0.214 s
%------------------------------------------------------------------------------
