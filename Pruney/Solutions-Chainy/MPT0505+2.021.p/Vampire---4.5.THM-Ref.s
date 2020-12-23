%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
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

% (16345)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
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
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f178,plain,
    ( spl7_14
  <=> r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f80,plain,
    ( spl7_5
  <=> r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f272,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl7_5 ),
    inference(resolution,[],[f82,f39])).

fof(f39,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f18])).

% (16346)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f18,plain,(
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

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(f82,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK1))
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
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f75,plain,
    ( spl7_4
  <=> r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f71,plain,
    ( spl7_3
  <=> r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f260,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),sK2)
    | ~ r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK0)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | spl7_3 ),
    inference(resolution,[],[f72,f38])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f252,plain,
    ( ~ spl7_4
    | spl7_19 ),
    inference(avatar_split_clause,[],[f249,f214,f75])).

fof(f214,plain,
    ( spl7_19
  <=> r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f249,plain,
    ( ~ r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK0)
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
    ( k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

fof(f216,plain,
    ( ~ r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK1)
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
    ( ~ r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),sK2)
    | ~ r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | spl7_5 ),
    inference(resolution,[],[f81,f38])).

fof(f81,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK1))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f181,plain,
    ( ~ spl7_6
    | ~ spl7_2
    | spl7_14
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f172,f71,f178,f67,f100])).

fof(f172,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f73,f39])).

fof(f73,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f176,plain,
    ( ~ spl7_6
    | ~ spl7_2
    | spl7_4
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f171,f71,f75,f67,f100])).

fof(f171,plain,
    ( r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK0)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f73,f40])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f122,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl7_2 ),
    inference(resolution,[],[f69,f47])).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f24,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
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
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
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
    ( ~ r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK1))
    | ~ r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK0)
    | ~ r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f42,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k7_relat_1(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f32,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ~ sQ6_eqProxy(k7_relat_1(k7_relat_1(sK2,sK1),sK0),k7_relat_1(sK2,sK0)) ),
    inference(equality_proxy_replacement,[],[f26,f41])).

fof(f26,plain,(
    k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f83,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_3
    | spl7_5 ),
    inference(avatar_split_clause,[],[f60,f80,f71,f67,f63])).

fof(f60,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK1))
    | r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f42,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k7_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f31,f41])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f78,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f59,f75,f71,f67,f63])).

fof(f59,plain,
    ( r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK0)
    | r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f42,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k7_relat_1(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f30,f41])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:06:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (16348)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.49  % (16335)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (16335)Refutation not found, incomplete strategy% (16335)------------------------------
% 0.20/0.50  % (16335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16335)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16335)Memory used [KB]: 10618
% 0.20/0.50  % (16335)Time elapsed: 0.078 s
% 0.20/0.50  % (16335)------------------------------
% 0.20/0.50  % (16335)------------------------------
% 0.20/0.50  % (16336)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (16338)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (16343)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (16360)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.50  % (16356)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (16339)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (16355)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (16355)Refutation not found, incomplete strategy% (16355)------------------------------
% 0.20/0.51  % (16355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16355)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (16355)Memory used [KB]: 10618
% 0.20/0.51  % (16355)Time elapsed: 0.110 s
% 0.20/0.51  % (16355)------------------------------
% 0.20/0.51  % (16355)------------------------------
% 0.20/0.51  % (16348)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f281,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f78,f83,f84,f117,f119,f122,f176,f181,f217,f252,f264,f276])).
% 0.20/0.51  % (16345)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  fof(f276,plain,(
% 0.20/0.51    ~spl7_6 | ~spl7_1 | spl7_14 | ~spl7_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f272,f80,f178,f63,f100])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    spl7_6 <=> v1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    spl7_1 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    spl7_14 <=> r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    spl7_5 <=> r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.51  fof(f272,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),sK2) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~spl7_5),
% 0.20/0.51    inference(resolution,[],[f82,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f18])).
% 0.20/0.51  % (16346)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(rectify,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK1)) | ~spl7_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f80])).
% 0.20/0.51  fof(f264,plain,(
% 0.20/0.51    ~spl7_6 | ~spl7_2 | ~spl7_4 | ~spl7_14 | spl7_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f260,f71,f178,f75,f67,f100])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    spl7_2 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    spl7_4 <=> r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    spl7_3 <=> r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.51  fof(f260,plain,(
% 0.20/0.51    ~r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),sK2) | ~r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK0) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2) | spl7_3),
% 0.20/0.51    inference(resolution,[],[f72,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ~r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0)) | spl7_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f71])).
% 0.20/0.51  fof(f252,plain,(
% 0.20/0.51    ~spl7_4 | spl7_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f249,f214,f75])).
% 0.20/0.51  fof(f214,plain,(
% 0.20/0.51    spl7_19 <=> r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.20/0.51  fof(f249,plain,(
% 0.20/0.51    ~r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK0) | spl7_19),
% 0.20/0.51    inference(resolution,[],[f216,f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.20/0.51    inference(resolution,[],[f25,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f7])).
% 0.20/0.51  fof(f7,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f5])).
% 0.20/0.51  fof(f5,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    ~r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK1) | spl7_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f214])).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    ~spl7_6 | ~spl7_1 | ~spl7_19 | ~spl7_14 | spl7_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f209,f80,f178,f214,f63,f100])).
% 0.20/0.51  fof(f209,plain,(
% 0.20/0.51    ~r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),sK2) | ~r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK1) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | spl7_5),
% 0.20/0.51    inference(resolution,[],[f81,f38])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ~r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK1)) | spl7_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f80])).
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    ~spl7_6 | ~spl7_2 | spl7_14 | ~spl7_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f172,f71,f178,f67,f100])).
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),sK2) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2) | ~spl7_3),
% 0.20/0.51    inference(resolution,[],[f73,f39])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0)) | ~spl7_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f71])).
% 0.20/0.51  fof(f176,plain,(
% 0.20/0.51    ~spl7_6 | ~spl7_2 | spl7_4 | ~spl7_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f171,f71,f75,f67,f100])).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK0) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2) | ~spl7_3),
% 0.20/0.51    inference(resolution,[],[f73,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    spl7_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f120])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    $false | spl7_2),
% 0.20/0.51    inference(resolution,[],[f69,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.20/0.51    inference(resolution,[],[f24,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    v1_relat_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl7_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f67])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    spl7_6),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f118])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    $false | spl7_6),
% 0.20/0.51    inference(resolution,[],[f102,f24])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | spl7_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f100])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    spl7_1),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f115])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    $false | spl7_1),
% 0.20/0.51    inference(resolution,[],[f65,f47])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl7_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f63])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f61,f80,f75,f71,f67,f63])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ~r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK1)) | ~r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK0) | ~r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.20/0.51    inference(resolution,[],[f42,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sQ6_eqProxy(k7_relat_1(X0,X1),X2) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(equality_proxy_replacement,[],[f32,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ! [X1,X0] : (sQ6_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.51    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ~sQ6_eqProxy(k7_relat_1(k7_relat_1(sK2,sK1),sK0),k7_relat_1(sK2,sK0))),
% 0.20/0.51    inference(equality_proxy_replacement,[],[f26,f41])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ~spl7_1 | ~spl7_2 | spl7_3 | spl7_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f60,f80,f71,f67,f63])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK1)) | r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.20/0.51    inference(resolution,[],[f42,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sQ6_eqProxy(k7_relat_1(X0,X1),X2) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(equality_proxy_replacement,[],[f31,f41])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ~spl7_1 | ~spl7_2 | spl7_3 | spl7_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f59,f75,f71,f67,f63])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    r2_hidden(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK0) | r2_hidden(k4_tarski(sK3(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK2,sK1),sK0,k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.20/0.51    inference(resolution,[],[f42,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sQ6_eqProxy(k7_relat_1(X0,X1),X2) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(equality_proxy_replacement,[],[f30,f41])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (16348)------------------------------
% 0.20/0.51  % (16348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16348)Termination reason: Refutation
% 0.20/0.51  % (16352)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.51  
% 0.20/0.51  % (16348)Memory used [KB]: 6396
% 0.20/0.51  % (16348)Time elapsed: 0.086 s
% 0.20/0.51  % (16348)------------------------------
% 0.20/0.51  % (16348)------------------------------
% 0.20/0.51  % (16332)Success in time 0.162 s
%------------------------------------------------------------------------------
