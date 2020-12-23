%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0507+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 206 expanded)
%              Number of leaves         :   20 (  78 expanded)
%              Depth                    :   13
%              Number of atoms          :  348 ( 925 expanded)
%              Number of equality atoms :   13 (  33 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f47,f51,f55,f75,f78,f84,f96,f114,f121,f132,f151,f158])).

fof(f158,plain,
    ( ~ spl7_5
    | spl7_1
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f155,f149,f41,f70])).

fof(f70,plain,
    ( spl7_5
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f41,plain,
    ( spl7_1
  <=> r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f149,plain,
    ( spl7_19
  <=> r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f155,plain,
    ( r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl7_19 ),
    inference(resolution,[],[f150,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f150,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f149])).

fof(f151,plain,
    ( ~ spl7_4
    | spl7_1
    | spl7_19
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f145,f130,f149,f41,f53])).

fof(f53,plain,
    ( spl7_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f130,plain,
    ( spl7_16
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),k7_relat_1(sK2,X0))
        | ~ r2_hidden(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f145,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0))
    | r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl7_16 ),
    inference(resolution,[],[f131,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k7_relat_1(X0,X1),X2),X1)
      | r1_tarski(k7_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f36,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X0,X1),X2)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | r2_hidden(sK3(k7_relat_1(X0,X1),X2),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f28,f56])).

fof(f56,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(X5,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f39,f36])).

fof(f39,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK5(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0)
                    & r2_hidden(sK5(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0)
            & r2_hidden(sK5(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
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

fof(f131,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),X0)
        | r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),k7_relat_1(sK2,X0)) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( ~ spl7_3
    | spl7_16
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f126,f119,f130,f49])).

fof(f49,plain,
    ( spl7_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f119,plain,
    ( spl7_14
  <=> r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f126,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),k7_relat_1(sK2,X0))
        | ~ r2_hidden(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_14 ),
    inference(resolution,[],[f120,f58])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f37,f36])).

fof(f37,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f120,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK2)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,
    ( spl7_14
    | ~ spl7_2
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f115,f112,f45,f119])).

fof(f45,plain,
    ( spl7_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f112,plain,
    ( spl7_13
  <=> ! [X1] :
        ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),X1)
        | ~ r1_tarski(sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f115,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK2)
    | ~ spl7_2
    | ~ spl7_13 ),
    inference(resolution,[],[f113,f46])).

fof(f46,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f113,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK1,X1)
        | r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),X1) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f112])).

fof(f114,plain,
    ( ~ spl7_4
    | spl7_13
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f106,f94,f112,f53])).

fof(f94,plain,
    ( spl7_9
  <=> r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f106,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),X1)
        | ~ r1_tarski(sK1,X1)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_9 ),
    inference(resolution,[],[f95,f27])).

fof(f27,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X5),X0)
      | r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f95,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK1)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f96,plain,
    ( ~ spl7_4
    | spl7_9
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f89,f82,f94,f53])).

fof(f82,plain,
    ( spl7_7
  <=> r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f89,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_7 ),
    inference(resolution,[],[f83,f57])).

fof(f57,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f38,f36])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),k7_relat_1(sK1,sK0))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,
    ( ~ spl7_5
    | spl7_7
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f79,f73,f82,f70])).

fof(f73,plain,
    ( spl7_6
  <=> ! [X0] :
        ( ~ r1_tarski(k7_relat_1(sK1,sK0),X0)
        | r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f79,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl7_6 ),
    inference(resolution,[],[f74,f62])).

fof(f62,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f29,f28])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k7_relat_1(sK1,sK0),X0)
        | r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),X0) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f78,plain,
    ( ~ spl7_4
    | spl7_5 ),
    inference(avatar_split_clause,[],[f76,f70,f53])).

fof(f76,plain,
    ( ~ v1_relat_1(sK1)
    | spl7_5 ),
    inference(resolution,[],[f71,f36])).

fof(f71,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f75,plain,
    ( ~ spl7_5
    | spl7_6
    | spl7_1 ),
    inference(avatar_split_clause,[],[f68,f41,f73,f70])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k7_relat_1(sK1,sK0),X0)
        | ~ v1_relat_1(k7_relat_1(sK1,sK0))
        | r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),X0) )
    | spl7_1 ),
    inference(resolution,[],[f65,f42])).

fof(f42,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X2) ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X2)
      | ~ r1_tarski(X0,X2)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f27,f28])).

fof(f55,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
            & r1_tarski(X1,X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(X2,sK0))
          & r1_tarski(sK1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(X2,sK0))
        & r1_tarski(sK1,X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))
      & r1_tarski(sK1,sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

fof(f51,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f25,f45])).

fof(f25,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f26,f41])).

fof(f26,plain,(
    ~ r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
