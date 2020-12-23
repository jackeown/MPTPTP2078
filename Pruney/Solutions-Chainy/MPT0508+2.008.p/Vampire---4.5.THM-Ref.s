%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:40 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 191 expanded)
%              Number of leaves         :   20 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  338 ( 930 expanded)
%              Number of equality atoms :   13 (  33 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f607,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f95,f152,f156,f184,f259,f264,f291,f298,f371,f606])).

fof(f606,plain,
    ( ~ spl10_19
    | spl10_24 ),
    inference(avatar_split_clause,[],[f599,f288,f261])).

fof(f261,plain,
    ( spl10_19
  <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f288,plain,
    ( spl10_24
  <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f599,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2)
    | spl10_24 ),
    inference(resolution,[],[f290,f74])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f33,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f33,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

fof(f290,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3)
    | spl10_24 ),
    inference(avatar_component_clause,[],[f288])).

fof(f371,plain,
    ( ~ spl10_18
    | spl10_23 ),
    inference(avatar_split_clause,[],[f368,f284,f256])).

fof(f256,plain,
    ( spl10_18
  <=> r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f284,plain,
    ( spl10_23
  <=> r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f368,plain,
    ( ~ r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK0)
    | spl10_23 ),
    inference(resolution,[],[f286,f76])).

fof(f76,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f34,f47])).

fof(f34,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f286,plain,
    ( ~ r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1)
    | spl10_23 ),
    inference(avatar_component_clause,[],[f284])).

fof(f298,plain,(
    spl10_22 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | spl10_22 ),
    inference(resolution,[],[f282,f69])).

fof(f69,plain,(
    ! [X5] : v1_relat_1(k7_relat_1(sK3,X5)) ),
    inference(resolution,[],[f32,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f32,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f282,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | spl10_22 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl10_22
  <=> v1_relat_1(k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f291,plain,
    ( ~ spl10_8
    | ~ spl10_22
    | ~ spl10_23
    | ~ spl10_24
    | spl10_3 ),
    inference(avatar_split_clause,[],[f274,f92,f288,f284,f280,f135])).

fof(f135,plain,
    ( spl10_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f92,plain,
    ( spl10_3
  <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f274,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3)
    | ~ r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | spl10_3 ),
    inference(resolution,[],[f94,f50])).

fof(f50,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK6(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
                    & r2_hidden(sK6(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f94,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,sK1))
    | spl10_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f264,plain,
    ( ~ spl10_4
    | ~ spl10_1
    | spl10_19
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f250,f87,f261,f83,f108])).

fof(f108,plain,
    ( spl10_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f83,plain,
    ( spl10_1
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f87,plain,
    ( spl10_2
  <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f250,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl10_2 ),
    inference(resolution,[],[f89,f51])).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f89,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f259,plain,
    ( ~ spl10_4
    | ~ spl10_1
    | spl10_18
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f249,f87,f256,f83,f108])).

fof(f249,plain,
    ( r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK0)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl10_2 ),
    inference(resolution,[],[f89,f52])).

fof(f52,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f184,plain,(
    spl10_8 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl10_8 ),
    inference(resolution,[],[f137,f32])).

fof(f137,plain,
    ( ~ v1_relat_1(sK3)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f156,plain,(
    spl10_4 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl10_4 ),
    inference(resolution,[],[f110,f31])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f110,plain,
    ( ~ v1_relat_1(sK2)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f152,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl10_1 ),
    inference(resolution,[],[f85,f61])).

fof(f61,plain,(
    ! [X5] : v1_relat_1(k7_relat_1(sK2,X5)) ),
    inference(resolution,[],[f31,f45])).

fof(f85,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f95,plain,
    ( ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f81,f92,f83])).

fof(f81,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f35,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f35,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f90,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f80,f87,f83])).

fof(f80,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f35,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:30:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (25800)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (25823)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (25813)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (25807)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (25802)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (25815)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (25803)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (25805)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (25826)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (25804)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (25821)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (25801)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (25820)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (25818)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (25817)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (25808)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (25810)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (25821)Refutation not found, incomplete strategy% (25821)------------------------------
% 0.21/0.53  % (25821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (25827)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (25828)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (25811)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (25822)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (25821)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  % (25799)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (25801)Refutation not found, incomplete strategy% (25801)------------------------------
% 0.21/0.54  % (25801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25801)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25801)Memory used [KB]: 10618
% 0.21/0.54  % (25801)Time elapsed: 0.126 s
% 0.21/0.54  % (25801)------------------------------
% 0.21/0.54  % (25801)------------------------------
% 0.21/0.54  % (25816)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (25819)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  
% 0.21/0.54  % (25821)Memory used [KB]: 10746
% 0.21/0.54  % (25821)Time elapsed: 0.106 s
% 0.21/0.54  % (25821)------------------------------
% 0.21/0.54  % (25821)------------------------------
% 0.21/0.54  % (25809)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (25814)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.48/0.55  % (25825)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.55  % (25806)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.48/0.55  % (25812)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.48/0.56  % (25824)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.48/0.56  % (25816)Refutation not found, incomplete strategy% (25816)------------------------------
% 1.48/0.56  % (25816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (25816)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (25816)Memory used [KB]: 10618
% 1.48/0.56  % (25816)Time elapsed: 0.148 s
% 1.48/0.56  % (25816)------------------------------
% 1.48/0.56  % (25816)------------------------------
% 1.62/0.58  % (25814)Refutation found. Thanks to Tanya!
% 1.62/0.58  % SZS status Theorem for theBenchmark
% 1.62/0.58  % SZS output start Proof for theBenchmark
% 1.62/0.58  fof(f607,plain,(
% 1.62/0.58    $false),
% 1.62/0.58    inference(avatar_sat_refutation,[],[f90,f95,f152,f156,f184,f259,f264,f291,f298,f371,f606])).
% 1.62/0.58  fof(f606,plain,(
% 1.62/0.58    ~spl10_19 | spl10_24),
% 1.62/0.58    inference(avatar_split_clause,[],[f599,f288,f261])).
% 1.62/0.58  fof(f261,plain,(
% 1.62/0.58    spl10_19 <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 1.62/0.58  fof(f288,plain,(
% 1.62/0.58    spl10_24 <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 1.62/0.58  fof(f599,plain,(
% 1.62/0.58    ~r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2) | spl10_24),
% 1.62/0.58    inference(resolution,[],[f290,f74])).
% 1.62/0.58  fof(f74,plain,(
% 1.62/0.58    ( ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK2)) )),
% 1.62/0.58    inference(resolution,[],[f33,f47])).
% 1.62/0.58  fof(f47,plain,(
% 1.62/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f30])).
% 1.62/0.58  fof(f30,plain,(
% 1.62/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.62/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f28,f29])).
% 1.62/0.58  fof(f29,plain,(
% 1.62/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f28,plain,(
% 1.62/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.62/0.58    inference(rectify,[],[f27])).
% 1.62/0.58  fof(f27,plain,(
% 1.62/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.62/0.58    inference(nnf_transformation,[],[f14])).
% 1.62/0.58  fof(f14,plain,(
% 1.62/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f1])).
% 1.62/0.58  fof(f1,axiom,(
% 1.62/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.62/0.58  fof(f33,plain,(
% 1.62/0.58    r1_tarski(sK2,sK3)),
% 1.62/0.58    inference(cnf_transformation,[],[f17])).
% 1.62/0.58  fof(f17,plain,(
% 1.62/0.58    (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 1.62/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f16,f15])).
% 1.62/0.58  fof(f15,plain,(
% 1.62/0.58    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f16,plain,(
% 1.62/0.58    ? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f9,plain,(
% 1.62/0.58    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 1.62/0.58    inference(flattening,[],[f8])).
% 1.62/0.58  fof(f8,plain,(
% 1.62/0.58    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 1.62/0.58    inference(ennf_transformation,[],[f7])).
% 1.62/0.58  fof(f7,negated_conjecture,(
% 1.62/0.58    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 1.62/0.58    inference(negated_conjecture,[],[f6])).
% 1.62/0.58  fof(f6,conjecture,(
% 1.62/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).
% 1.62/0.58  fof(f290,plain,(
% 1.62/0.58    ~r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3) | spl10_24),
% 1.62/0.58    inference(avatar_component_clause,[],[f288])).
% 1.62/0.58  fof(f371,plain,(
% 1.62/0.58    ~spl10_18 | spl10_23),
% 1.62/0.58    inference(avatar_split_clause,[],[f368,f284,f256])).
% 1.62/0.58  fof(f256,plain,(
% 1.62/0.58    spl10_18 <=> r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK0)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 1.62/0.58  fof(f284,plain,(
% 1.62/0.58    spl10_23 <=> r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 1.62/0.58  fof(f368,plain,(
% 1.62/0.58    ~r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK0) | spl10_23),
% 1.62/0.58    inference(resolution,[],[f286,f76])).
% 1.62/0.58  fof(f76,plain,(
% 1.62/0.58    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 1.62/0.58    inference(resolution,[],[f34,f47])).
% 1.62/0.58  fof(f34,plain,(
% 1.62/0.58    r1_tarski(sK0,sK1)),
% 1.62/0.58    inference(cnf_transformation,[],[f17])).
% 1.62/0.58  fof(f286,plain,(
% 1.62/0.58    ~r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1) | spl10_23),
% 1.62/0.58    inference(avatar_component_clause,[],[f284])).
% 1.62/0.58  fof(f298,plain,(
% 1.62/0.58    spl10_22),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f296])).
% 1.62/0.58  fof(f296,plain,(
% 1.62/0.58    $false | spl10_22),
% 1.62/0.58    inference(resolution,[],[f282,f69])).
% 1.62/0.58  fof(f69,plain,(
% 1.62/0.58    ( ! [X5] : (v1_relat_1(k7_relat_1(sK3,X5))) )),
% 1.62/0.58    inference(resolution,[],[f32,f45])).
% 1.62/0.58  fof(f45,plain,(
% 1.62/0.58    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f12])).
% 1.62/0.58  fof(f12,plain,(
% 1.62/0.58    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f4])).
% 1.62/0.58  fof(f4,axiom,(
% 1.62/0.58    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.62/0.58  fof(f32,plain,(
% 1.62/0.58    v1_relat_1(sK3)),
% 1.62/0.58    inference(cnf_transformation,[],[f17])).
% 1.62/0.58  fof(f282,plain,(
% 1.62/0.58    ~v1_relat_1(k7_relat_1(sK3,sK1)) | spl10_22),
% 1.62/0.58    inference(avatar_component_clause,[],[f280])).
% 1.62/0.58  fof(f280,plain,(
% 1.62/0.58    spl10_22 <=> v1_relat_1(k7_relat_1(sK3,sK1))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 1.62/0.58  fof(f291,plain,(
% 1.62/0.58    ~spl10_8 | ~spl10_22 | ~spl10_23 | ~spl10_24 | spl10_3),
% 1.62/0.58    inference(avatar_split_clause,[],[f274,f92,f288,f284,f280,f135])).
% 1.62/0.58  fof(f135,plain,(
% 1.62/0.58    spl10_8 <=> v1_relat_1(sK3)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 1.62/0.58  fof(f92,plain,(
% 1.62/0.58    spl10_3 <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,sK1))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.62/0.58  fof(f274,plain,(
% 1.62/0.58    ~r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3) | ~r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1) | ~v1_relat_1(k7_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | spl10_3),
% 1.62/0.58    inference(resolution,[],[f94,f50])).
% 1.62/0.58  fof(f50,plain,(
% 1.62/0.58    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.62/0.58    inference(equality_resolution,[],[f41])).
% 1.62/0.58  fof(f41,plain,(
% 1.62/0.58    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f26])).
% 1.62/0.58  fof(f26,plain,(
% 1.62/0.58    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 1.62/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f24,f25])).
% 1.62/0.58  fof(f25,plain,(
% 1.62/0.58    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2))))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f24,plain,(
% 1.62/0.58    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 1.62/0.58    inference(rectify,[],[f23])).
% 1.62/0.58  fof(f23,plain,(
% 1.62/0.58    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 1.62/0.58    inference(flattening,[],[f22])).
% 1.62/0.58  fof(f22,plain,(
% 1.62/0.58    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 1.62/0.58    inference(nnf_transformation,[],[f11])).
% 1.62/0.58  fof(f11,plain,(
% 1.62/0.58    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f2])).
% 1.62/0.58  fof(f2,axiom,(
% 1.62/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).
% 1.62/0.58  fof(f94,plain,(
% 1.62/0.58    ~r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,sK1)) | spl10_3),
% 1.62/0.58    inference(avatar_component_clause,[],[f92])).
% 1.62/0.58  fof(f264,plain,(
% 1.62/0.58    ~spl10_4 | ~spl10_1 | spl10_19 | ~spl10_2),
% 1.62/0.58    inference(avatar_split_clause,[],[f250,f87,f261,f83,f108])).
% 1.62/0.58  fof(f108,plain,(
% 1.62/0.58    spl10_4 <=> v1_relat_1(sK2)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.62/0.58  fof(f83,plain,(
% 1.62/0.58    spl10_1 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.62/0.58  fof(f87,plain,(
% 1.62/0.58    spl10_2 <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.62/0.58  fof(f250,plain,(
% 1.62/0.58    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2) | ~spl10_2),
% 1.62/0.58    inference(resolution,[],[f89,f51])).
% 1.62/0.58  fof(f51,plain,(
% 1.62/0.58    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.62/0.58    inference(equality_resolution,[],[f40])).
% 1.62/0.58  fof(f40,plain,(
% 1.62/0.58    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f26])).
% 1.62/0.58  fof(f89,plain,(
% 1.62/0.58    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0)) | ~spl10_2),
% 1.62/0.58    inference(avatar_component_clause,[],[f87])).
% 1.62/0.58  fof(f259,plain,(
% 1.62/0.58    ~spl10_4 | ~spl10_1 | spl10_18 | ~spl10_2),
% 1.62/0.58    inference(avatar_split_clause,[],[f249,f87,f256,f83,f108])).
% 1.62/0.58  fof(f249,plain,(
% 1.62/0.58    r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK0) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2) | ~spl10_2),
% 1.62/0.58    inference(resolution,[],[f89,f52])).
% 1.62/0.58  fof(f52,plain,(
% 1.62/0.58    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.62/0.58    inference(equality_resolution,[],[f39])).
% 1.62/0.58  fof(f39,plain,(
% 1.62/0.58    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f26])).
% 1.62/0.59  fof(f184,plain,(
% 1.62/0.59    spl10_8),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f183])).
% 1.62/0.59  fof(f183,plain,(
% 1.62/0.59    $false | spl10_8),
% 1.62/0.59    inference(resolution,[],[f137,f32])).
% 1.62/0.59  fof(f137,plain,(
% 1.62/0.59    ~v1_relat_1(sK3) | spl10_8),
% 1.62/0.59    inference(avatar_component_clause,[],[f135])).
% 1.62/0.59  fof(f156,plain,(
% 1.62/0.59    spl10_4),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f155])).
% 1.62/0.59  fof(f155,plain,(
% 1.62/0.59    $false | spl10_4),
% 1.62/0.59    inference(resolution,[],[f110,f31])).
% 1.62/0.59  fof(f31,plain,(
% 1.62/0.59    v1_relat_1(sK2)),
% 1.62/0.59    inference(cnf_transformation,[],[f17])).
% 1.62/0.59  fof(f110,plain,(
% 1.62/0.59    ~v1_relat_1(sK2) | spl10_4),
% 1.62/0.59    inference(avatar_component_clause,[],[f108])).
% 1.62/0.59  fof(f152,plain,(
% 1.62/0.59    spl10_1),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f150])).
% 1.62/0.59  fof(f150,plain,(
% 1.62/0.59    $false | spl10_1),
% 1.62/0.59    inference(resolution,[],[f85,f61])).
% 1.62/0.59  fof(f61,plain,(
% 1.62/0.59    ( ! [X5] : (v1_relat_1(k7_relat_1(sK2,X5))) )),
% 1.62/0.59    inference(resolution,[],[f31,f45])).
% 1.62/0.59  fof(f85,plain,(
% 1.62/0.59    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl10_1),
% 1.62/0.59    inference(avatar_component_clause,[],[f83])).
% 1.62/0.59  fof(f95,plain,(
% 1.62/0.59    ~spl10_1 | ~spl10_3),
% 1.62/0.59    inference(avatar_split_clause,[],[f81,f92,f83])).
% 1.62/0.59  fof(f81,plain,(
% 1.62/0.59    ~r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,sK1)) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 1.62/0.59    inference(resolution,[],[f35,f38])).
% 1.62/0.59  fof(f38,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f21])).
% 1.62/0.59  fof(f21,plain,(
% 1.62/0.59    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f20])).
% 1.62/0.59  fof(f20,plain,(
% 1.62/0.59    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f19,plain,(
% 1.62/0.59    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.62/0.59    inference(rectify,[],[f18])).
% 1.62/0.59  fof(f18,plain,(
% 1.62/0.59    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.62/0.59    inference(nnf_transformation,[],[f10])).
% 1.62/0.59  fof(f10,plain,(
% 1.62/0.59    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 1.62/0.59    inference(ennf_transformation,[],[f3])).
% 1.62/0.59  fof(f3,axiom,(
% 1.62/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 1.62/0.59  fof(f35,plain,(
% 1.62/0.59    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 1.62/0.59    inference(cnf_transformation,[],[f17])).
% 1.62/0.59  fof(f90,plain,(
% 1.62/0.59    ~spl10_1 | spl10_2),
% 1.62/0.59    inference(avatar_split_clause,[],[f80,f87,f83])).
% 1.62/0.59  fof(f80,plain,(
% 1.62/0.59    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 1.62/0.59    inference(resolution,[],[f35,f37])).
% 1.62/0.59  fof(f37,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f21])).
% 1.62/0.59  % SZS output end Proof for theBenchmark
% 1.62/0.59  % (25814)------------------------------
% 1.62/0.59  % (25814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (25814)Termination reason: Refutation
% 1.62/0.59  
% 1.62/0.59  % (25814)Memory used [KB]: 6524
% 1.62/0.59  % (25814)Time elapsed: 0.176 s
% 1.62/0.59  % (25814)------------------------------
% 1.62/0.59  % (25814)------------------------------
% 1.62/0.59  % (25798)Success in time 0.23 s
%------------------------------------------------------------------------------
