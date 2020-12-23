%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:31 EST 2020

% Result     : Theorem 6.96s
% Output     : Refutation 6.96s
% Verified   : 
% Statistics : Number of formulae       :  215 (2738 expanded)
%              Number of leaves         :   43 ( 919 expanded)
%              Depth                    :   17
%              Number of atoms          :  476 (4703 expanded)
%              Number of equality atoms :  214 (3147 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4483,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f105,f111,f279,f284,f312,f318,f382,f408,f416,f478,f1008,f1146,f1208,f1637,f1772,f1779,f1781,f1790,f1795,f3788,f4468,f4469,f4470,f4471,f4472,f4473,f4474,f4475,f4480])).

fof(f4480,plain,
    ( spl5_21
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f4453,f1634,f4477])).

fof(f4477,plain,
    ( spl5_21
  <=> r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f1634,plain,
    ( spl5_15
  <=> sP1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f4453,plain,
    ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f86,f1636,f56])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | ~ sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X11,X9) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
          & ( sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ~ sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X11,X9) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X10] :
          ( ( ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X10,X9) )
          & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X10,X9) ) )
     => ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
        & ( sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ? [X10] :
            ( ( ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X9) )
            & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ~ sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X11,X9) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ? [X10] :
            ( ( ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X9) )
            & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X9)
              | ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X9) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1636,plain,
    ( sP1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f1634])).

fof(f86,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8
          & X0 != X9 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | X0 = X9
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X8 != X10
          & X7 != X10
          & X6 != X10
          & X5 != X10
          & X4 != X10
          & X3 != X10
          & X2 != X10
          & X1 != X10
          & X0 != X10 ) )
      & ( X8 = X10
        | X7 = X10
        | X6 = X10
        | X5 = X10
        | X4 = X10
        | X3 = X10
        | X2 = X10
        | X1 = X10
        | X0 = X10
        | ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X8 != X10
          & X7 != X10
          & X6 != X10
          & X5 != X10
          & X4 != X10
          & X3 != X10
          & X2 != X10
          & X1 != X10
          & X0 != X10 ) )
      & ( X8 = X10
        | X7 = X10
        | X6 = X10
        | X5 = X10
        | X4 = X10
        | X3 = X10
        | X2 = X10
        | X1 = X10
        | X0 = X10
        | ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X8 = X10
        | X7 = X10
        | X6 = X10
        | X5 = X10
        | X4 = X10
        | X3 = X10
        | X2 = X10
        | X1 = X10
        | X0 = X10 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f4475,plain,
    ( spl5_20
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f4454,f1634,f4465])).

fof(f4465,plain,
    ( spl5_20
  <=> r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f4454,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f87,f1636,f56])).

fof(f87,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X2,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4474,plain,
    ( spl5_20
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f4455,f1634,f4465])).

fof(f4455,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f88,f1636,f56])).

fof(f88,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X3,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4473,plain,
    ( spl5_20
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f4456,f1634,f4465])).

fof(f4456,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f89,f1636,f56])).

fof(f89,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X4,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X4 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4472,plain,
    ( spl5_20
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f4457,f1634,f4465])).

fof(f4457,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f90,f1636,f56])).

fof(f90,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X5,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X5 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4471,plain,
    ( spl5_20
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f4458,f1634,f4465])).

fof(f4458,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f91,f1636,f56])).

fof(f91,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X6,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X6 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4470,plain,
    ( spl5_20
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f4459,f1634,f4465])).

fof(f4459,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f92,f1636,f56])).

fof(f92,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X7,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X7 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4469,plain,
    ( spl5_20
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f4460,f1634,f4465])).

fof(f4460,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f93,f1636,f56])).

fof(f93,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X8 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4468,plain,
    ( spl5_20
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f4461,f1634,f4465])).

fof(f4461,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f94,f1636,f56])).

fof(f94,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X9,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X9 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3788,plain,
    ( spl5_19
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f3762,f108,f3785])).

fof(f3785,plain,
    ( spl5_19
  <=> r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f108,plain,
    ( spl5_3
  <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f3762,plain,
    ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_3 ),
    inference(superposition,[],[f1651,f110])).

fof(f110,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f1651,plain,(
    ! [X0,X1] : r1_tarski(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) ),
    inference(superposition,[],[f775,f1199])).

fof(f1199,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k5_xboole_0(X5,X4) ),
    inference(forward_demodulation,[],[f1176,f209])).

fof(f209,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(forward_demodulation,[],[f196,f38])).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f196,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f120,f116])).

fof(f116,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f114,f81])).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f42,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f114,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(unit_resulting_resolution,[],[f80,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f47,f44])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f40,f71])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f120,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f49,f116])).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1176,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X5),X4) ),
    inference(superposition,[],[f1110,f120])).

fof(f1110,plain,(
    ! [X8,X9] : k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8 ),
    inference(superposition,[],[f975,f975])).

fof(f975,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,X2)) = X3 ),
    inference(superposition,[],[f392,f209])).

fof(f392,plain,(
    ! [X2,X3] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k5_xboole_0(X2,X3))) = X2 ),
    inference(forward_demodulation,[],[f360,f38])).

fof(f360,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k5_xboole_0(X2,X3))) ),
    inference(superposition,[],[f120,f123])).

fof(f123,plain,(
    ! [X6,X5] : k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6))) ),
    inference(superposition,[],[f49,f116])).

fof(f775,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),X0))) ),
    inference(superposition,[],[f486,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f486,plain,(
    ! [X4,X3] : r1_tarski(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X3,X4),X3))) ),
    inference(forward_demodulation,[],[f485,f49])).

fof(f485,plain,(
    ! [X4,X3] : r1_tarski(X3,k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(X3,X4)),X3)) ),
    inference(forward_demodulation,[],[f484,f209])).

fof(f484,plain,(
    ! [X4,X3] : r1_tarski(X3,k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(X3,X4)),X3))) ),
    inference(forward_demodulation,[],[f483,f120])).

fof(f483,plain,(
    ! [X4,X3] : r1_tarski(X3,k5_xboole_0(X3,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(X3,X4)),X3)))) ),
    inference(forward_demodulation,[],[f458,f49])).

fof(f458,plain,(
    ! [X4,X3] : r1_tarski(X3,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X3,X4))),X3))) ),
    inference(superposition,[],[f112,f136])).

fof(f136,plain,(
    ! [X0,X1] : k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X1 ),
    inference(superposition,[],[f81,f41])).

fof(f112,plain,(
    ! [X0,X1] : r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) ),
    inference(superposition,[],[f80,f41])).

fof(f1795,plain,
    ( spl5_18
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1752,f108,f1792])).

fof(f1792,plain,
    ( spl5_18
  <=> r1_tarski(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f1752,plain,
    ( r1_tarski(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))
    | ~ spl5_3 ),
    inference(superposition,[],[f127,f319])).

fof(f319,plain,
    ( ! [X0] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X0)))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f307,f49])).

fof(f307,plain,
    ( ! [X0] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),X0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)
    | ~ spl5_3 ),
    inference(superposition,[],[f49,f110])).

fof(f127,plain,(
    ! [X8,X7,X9] : r1_tarski(k5_xboole_0(X7,X8),k5_xboole_0(X7,k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,k5_xboole_0(X7,X8)))))) ),
    inference(superposition,[],[f80,f49])).

fof(f1790,plain,
    ( spl5_17
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1751,f108,f1787])).

fof(f1787,plain,
    ( spl5_17
  <=> k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f1751,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))
    | ~ spl5_3 ),
    inference(superposition,[],[f140,f319])).

fof(f140,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,X1) = k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,X1)))))) ),
    inference(superposition,[],[f81,f49])).

fof(f1781,plain,
    ( spl5_16
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1748,f108,f1769])).

fof(f1769,plain,
    ( spl5_16
  <=> k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f1748,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ spl5_3 ),
    inference(superposition,[],[f319,f975])).

fof(f1779,plain,
    ( spl5_16
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1778,f108,f1769])).

fof(f1778,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f1777,f209])).

fof(f1777,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f1776,f1291])).

fof(f1291,plain,(
    ! [X19,X17,X18] : k5_xboole_0(X17,k5_xboole_0(X18,X19)) = k5_xboole_0(X19,k5_xboole_0(X17,X18)) ),
    inference(superposition,[],[f1199,f49])).

fof(f1776,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f1745,f975])).

fof(f1745,plain,
    ( ! [X5] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X5)))
    | ~ spl5_3 ),
    inference(superposition,[],[f319,f123])).

fof(f1772,plain,
    ( spl5_16
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1767,f108,f1769])).

fof(f1767,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f1766,f209])).

fof(f1766,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f1738,f1291])).

fof(f1738,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0))
    | ~ spl5_3 ),
    inference(superposition,[],[f319,f116])).

fof(f1637,plain,
    ( spl5_15
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1626,f108,f1634])).

fof(f1626,plain,
    ( sP1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_3 ),
    inference(superposition,[],[f330,f110])).

fof(f330,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : sP1(X1,X2,X3,X4,X5,X6,X7,X8,X0,k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) ),
    inference(superposition,[],[f95,f41])).

fof(f95,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) != X9 ) ),
    inference(definition_unfolding,[],[f69,f78])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) ),
    inference(definition_unfolding,[],[f54,f71,f77])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(definition_folding,[],[f21,f23,f22])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ( X8 = X10
            | X7 = X10
            | X6 = X10
            | X5 = X10
            | X4 = X10
            | X3 = X10
            | X2 = X10
            | X1 = X10
            | X0 = X10 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X8 != X10
              & X7 != X10
              & X6 != X10
              & X5 != X10
              & X4 != X10
              & X3 != X10
              & X2 != X10
              & X1 != X10
              & X0 != X10 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).

fof(f1208,plain,
    ( spl5_14
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1203,f108,f1205])).

fof(f1205,plain,
    ( spl5_14
  <=> k1_xboole_0 = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f1203,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f1183,f116])).

fof(f1183,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_3 ),
    inference(superposition,[],[f1110,f110])).

fof(f1146,plain,
    ( spl5_13
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1115,f108,f1143])).

fof(f1143,plain,
    ( spl5_13
  <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f1115,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_3 ),
    inference(superposition,[],[f975,f110])).

fof(f1008,plain,
    ( spl5_12
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1003,f108,f1005])).

fof(f1005,plain,
    ( spl5_12
  <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f1003,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f970,f49])).

fof(f970,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | ~ spl5_3 ),
    inference(superposition,[],[f392,f110])).

fof(f478,plain,
    ( spl5_11
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f456,f108,f475])).

fof(f475,plain,
    ( spl5_11
  <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f456,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_3 ),
    inference(superposition,[],[f136,f110])).

fof(f416,plain,
    ( ~ spl5_10
    | spl5_5 ),
    inference(avatar_split_clause,[],[f411,f281,f413])).

fof(f413,plain,
    ( spl5_10
  <=> r2_hidden(sK2,k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f281,plain,
    ( spl5_5
  <=> sP0(sK2,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f411,plain,
    ( ~ r2_hidden(sK2,k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
    | spl5_5 ),
    inference(forward_demodulation,[],[f410,f209])).

fof(f410,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | spl5_5 ),
    inference(forward_demodulation,[],[f409,f120])).

fof(f409,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f95,f283,f55])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( ~ r2_hidden(X11,X9)
      | sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f283,plain,
    ( ~ sP0(sK2,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f281])).

fof(f408,plain,
    ( ~ spl5_9
    | spl5_4 ),
    inference(avatar_split_clause,[],[f403,f276,f405])).

fof(f405,plain,
    ( spl5_9
  <=> r2_hidden(sK3,k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f276,plain,
    ( spl5_4
  <=> sP0(sK3,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f403,plain,
    ( ~ r2_hidden(sK3,k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | spl5_4 ),
    inference(forward_demodulation,[],[f402,f209])).

fof(f402,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | spl5_4 ),
    inference(forward_demodulation,[],[f401,f120])).

fof(f401,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f95,f278,f55])).

fof(f278,plain,
    ( ~ sP0(sK3,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f276])).

fof(f382,plain,
    ( spl5_8
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f377,f108,f379])).

fof(f379,plain,
    ( spl5_8
  <=> k1_xboole_0 = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f377,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f349,f49])).

fof(f349,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | ~ spl5_3 ),
    inference(superposition,[],[f123,f110])).

fof(f318,plain,
    ( spl5_7
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f313,f108,f315])).

fof(f315,plain,
    ( spl5_7
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f313,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f306,f116])).

fof(f306,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_3 ),
    inference(superposition,[],[f120,f110])).

fof(f312,plain,
    ( spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f305,f108,f309])).

fof(f309,plain,
    ( spl5_6
  <=> r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f305,plain,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_3 ),
    inference(superposition,[],[f112,f110])).

fof(f284,plain,
    ( ~ spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f246,f97,f281])).

fof(f97,plain,
    ( spl5_1
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f246,plain,
    ( ~ sP0(sK2,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f99,f99,f99,f99,f99,f99,f99,f99,f99,f59])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X5
      | X0 = X6
      | X0 = X7
      | X0 = X8
      | X0 = X9
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f99,plain,
    ( sK2 != sK3
    | spl5_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f279,plain,
    ( ~ spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f247,f97,f276])).

fof(f247,plain,
    ( ~ sP0(sK3,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f99,f99,f99,f99,f99,f99,f99,f99,f99,f59])).

fof(f111,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f106,f102,f108])).

fof(f102,plain,
    ( spl5_2
  <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f106,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f104,f41])).

fof(f104,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f105,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f79,f102])).

fof(f79,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f36,f77,f71,f77,f77])).

fof(f36,plain,(
    k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK2 != sK3
    & k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK2 != sK3
      & k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f100,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f37,f97])).

fof(f37,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:21:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (27009)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (27017)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (27006)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (27025)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (27011)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (27008)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (27003)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (27005)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (27003)Refutation not found, incomplete strategy% (27003)------------------------------
% 0.22/0.54  % (27003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27003)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27003)Memory used [KB]: 1663
% 0.22/0.54  % (27003)Time elapsed: 0.090 s
% 0.22/0.54  % (27003)------------------------------
% 0.22/0.54  % (27003)------------------------------
% 0.22/0.54  % (27011)Refutation not found, incomplete strategy% (27011)------------------------------
% 0.22/0.54  % (27011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27011)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27011)Memory used [KB]: 10746
% 0.22/0.54  % (27011)Time elapsed: 0.123 s
% 0.22/0.54  % (27011)------------------------------
% 0.22/0.54  % (27011)------------------------------
% 0.22/0.54  % (27012)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (27005)Refutation not found, incomplete strategy% (27005)------------------------------
% 0.22/0.54  % (27005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27005)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27005)Memory used [KB]: 10746
% 0.22/0.54  % (27005)Time elapsed: 0.123 s
% 0.22/0.54  % (27005)------------------------------
% 0.22/0.54  % (27005)------------------------------
% 0.22/0.54  % (27004)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (27026)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (27012)Refutation not found, incomplete strategy% (27012)------------------------------
% 0.22/0.54  % (27012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27012)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27012)Memory used [KB]: 10618
% 0.22/0.54  % (27012)Time elapsed: 0.124 s
% 0.22/0.54  % (27012)------------------------------
% 0.22/0.54  % (27012)------------------------------
% 0.22/0.55  % (27032)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (27010)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (27028)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (27007)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (27023)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (27013)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (27020)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (27018)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (27024)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (27013)Refutation not found, incomplete strategy% (27013)------------------------------
% 0.22/0.55  % (27013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27013)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (27013)Memory used [KB]: 10618
% 0.22/0.55  % (27013)Time elapsed: 0.135 s
% 0.22/0.55  % (27013)------------------------------
% 0.22/0.55  % (27013)------------------------------
% 0.22/0.55  % (27020)Refutation not found, incomplete strategy% (27020)------------------------------
% 0.22/0.55  % (27020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27020)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (27020)Memory used [KB]: 10618
% 0.22/0.55  % (27020)Time elapsed: 0.138 s
% 0.22/0.55  % (27020)------------------------------
% 0.22/0.55  % (27020)------------------------------
% 0.22/0.55  % (27015)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (27029)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (27027)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (27019)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.56  % (27021)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.56  % (27031)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.56  % (27016)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.65/0.58  % (27024)Refutation not found, incomplete strategy% (27024)------------------------------
% 1.65/0.58  % (27024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (27024)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.58  
% 1.65/0.58  % (27024)Memory used [KB]: 1791
% 1.65/0.58  % (27024)Time elapsed: 0.168 s
% 1.65/0.58  % (27024)------------------------------
% 1.65/0.58  % (27024)------------------------------
% 1.65/0.59  % (27007)Refutation not found, incomplete strategy% (27007)------------------------------
% 1.65/0.59  % (27007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (27007)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.59  
% 1.65/0.59  % (27007)Memory used [KB]: 6396
% 1.65/0.59  % (27007)Time elapsed: 0.165 s
% 1.65/0.59  % (27007)------------------------------
% 1.65/0.59  % (27007)------------------------------
% 1.65/0.61  % (27028)Refutation not found, incomplete strategy% (27028)------------------------------
% 1.65/0.61  % (27028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.61  % (27028)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.61  
% 1.65/0.61  % (27028)Memory used [KB]: 6524
% 1.65/0.61  % (27028)Time elapsed: 0.181 s
% 1.65/0.61  % (27028)------------------------------
% 1.65/0.61  % (27028)------------------------------
% 1.65/0.61  % (27014)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.65/0.61  % (27014)Refutation not found, incomplete strategy% (27014)------------------------------
% 1.65/0.61  % (27014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.61  % (27014)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.61  
% 1.65/0.61  % (27014)Memory used [KB]: 10618
% 1.65/0.61  % (27014)Time elapsed: 0.168 s
% 1.65/0.61  % (27014)------------------------------
% 1.65/0.61  % (27014)------------------------------
% 1.65/0.62  % (27030)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.65/0.62  % (27022)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.35/0.71  % (27039)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.35/0.72  % (27036)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.35/0.72  % (27036)Refutation not found, incomplete strategy% (27036)------------------------------
% 2.35/0.72  % (27036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.35/0.72  % (27036)Termination reason: Refutation not found, incomplete strategy
% 2.35/0.72  
% 2.35/0.72  % (27036)Memory used [KB]: 6140
% 2.35/0.72  % (27036)Time elapsed: 0.140 s
% 2.35/0.72  % (27036)------------------------------
% 2.35/0.72  % (27036)------------------------------
% 2.56/0.72  % (27040)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.71/0.75  % (27049)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.71/0.76  % (27044)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.71/0.77  % (27038)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.71/0.77  % (27064)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.71/0.79  % (27063)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.71/0.80  % (27037)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.13/0.84  % (27008)Time limit reached!
% 3.13/0.84  % (27008)------------------------------
% 3.13/0.84  % (27008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.13/0.84  % (27008)Termination reason: Time limit
% 3.13/0.84  
% 3.13/0.84  % (27008)Memory used [KB]: 9083
% 3.13/0.84  % (27008)Time elapsed: 0.434 s
% 3.13/0.84  % (27008)------------------------------
% 3.13/0.84  % (27008)------------------------------
% 3.47/0.88  % (27052)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 3.47/0.89  % (27070)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 3.47/0.92  % (27015)Time limit reached!
% 3.47/0.92  % (27015)------------------------------
% 3.47/0.92  % (27015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.92  % (27015)Termination reason: Time limit
% 3.47/0.92  
% 3.47/0.92  % (27015)Memory used [KB]: 8699
% 3.47/0.92  % (27015)Time elapsed: 0.506 s
% 3.47/0.92  % (27015)------------------------------
% 3.47/0.92  % (27015)------------------------------
% 3.47/0.93  % (27004)Time limit reached!
% 3.47/0.93  % (27004)------------------------------
% 3.47/0.93  % (27004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.93  % (27004)Termination reason: Time limit
% 3.47/0.93  
% 3.47/0.93  % (27004)Memory used [KB]: 8699
% 3.47/0.93  % (27004)Time elapsed: 0.514 s
% 3.47/0.93  % (27004)------------------------------
% 3.47/0.93  % (27004)------------------------------
% 4.08/0.98  % (27039)Time limit reached!
% 4.08/0.98  % (27039)------------------------------
% 4.08/0.98  % (27039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.08/0.98  % (27039)Termination reason: Time limit
% 4.08/0.98  % (27039)Termination phase: Saturation
% 4.08/0.98  
% 4.08/0.98  % (27039)Memory used [KB]: 6908
% 4.08/0.98  % (27039)Time elapsed: 0.400 s
% 4.08/0.98  % (27039)------------------------------
% 4.08/0.98  % (27039)------------------------------
% 4.08/1.01  % (27040)Time limit reached!
% 4.08/1.01  % (27040)------------------------------
% 4.08/1.01  % (27040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.08/1.01  % (27040)Termination reason: Time limit
% 4.08/1.01  
% 4.08/1.02  % (27040)Memory used [KB]: 13304
% 4.08/1.02  % (27040)Time elapsed: 0.431 s
% 4.08/1.02  % (27040)------------------------------
% 4.08/1.02  % (27040)------------------------------
% 4.45/1.02  % (27071)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 4.45/1.03  % (27019)Time limit reached!
% 4.45/1.03  % (27019)------------------------------
% 4.45/1.03  % (27019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/1.03  % (27019)Termination reason: Time limit
% 4.45/1.03  % (27019)Termination phase: Saturation
% 4.45/1.03  
% 4.45/1.03  % (27019)Memory used [KB]: 12409
% 4.45/1.03  % (27019)Time elapsed: 0.600 s
% 4.45/1.03  % (27019)------------------------------
% 4.45/1.03  % (27019)------------------------------
% 5.40/1.06  % (27010)Time limit reached!
% 5.40/1.06  % (27010)------------------------------
% 5.40/1.06  % (27010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.40/1.06  % (27010)Termination reason: Time limit
% 5.40/1.06  
% 5.40/1.06  % (27010)Memory used [KB]: 10618
% 5.40/1.06  % (27010)Time elapsed: 0.609 s
% 5.40/1.06  % (27010)------------------------------
% 5.40/1.06  % (27010)------------------------------
% 5.40/1.07  % (27037)Refutation not found, incomplete strategy% (27037)------------------------------
% 5.40/1.07  % (27037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.40/1.07  % (27037)Termination reason: Refutation not found, incomplete strategy
% 5.40/1.07  
% 5.40/1.07  % (27037)Memory used [KB]: 6140
% 5.40/1.07  % (27037)Time elapsed: 0.469 s
% 5.40/1.07  % (27037)------------------------------
% 5.40/1.07  % (27037)------------------------------
% 5.40/1.11  % (27073)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.40/1.11  % (27031)Time limit reached!
% 5.40/1.11  % (27031)------------------------------
% 5.40/1.11  % (27031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.40/1.11  % (27031)Termination reason: Time limit
% 5.40/1.11  % (27031)Termination phase: Saturation
% 5.40/1.11  
% 5.40/1.11  % (27031)Memory used [KB]: 7291
% 5.40/1.11  % (27031)Time elapsed: 0.600 s
% 5.40/1.11  % (27031)------------------------------
% 5.40/1.11  % (27031)------------------------------
% 5.40/1.11  % (27072)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 6.02/1.15  % (27076)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.02/1.16  % (27074)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 6.02/1.17  % (27075)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 6.02/1.19  % (27077)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.47/1.22  % (27078)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.96/1.27  % (27044)Refutation found. Thanks to Tanya!
% 6.96/1.27  % SZS status Theorem for theBenchmark
% 6.96/1.27  % (27080)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 6.96/1.28  % SZS output start Proof for theBenchmark
% 6.96/1.28  fof(f4483,plain,(
% 6.96/1.28    $false),
% 6.96/1.28    inference(avatar_sat_refutation,[],[f100,f105,f111,f279,f284,f312,f318,f382,f408,f416,f478,f1008,f1146,f1208,f1637,f1772,f1779,f1781,f1790,f1795,f3788,f4468,f4469,f4470,f4471,f4472,f4473,f4474,f4475,f4480])).
% 6.96/1.28  fof(f4480,plain,(
% 6.96/1.28    spl5_21 | ~spl5_15),
% 6.96/1.28    inference(avatar_split_clause,[],[f4453,f1634,f4477])).
% 6.96/1.28  fof(f4477,plain,(
% 6.96/1.28    spl5_21 <=> r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 6.96/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 6.96/1.28  fof(f1634,plain,(
% 6.96/1.28    spl5_15 <=> sP1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 6.96/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 6.96/1.28  fof(f4453,plain,(
% 6.96/1.28    r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_15),
% 6.96/1.28    inference(unit_resulting_resolution,[],[f86,f1636,f56])).
% 6.96/1.28  fof(f56,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X11,X9)) )),
% 6.96/1.28    inference(cnf_transformation,[],[f31])).
% 6.96/1.28  fof(f31,plain,(
% 6.96/1.28    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ((~sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 6.96/1.28    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 6.96/1.28  fof(f30,plain,(
% 6.96/1.28    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9))) => ((~sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9))))),
% 6.96/1.28    introduced(choice_axiom,[])).
% 6.96/1.28  fof(f29,plain,(
% 6.96/1.28    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 6.96/1.28    inference(rectify,[],[f28])).
% 6.96/1.28  fof(f28,plain,(
% 6.96/1.28    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 6.96/1.28    inference(nnf_transformation,[],[f23])).
% 6.96/1.28  fof(f23,plain,(
% 6.96/1.28    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) <=> ! [X10] : (r2_hidden(X10,X9) <=> sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 6.96/1.28    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 6.96/1.28  fof(f1636,plain,(
% 6.96/1.28    sP1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_15),
% 6.96/1.28    inference(avatar_component_clause,[],[f1634])).
% 6.96/1.28  fof(f86,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 6.96/1.28    inference(equality_resolution,[],[f68])).
% 6.96/1.28  fof(f68,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X1) )),
% 6.96/1.28    inference(cnf_transformation,[],[f34])).
% 6.96/1.28  fof(f34,plain,(
% 6.96/1.28    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8 & X0 != X9)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 6.96/1.28    inference(rectify,[],[f33])).
% 6.96/1.28  fof(f33,plain,(
% 6.96/1.28    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 6.96/1.28    inference(flattening,[],[f32])).
% 6.96/1.28  fof(f32,plain,(
% 6.96/1.28    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 6.96/1.28    inference(nnf_transformation,[],[f22])).
% 6.96/1.28  fof(f22,plain,(
% 6.96/1.28    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10))),
% 6.96/1.28    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 6.96/1.28  fof(f4475,plain,(
% 6.96/1.28    spl5_20 | ~spl5_15),
% 6.96/1.28    inference(avatar_split_clause,[],[f4454,f1634,f4465])).
% 6.96/1.28  fof(f4465,plain,(
% 6.96/1.28    spl5_20 <=> r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 6.96/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 6.96/1.28  fof(f4454,plain,(
% 6.96/1.28    r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_15),
% 6.96/1.28    inference(unit_resulting_resolution,[],[f87,f1636,f56])).
% 6.96/1.28  fof(f87,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X2,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 6.96/1.28    inference(equality_resolution,[],[f67])).
% 6.96/1.28  fof(f67,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X2) )),
% 6.96/1.28    inference(cnf_transformation,[],[f34])).
% 6.96/1.28  fof(f4474,plain,(
% 6.96/1.28    spl5_20 | ~spl5_15),
% 6.96/1.28    inference(avatar_split_clause,[],[f4455,f1634,f4465])).
% 6.96/1.28  fof(f4455,plain,(
% 6.96/1.28    r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_15),
% 6.96/1.28    inference(unit_resulting_resolution,[],[f88,f1636,f56])).
% 6.96/1.28  fof(f88,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X3,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 6.96/1.28    inference(equality_resolution,[],[f66])).
% 6.96/1.28  fof(f66,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X3) )),
% 6.96/1.28    inference(cnf_transformation,[],[f34])).
% 6.96/1.28  fof(f4473,plain,(
% 6.96/1.28    spl5_20 | ~spl5_15),
% 6.96/1.28    inference(avatar_split_clause,[],[f4456,f1634,f4465])).
% 6.96/1.28  fof(f4456,plain,(
% 6.96/1.28    r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_15),
% 6.96/1.28    inference(unit_resulting_resolution,[],[f89,f1636,f56])).
% 6.96/1.28  fof(f89,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X4,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 6.96/1.28    inference(equality_resolution,[],[f65])).
% 6.96/1.28  fof(f65,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X4) )),
% 6.96/1.28    inference(cnf_transformation,[],[f34])).
% 6.96/1.28  fof(f4472,plain,(
% 6.96/1.28    spl5_20 | ~spl5_15),
% 6.96/1.28    inference(avatar_split_clause,[],[f4457,f1634,f4465])).
% 6.96/1.28  fof(f4457,plain,(
% 6.96/1.28    r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_15),
% 6.96/1.28    inference(unit_resulting_resolution,[],[f90,f1636,f56])).
% 6.96/1.28  fof(f90,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X5,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 6.96/1.28    inference(equality_resolution,[],[f64])).
% 6.96/1.28  fof(f64,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X5) )),
% 6.96/1.28    inference(cnf_transformation,[],[f34])).
% 6.96/1.28  fof(f4471,plain,(
% 6.96/1.28    spl5_20 | ~spl5_15),
% 6.96/1.28    inference(avatar_split_clause,[],[f4458,f1634,f4465])).
% 6.96/1.28  fof(f4458,plain,(
% 6.96/1.28    r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_15),
% 6.96/1.28    inference(unit_resulting_resolution,[],[f91,f1636,f56])).
% 6.96/1.28  fof(f91,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X6,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 6.96/1.28    inference(equality_resolution,[],[f63])).
% 6.96/1.28  fof(f63,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X6) )),
% 6.96/1.28    inference(cnf_transformation,[],[f34])).
% 6.96/1.28  fof(f4470,plain,(
% 6.96/1.28    spl5_20 | ~spl5_15),
% 6.96/1.28    inference(avatar_split_clause,[],[f4459,f1634,f4465])).
% 6.96/1.28  fof(f4459,plain,(
% 6.96/1.28    r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_15),
% 6.96/1.28    inference(unit_resulting_resolution,[],[f92,f1636,f56])).
% 6.96/1.28  fof(f92,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X7,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 6.96/1.28    inference(equality_resolution,[],[f62])).
% 6.96/1.28  fof(f62,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X7) )),
% 6.96/1.28    inference(cnf_transformation,[],[f34])).
% 6.96/1.28  fof(f4469,plain,(
% 6.96/1.28    spl5_20 | ~spl5_15),
% 6.96/1.28    inference(avatar_split_clause,[],[f4460,f1634,f4465])).
% 6.96/1.28  fof(f4460,plain,(
% 6.96/1.28    r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_15),
% 6.96/1.28    inference(unit_resulting_resolution,[],[f93,f1636,f56])).
% 6.96/1.28  fof(f93,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 6.96/1.28    inference(equality_resolution,[],[f61])).
% 6.96/1.28  fof(f61,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X8) )),
% 6.96/1.28    inference(cnf_transformation,[],[f34])).
% 6.96/1.28  fof(f4468,plain,(
% 6.96/1.28    spl5_20 | ~spl5_15),
% 6.96/1.28    inference(avatar_split_clause,[],[f4461,f1634,f4465])).
% 6.96/1.28  fof(f4461,plain,(
% 6.96/1.28    r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_15),
% 6.96/1.28    inference(unit_resulting_resolution,[],[f94,f1636,f56])).
% 6.96/1.28  fof(f94,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X9,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 6.96/1.28    inference(equality_resolution,[],[f60])).
% 6.96/1.28  fof(f60,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X9) )),
% 6.96/1.28    inference(cnf_transformation,[],[f34])).
% 6.96/1.28  fof(f3788,plain,(
% 6.96/1.28    spl5_19 | ~spl5_3),
% 6.96/1.28    inference(avatar_split_clause,[],[f3762,f108,f3785])).
% 6.96/1.28  fof(f3785,plain,(
% 6.96/1.28    spl5_19 <=> r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 6.96/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 6.96/1.28  fof(f108,plain,(
% 6.96/1.28    spl5_3 <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))),
% 6.96/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 6.96/1.28  fof(f3762,plain,(
% 6.96/1.28    r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_3),
% 6.96/1.28    inference(superposition,[],[f1651,f110])).
% 6.96/1.28  fof(f110,plain,(
% 6.96/1.28    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) | ~spl5_3),
% 6.96/1.28    inference(avatar_component_clause,[],[f108])).
% 6.96/1.28  fof(f1651,plain,(
% 6.96/1.28    ( ! [X0,X1] : (r1_tarski(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))) )),
% 6.96/1.28    inference(superposition,[],[f775,f1199])).
% 6.96/1.28  fof(f1199,plain,(
% 6.96/1.28    ( ! [X4,X5] : (k5_xboole_0(X4,X5) = k5_xboole_0(X5,X4)) )),
% 6.96/1.28    inference(forward_demodulation,[],[f1176,f209])).
% 6.96/1.28  fof(f209,plain,(
% 6.96/1.28    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 6.96/1.28    inference(forward_demodulation,[],[f196,f38])).
% 6.96/1.28  fof(f38,plain,(
% 6.96/1.28    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.96/1.28    inference(cnf_transformation,[],[f5])).
% 6.96/1.28  fof(f5,axiom,(
% 6.96/1.28    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 6.96/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 6.96/1.28  fof(f196,plain,(
% 6.96/1.28    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k1_xboole_0)) )),
% 6.96/1.28    inference(superposition,[],[f120,f116])).
% 6.96/1.28  fof(f116,plain,(
% 6.96/1.28    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 6.96/1.28    inference(forward_demodulation,[],[f114,f81])).
% 6.96/1.28  fof(f81,plain,(
% 6.96/1.28    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 6.96/1.28    inference(definition_unfolding,[],[f42,f71])).
% 6.96/1.28  fof(f71,plain,(
% 6.96/1.28    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 6.96/1.28    inference(definition_unfolding,[],[f45,f44])).
% 6.96/1.28  fof(f44,plain,(
% 6.96/1.28    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.96/1.28    inference(cnf_transformation,[],[f3])).
% 6.96/1.28  fof(f3,axiom,(
% 6.96/1.28    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.96/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 6.96/1.28  fof(f45,plain,(
% 6.96/1.28    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.96/1.28    inference(cnf_transformation,[],[f8])).
% 6.96/1.28  fof(f8,axiom,(
% 6.96/1.28    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 6.96/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 6.96/1.28  fof(f42,plain,(
% 6.96/1.28    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 6.96/1.28    inference(cnf_transformation,[],[f4])).
% 6.96/1.28  fof(f4,axiom,(
% 6.96/1.28    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 6.96/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 6.96/1.28  fof(f114,plain,(
% 6.96/1.28    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 6.96/1.28    inference(unit_resulting_resolution,[],[f80,f82])).
% 6.96/1.28  fof(f82,plain,(
% 6.96/1.28    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.96/1.28    inference(definition_unfolding,[],[f47,f44])).
% 6.96/1.28  fof(f47,plain,(
% 6.96/1.28    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 6.96/1.28    inference(cnf_transformation,[],[f27])).
% 6.96/1.28  fof(f27,plain,(
% 6.96/1.28    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 6.96/1.28    inference(nnf_transformation,[],[f2])).
% 6.96/1.28  fof(f2,axiom,(
% 6.96/1.28    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 6.96/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 6.96/1.28  fof(f80,plain,(
% 6.96/1.28    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 6.96/1.28    inference(definition_unfolding,[],[f40,f71])).
% 6.96/1.28  fof(f40,plain,(
% 6.96/1.28    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 6.96/1.28    inference(cnf_transformation,[],[f6])).
% 6.96/1.28  fof(f6,axiom,(
% 6.96/1.28    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 6.96/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 6.96/1.28  fof(f120,plain,(
% 6.96/1.28    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 6.96/1.28    inference(superposition,[],[f49,f116])).
% 6.96/1.28  fof(f49,plain,(
% 6.96/1.28    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 6.96/1.28    inference(cnf_transformation,[],[f7])).
% 6.96/1.28  fof(f7,axiom,(
% 6.96/1.28    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 6.96/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 6.96/1.28  fof(f1176,plain,(
% 6.96/1.28    ( ! [X4,X5] : (k5_xboole_0(X4,X5) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X5),X4)) )),
% 6.96/1.28    inference(superposition,[],[f1110,f120])).
% 6.96/1.28  fof(f1110,plain,(
% 6.96/1.28    ( ! [X8,X9] : (k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8) )),
% 6.96/1.28    inference(superposition,[],[f975,f975])).
% 6.96/1.28  fof(f975,plain,(
% 6.96/1.28    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,X2)) = X3) )),
% 6.96/1.28    inference(superposition,[],[f392,f209])).
% 6.96/1.28  fof(f392,plain,(
% 6.96/1.28    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k5_xboole_0(X2,X3))) = X2) )),
% 6.96/1.28    inference(forward_demodulation,[],[f360,f38])).
% 6.96/1.28  fof(f360,plain,(
% 6.96/1.28    ( ! [X2,X3] : (k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k5_xboole_0(X2,X3)))) )),
% 6.96/1.28    inference(superposition,[],[f120,f123])).
% 6.96/1.28  fof(f123,plain,(
% 6.96/1.28    ( ! [X6,X5] : (k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6)))) )),
% 6.96/1.28    inference(superposition,[],[f49,f116])).
% 6.96/1.28  fof(f775,plain,(
% 6.96/1.28    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),X0)))) )),
% 6.96/1.28    inference(superposition,[],[f486,f41])).
% 6.96/1.28  fof(f41,plain,(
% 6.96/1.28    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.96/1.28    inference(cnf_transformation,[],[f1])).
% 6.96/1.28  fof(f1,axiom,(
% 6.96/1.28    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.96/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.96/1.28  fof(f486,plain,(
% 6.96/1.28    ( ! [X4,X3] : (r1_tarski(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X3,X4),X3)))) )),
% 6.96/1.28    inference(forward_demodulation,[],[f485,f49])).
% 6.96/1.28  fof(f485,plain,(
% 6.96/1.28    ( ! [X4,X3] : (r1_tarski(X3,k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(X3,X4)),X3))) )),
% 6.96/1.28    inference(forward_demodulation,[],[f484,f209])).
% 6.96/1.28  fof(f484,plain,(
% 6.96/1.28    ( ! [X4,X3] : (r1_tarski(X3,k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(X3,X4)),X3)))) )),
% 6.96/1.28    inference(forward_demodulation,[],[f483,f120])).
% 6.96/1.28  fof(f483,plain,(
% 6.96/1.28    ( ! [X4,X3] : (r1_tarski(X3,k5_xboole_0(X3,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(X3,X4)),X3))))) )),
% 6.96/1.28    inference(forward_demodulation,[],[f458,f49])).
% 6.96/1.28  fof(f458,plain,(
% 6.96/1.28    ( ! [X4,X3] : (r1_tarski(X3,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X3,X4))),X3)))) )),
% 6.96/1.28    inference(superposition,[],[f112,f136])).
% 6.96/1.28  fof(f136,plain,(
% 6.96/1.28    ( ! [X0,X1] : (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X1) )),
% 6.96/1.28    inference(superposition,[],[f81,f41])).
% 6.96/1.28  fof(f112,plain,(
% 6.96/1.28    ( ! [X0,X1] : (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) )),
% 6.96/1.28    inference(superposition,[],[f80,f41])).
% 6.96/1.28  fof(f1795,plain,(
% 6.96/1.28    spl5_18 | ~spl5_3),
% 6.96/1.28    inference(avatar_split_clause,[],[f1752,f108,f1792])).
% 6.96/1.28  fof(f1792,plain,(
% 6.96/1.28    spl5_18 <=> r1_tarski(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))),
% 6.96/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 6.96/1.28  fof(f1752,plain,(
% 6.96/1.28    r1_tarski(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) | ~spl5_3),
% 6.96/1.28    inference(superposition,[],[f127,f319])).
% 6.96/1.28  fof(f319,plain,(
% 6.96/1.28    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X0)))) ) | ~spl5_3),
% 6.96/1.28    inference(forward_demodulation,[],[f307,f49])).
% 6.96/1.28  fof(f307,plain,(
% 6.96/1.28    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),X0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)) ) | ~spl5_3),
% 6.96/1.28    inference(superposition,[],[f49,f110])).
% 6.96/1.28  fof(f127,plain,(
% 6.96/1.28    ( ! [X8,X7,X9] : (r1_tarski(k5_xboole_0(X7,X8),k5_xboole_0(X7,k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,k5_xboole_0(X7,X8))))))) )),
% 6.96/1.28    inference(superposition,[],[f80,f49])).
% 6.96/1.28  fof(f1790,plain,(
% 6.96/1.28    spl5_17 | ~spl5_3),
% 6.96/1.28    inference(avatar_split_clause,[],[f1751,f108,f1787])).
% 6.96/1.28  fof(f1787,plain,(
% 6.96/1.28    spl5_17 <=> k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))),
% 6.96/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 6.96/1.28  fof(f1751,plain,(
% 6.96/1.28    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) | ~spl5_3),
% 6.96/1.28    inference(superposition,[],[f140,f319])).
% 6.96/1.28  fof(f140,plain,(
% 6.96/1.28    ( ! [X2,X0,X1] : (k5_xboole_0(X0,X1) = k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,X1))))))) )),
% 6.96/1.28    inference(superposition,[],[f81,f49])).
% 6.96/1.28  fof(f1781,plain,(
% 6.96/1.28    spl5_16 | ~spl5_3),
% 6.96/1.28    inference(avatar_split_clause,[],[f1748,f108,f1769])).
% 6.96/1.28  fof(f1769,plain,(
% 6.96/1.28    spl5_16 <=> k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),
% 6.96/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 6.96/1.28  fof(f1748,plain,(
% 6.96/1.28    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~spl5_3),
% 6.96/1.28    inference(superposition,[],[f319,f975])).
% 6.96/1.28  fof(f1779,plain,(
% 6.96/1.28    spl5_16 | ~spl5_3),
% 6.96/1.28    inference(avatar_split_clause,[],[f1778,f108,f1769])).
% 6.96/1.28  fof(f1778,plain,(
% 6.96/1.28    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~spl5_3),
% 6.96/1.28    inference(forward_demodulation,[],[f1777,f209])).
% 6.96/1.28  fof(f1777,plain,(
% 6.96/1.28    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) | ~spl5_3),
% 6.96/1.28    inference(forward_demodulation,[],[f1776,f1291])).
% 6.96/1.28  fof(f1291,plain,(
% 6.96/1.28    ( ! [X19,X17,X18] : (k5_xboole_0(X17,k5_xboole_0(X18,X19)) = k5_xboole_0(X19,k5_xboole_0(X17,X18))) )),
% 6.96/1.28    inference(superposition,[],[f1199,f49])).
% 6.96/1.28  fof(f1776,plain,(
% 6.96/1.28    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0)) | ~spl5_3),
% 6.96/1.28    inference(forward_demodulation,[],[f1745,f975])).
% 6.96/1.28  fof(f1745,plain,(
% 6.96/1.28    ( ! [X5] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X5)))) ) | ~spl5_3),
% 6.96/1.28    inference(superposition,[],[f319,f123])).
% 6.96/1.28  fof(f1772,plain,(
% 6.96/1.28    spl5_16 | ~spl5_3),
% 6.96/1.28    inference(avatar_split_clause,[],[f1767,f108,f1769])).
% 6.96/1.28  fof(f1767,plain,(
% 6.96/1.28    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~spl5_3),
% 6.96/1.28    inference(forward_demodulation,[],[f1766,f209])).
% 6.96/1.28  fof(f1766,plain,(
% 6.96/1.28    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) | ~spl5_3),
% 6.96/1.28    inference(forward_demodulation,[],[f1738,f1291])).
% 6.96/1.28  fof(f1738,plain,(
% 6.96/1.28    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0)) | ~spl5_3),
% 6.96/1.28    inference(superposition,[],[f319,f116])).
% 6.96/1.28  fof(f1637,plain,(
% 6.96/1.28    spl5_15 | ~spl5_3),
% 6.96/1.28    inference(avatar_split_clause,[],[f1626,f108,f1634])).
% 6.96/1.28  fof(f1626,plain,(
% 6.96/1.28    sP1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_3),
% 6.96/1.28    inference(superposition,[],[f330,f110])).
% 6.96/1.28  fof(f330,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X1,X2,X3,X4,X5,X6,X7,X8,X0,k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))) )),
% 6.96/1.28    inference(superposition,[],[f95,f41])).
% 6.96/1.28  fof(f95,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))))) )),
% 6.96/1.28    inference(equality_resolution,[],[f85])).
% 6.96/1.28  fof(f85,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) != X9) )),
% 6.96/1.28    inference(definition_unfolding,[],[f69,f78])).
% 6.96/1.28  fof(f78,plain,(
% 6.96/1.28    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) )),
% 6.96/1.28    inference(definition_unfolding,[],[f54,f71,f77])).
% 6.96/1.28  fof(f77,plain,(
% 6.96/1.28    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 6.96/1.28    inference(definition_unfolding,[],[f39,f76])).
% 6.96/1.28  fof(f76,plain,(
% 6.96/1.28    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 6.96/1.28    inference(definition_unfolding,[],[f43,f75])).
% 6.96/1.28  fof(f75,plain,(
% 6.96/1.28    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 6.96/1.28    inference(definition_unfolding,[],[f48,f74])).
% 6.96/1.28  fof(f74,plain,(
% 6.96/1.28    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 6.96/1.28    inference(definition_unfolding,[],[f50,f73])).
% 6.96/1.28  fof(f73,plain,(
% 6.96/1.28    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 6.96/1.28    inference(definition_unfolding,[],[f51,f72])).
% 6.96/1.28  fof(f72,plain,(
% 6.96/1.28    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 6.96/1.28    inference(definition_unfolding,[],[f52,f53])).
% 6.96/1.29  fof(f53,plain,(
% 6.96/1.29    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 6.96/1.29    inference(cnf_transformation,[],[f17])).
% 6.96/1.29  fof(f17,axiom,(
% 6.96/1.29    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 6.96/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 6.96/1.29  fof(f52,plain,(
% 6.96/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 6.96/1.29    inference(cnf_transformation,[],[f16])).
% 6.96/1.29  fof(f16,axiom,(
% 6.96/1.29    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 6.96/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 6.96/1.29  fof(f51,plain,(
% 6.96/1.29    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 6.96/1.29    inference(cnf_transformation,[],[f15])).
% 6.96/1.29  fof(f15,axiom,(
% 6.96/1.29    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 6.96/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 6.96/1.29  fof(f50,plain,(
% 6.96/1.29    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 6.96/1.29    inference(cnf_transformation,[],[f14])).
% 6.96/1.29  fof(f14,axiom,(
% 6.96/1.29    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 6.96/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 6.96/1.29  fof(f48,plain,(
% 6.96/1.29    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 6.96/1.29    inference(cnf_transformation,[],[f13])).
% 6.96/1.29  fof(f13,axiom,(
% 6.96/1.29    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 6.96/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 6.96/1.29  fof(f43,plain,(
% 6.96/1.29    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 6.96/1.29    inference(cnf_transformation,[],[f12])).
% 6.96/1.29  fof(f12,axiom,(
% 6.96/1.29    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 6.96/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 6.96/1.29  fof(f39,plain,(
% 6.96/1.29    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.96/1.29    inference(cnf_transformation,[],[f11])).
% 6.96/1.29  fof(f11,axiom,(
% 6.96/1.29    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.96/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 6.96/1.29  fof(f54,plain,(
% 6.96/1.29    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))) )),
% 6.96/1.29    inference(cnf_transformation,[],[f10])).
% 6.96/1.29  fof(f10,axiom,(
% 6.96/1.29    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 6.96/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).
% 6.96/1.29  fof(f69,plain,(
% 6.96/1.29    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 6.96/1.29    inference(cnf_transformation,[],[f35])).
% 6.96/1.29  fof(f35,plain,(
% 6.96/1.29    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 6.96/1.29    inference(nnf_transformation,[],[f24])).
% 6.96/1.29  fof(f24,plain,(
% 6.96/1.29    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9))),
% 6.96/1.29    inference(definition_folding,[],[f21,f23,f22])).
% 6.96/1.29  fof(f21,plain,(
% 6.96/1.29    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 6.96/1.29    inference(ennf_transformation,[],[f9])).
% 6.96/1.29  fof(f9,axiom,(
% 6.96/1.29    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 6.96/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).
% 6.96/1.29  fof(f1208,plain,(
% 6.96/1.29    spl5_14 | ~spl5_3),
% 6.96/1.29    inference(avatar_split_clause,[],[f1203,f108,f1205])).
% 6.96/1.29  fof(f1205,plain,(
% 6.96/1.29    spl5_14 <=> k1_xboole_0 = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),
% 6.96/1.29    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 6.96/1.29  fof(f1203,plain,(
% 6.96/1.29    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) | ~spl5_3),
% 6.96/1.29    inference(forward_demodulation,[],[f1183,f116])).
% 6.96/1.29  fof(f1183,plain,(
% 6.96/1.29    k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_3),
% 6.96/1.29    inference(superposition,[],[f1110,f110])).
% 6.96/1.29  fof(f1146,plain,(
% 6.96/1.29    spl5_13 | ~spl5_3),
% 6.96/1.29    inference(avatar_split_clause,[],[f1115,f108,f1143])).
% 6.96/1.29  fof(f1143,plain,(
% 6.96/1.29    spl5_13 <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 6.96/1.29    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 6.96/1.29  fof(f1115,plain,(
% 6.96/1.29    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_3),
% 6.96/1.29    inference(superposition,[],[f975,f110])).
% 6.96/1.29  fof(f1008,plain,(
% 6.96/1.29    spl5_12 | ~spl5_3),
% 6.96/1.29    inference(avatar_split_clause,[],[f1003,f108,f1005])).
% 6.96/1.29  fof(f1005,plain,(
% 6.96/1.29    spl5_12 <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 6.96/1.29    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 6.96/1.29  fof(f1003,plain,(
% 6.96/1.29    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | ~spl5_3),
% 6.96/1.29    inference(forward_demodulation,[],[f970,f49])).
% 6.96/1.29  fof(f970,plain,(
% 6.96/1.29    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | ~spl5_3),
% 6.96/1.29    inference(superposition,[],[f392,f110])).
% 6.96/1.29  fof(f478,plain,(
% 6.96/1.29    spl5_11 | ~spl5_3),
% 6.96/1.29    inference(avatar_split_clause,[],[f456,f108,f475])).
% 6.96/1.29  fof(f475,plain,(
% 6.96/1.29    spl5_11 <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 6.96/1.29    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 6.96/1.29  fof(f456,plain,(
% 6.96/1.29    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_3),
% 6.96/1.29    inference(superposition,[],[f136,f110])).
% 6.96/1.29  fof(f416,plain,(
% 6.96/1.29    ~spl5_10 | spl5_5),
% 6.96/1.29    inference(avatar_split_clause,[],[f411,f281,f413])).
% 6.96/1.29  fof(f413,plain,(
% 6.96/1.29    spl5_10 <=> r2_hidden(sK2,k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),
% 6.96/1.29    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 6.96/1.29  fof(f281,plain,(
% 6.96/1.29    spl5_5 <=> sP0(sK2,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 6.96/1.29    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 6.96/1.29  fof(f411,plain,(
% 6.96/1.29    ~r2_hidden(sK2,k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) | spl5_5),
% 6.96/1.29    inference(forward_demodulation,[],[f410,f209])).
% 6.96/1.29  fof(f410,plain,(
% 6.96/1.29    ~r2_hidden(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) | spl5_5),
% 6.96/1.29    inference(forward_demodulation,[],[f409,f120])).
% 6.96/1.29  fof(f409,plain,(
% 6.96/1.29    ~r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) | spl5_5),
% 6.96/1.29    inference(unit_resulting_resolution,[],[f95,f283,f55])).
% 6.96/1.29  fof(f55,plain,(
% 6.96/1.29    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (~r2_hidden(X11,X9) | sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 6.96/1.29    inference(cnf_transformation,[],[f31])).
% 6.96/1.29  fof(f283,plain,(
% 6.96/1.29    ~sP0(sK2,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | spl5_5),
% 6.96/1.29    inference(avatar_component_clause,[],[f281])).
% 6.96/1.29  fof(f408,plain,(
% 6.96/1.29    ~spl5_9 | spl5_4),
% 6.96/1.29    inference(avatar_split_clause,[],[f403,f276,f405])).
% 6.96/1.29  fof(f405,plain,(
% 6.96/1.29    spl5_9 <=> r2_hidden(sK3,k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),
% 6.96/1.29    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 6.96/1.29  fof(f276,plain,(
% 6.96/1.29    spl5_4 <=> sP0(sK3,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 6.96/1.29    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 6.96/1.29  fof(f403,plain,(
% 6.96/1.29    ~r2_hidden(sK3,k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | spl5_4),
% 6.96/1.29    inference(forward_demodulation,[],[f402,f209])).
% 6.96/1.29  fof(f402,plain,(
% 6.96/1.29    ~r2_hidden(sK3,k5_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | spl5_4),
% 6.96/1.29    inference(forward_demodulation,[],[f401,f120])).
% 6.96/1.29  fof(f401,plain,(
% 6.96/1.29    ~r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) | spl5_4),
% 6.96/1.29    inference(unit_resulting_resolution,[],[f95,f278,f55])).
% 6.96/1.29  fof(f278,plain,(
% 6.96/1.29    ~sP0(sK3,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | spl5_4),
% 6.96/1.29    inference(avatar_component_clause,[],[f276])).
% 6.96/1.29  fof(f382,plain,(
% 6.96/1.29    spl5_8 | ~spl5_3),
% 6.96/1.29    inference(avatar_split_clause,[],[f377,f108,f379])).
% 6.96/1.29  fof(f379,plain,(
% 6.96/1.29    spl5_8 <=> k1_xboole_0 = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 6.96/1.29    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 6.96/1.29  fof(f377,plain,(
% 6.96/1.29    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | ~spl5_3),
% 6.96/1.29    inference(forward_demodulation,[],[f349,f49])).
% 6.96/1.29  fof(f349,plain,(
% 6.96/1.29    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | ~spl5_3),
% 6.96/1.29    inference(superposition,[],[f123,f110])).
% 6.96/1.29  fof(f318,plain,(
% 6.96/1.29    spl5_7 | ~spl5_3),
% 6.96/1.29    inference(avatar_split_clause,[],[f313,f108,f315])).
% 6.96/1.29  fof(f315,plain,(
% 6.96/1.29    spl5_7 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))),
% 6.96/1.29    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 6.96/1.29  fof(f313,plain,(
% 6.96/1.29    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) | ~spl5_3),
% 6.96/1.29    inference(forward_demodulation,[],[f306,f116])).
% 6.96/1.29  fof(f306,plain,(
% 6.96/1.29    k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_3),
% 6.96/1.29    inference(superposition,[],[f120,f110])).
% 6.96/1.29  fof(f312,plain,(
% 6.96/1.29    spl5_6 | ~spl5_3),
% 6.96/1.29    inference(avatar_split_clause,[],[f305,f108,f309])).
% 6.96/1.29  fof(f309,plain,(
% 6.96/1.29    spl5_6 <=> r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 6.96/1.29    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 6.96/1.29  fof(f305,plain,(
% 6.96/1.29    r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_3),
% 6.96/1.29    inference(superposition,[],[f112,f110])).
% 6.96/1.29  fof(f284,plain,(
% 6.96/1.29    ~spl5_5 | spl5_1),
% 6.96/1.29    inference(avatar_split_clause,[],[f246,f97,f281])).
% 6.96/1.29  fof(f97,plain,(
% 6.96/1.29    spl5_1 <=> sK2 = sK3),
% 6.96/1.29    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 6.96/1.29  fof(f246,plain,(
% 6.96/1.29    ~sP0(sK2,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | spl5_1),
% 6.96/1.29    inference(unit_resulting_resolution,[],[f99,f99,f99,f99,f99,f99,f99,f99,f99,f59])).
% 6.96/1.29  fof(f59,plain,(
% 6.96/1.29    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | X0 = X1) )),
% 6.96/1.29    inference(cnf_transformation,[],[f34])).
% 6.96/1.29  fof(f99,plain,(
% 6.96/1.29    sK2 != sK3 | spl5_1),
% 6.96/1.29    inference(avatar_component_clause,[],[f97])).
% 6.96/1.29  fof(f279,plain,(
% 6.96/1.29    ~spl5_4 | spl5_1),
% 6.96/1.29    inference(avatar_split_clause,[],[f247,f97,f276])).
% 6.96/1.29  fof(f247,plain,(
% 6.96/1.29    ~sP0(sK3,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | spl5_1),
% 6.96/1.29    inference(unit_resulting_resolution,[],[f99,f99,f99,f99,f99,f99,f99,f99,f99,f59])).
% 6.96/1.29  fof(f111,plain,(
% 6.96/1.29    spl5_3 | ~spl5_2),
% 6.96/1.29    inference(avatar_split_clause,[],[f106,f102,f108])).
% 6.96/1.29  fof(f102,plain,(
% 6.96/1.29    spl5_2 <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 6.96/1.29    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 6.96/1.29  fof(f106,plain,(
% 6.96/1.29    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) | ~spl5_2),
% 6.96/1.29    inference(forward_demodulation,[],[f104,f41])).
% 6.96/1.29  fof(f104,plain,(
% 6.96/1.29    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | ~spl5_2),
% 6.96/1.29    inference(avatar_component_clause,[],[f102])).
% 6.96/1.29  fof(f105,plain,(
% 6.96/1.29    spl5_2),
% 6.96/1.29    inference(avatar_split_clause,[],[f79,f102])).
% 6.96/1.29  fof(f79,plain,(
% 6.96/1.29    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 6.96/1.29    inference(definition_unfolding,[],[f36,f77,f71,f77,f77])).
% 6.96/1.29  fof(f36,plain,(
% 6.96/1.29    k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),
% 6.96/1.29    inference(cnf_transformation,[],[f26])).
% 6.96/1.29  fof(f26,plain,(
% 6.96/1.29    sK2 != sK3 & k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),
% 6.96/1.29    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f25])).
% 6.96/1.29  fof(f25,plain,(
% 6.96/1.29    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK2 != sK3 & k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),
% 6.96/1.29    introduced(choice_axiom,[])).
% 6.96/1.29  fof(f20,plain,(
% 6.96/1.29    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 6.96/1.29    inference(ennf_transformation,[],[f19])).
% 6.96/1.30  fof(f19,negated_conjecture,(
% 6.96/1.30    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 6.96/1.30    inference(negated_conjecture,[],[f18])).
% 6.96/1.30  fof(f18,conjecture,(
% 6.96/1.30    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 6.96/1.30    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 6.96/1.30  fof(f100,plain,(
% 6.96/1.30    ~spl5_1),
% 6.96/1.30    inference(avatar_split_clause,[],[f37,f97])).
% 6.96/1.30  fof(f37,plain,(
% 6.96/1.30    sK2 != sK3),
% 6.96/1.30    inference(cnf_transformation,[],[f26])).
% 6.96/1.30  % SZS output end Proof for theBenchmark
% 6.96/1.30  % (27044)------------------------------
% 6.96/1.30  % (27044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.96/1.30  % (27044)Termination reason: Refutation
% 6.96/1.30  
% 6.96/1.30  % (27044)Memory used [KB]: 4733
% 6.96/1.30  % (27044)Time elapsed: 0.652 s
% 6.96/1.30  % (27044)------------------------------
% 6.96/1.30  % (27044)------------------------------
% 7.26/1.30  % (27002)Success in time 0.928 s
%------------------------------------------------------------------------------
