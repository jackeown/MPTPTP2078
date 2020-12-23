%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0684+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 355 expanded)
%              Number of leaves         :   22 ( 124 expanded)
%              Depth                    :   11
%              Number of atoms          :  480 (1962 expanded)
%              Number of equality atoms :   43 ( 266 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f449,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f104,f105,f106,f108,f113,f115,f129,f287,f292,f293,f298,f299,f336,f345,f444,f446,f448])).

fof(f448,plain,
    ( ~ spl6_17
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f200,f117,f295])).

fof(f295,plain,
    ( spl6_17
  <=> r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f117,plain,
    ( spl6_9
  <=> r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f200,plain,
    ( ~ r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_9 ),
    inference(resolution,[],[f119,f48])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f119,plain,
    ( r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f446,plain,
    ( ~ spl6_21
    | spl6_20
    | spl6_11 ),
    inference(avatar_split_clause,[],[f348,f126,f332,f340])).

fof(f340,plain,
    ( spl6_21
  <=> r2_hidden(k1_funct_1(sK2,sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f332,plain,
    ( spl6_20
  <=> r2_hidden(k1_funct_1(sK2,sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f126,plain,
    ( spl6_11
  <=> r2_hidden(k1_funct_1(sK2,sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f348,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ r2_hidden(k1_funct_1(sK2,sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | spl6_11 ),
    inference(resolution,[],[f127,f47])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k6_subset_1(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f34,f31])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f127,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k6_subset_1(sK0,sK1))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f444,plain,
    ( ~ spl6_20
    | ~ spl6_10
    | ~ spl6_4
    | spl6_17 ),
    inference(avatar_split_clause,[],[f436,f295,f78,f121,f332])).

fof(f121,plain,
    ( spl6_10
  <=> r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f78,plain,
    ( spl6_4
  <=> ! [X5,X4] :
        ( r2_hidden(X4,k10_relat_1(sK2,X5))
        | ~ r2_hidden(X4,k1_relat_1(sK2))
        | ~ r2_hidden(k1_funct_1(sK2,X4),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f436,plain,
    ( ~ r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ spl6_4
    | spl6_17 ),
    inference(resolution,[],[f297,f79])).

fof(f79,plain,
    ( ! [X4,X5] :
        ( r2_hidden(X4,k10_relat_1(sK2,X5))
        | ~ r2_hidden(X4,k1_relat_1(sK2))
        | ~ r2_hidden(k1_funct_1(sK2,X4),X5) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f297,plain,
    ( ~ r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f295])).

fof(f345,plain,
    ( spl6_21
    | ~ spl6_3
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f198,f117,f74,f340])).

fof(f74,plain,
    ( spl6_3
  <=> ! [X3,X2] :
        ( r2_hidden(k1_funct_1(sK2,X2),X3)
        | ~ r2_hidden(X2,k10_relat_1(sK2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f198,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl6_3
    | ~ spl6_9 ),
    inference(resolution,[],[f119,f151])).

fof(f151,plain,
    ( ! [X14,X15,X16] :
        ( ~ r2_hidden(X14,k6_subset_1(k10_relat_1(sK2,X15),X16))
        | r2_hidden(k1_funct_1(sK2,X14),X15) )
    | ~ spl6_3 ),
    inference(resolution,[],[f75,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k10_relat_1(sK2,X3))
        | r2_hidden(k1_funct_1(sK2,X2),X3) )
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f336,plain,
    ( ~ spl6_16
    | spl6_17
    | spl6_9 ),
    inference(avatar_split_clause,[],[f328,f117,f295,f289])).

fof(f289,plain,
    ( spl6_16
  <=> r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f328,plain,
    ( r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | spl6_9 ),
    inference(resolution,[],[f118,f47])).

fof(f118,plain,
    ( ~ r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f299,plain,
    ( ~ spl6_11
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f203,f90,f117,f121,f126])).

fof(f90,plain,
    ( spl6_7
  <=> ! [X11,X10] :
        ( sQ5_eqProxy(k10_relat_1(sK2,X10),X11)
        | ~ r2_hidden(sK3(sK2,X10,X11),X11)
        | ~ r2_hidden(sK3(sK2,X10,X11),k1_relat_1(sK2))
        | ~ r2_hidden(k1_funct_1(sK2,sK3(sK2,X10,X11)),X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f203,plain,
    ( ~ r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k6_subset_1(sK0,sK1))
    | ~ spl6_7 ),
    inference(resolution,[],[f91,f51])).

fof(f51,plain,(
    ~ sQ5_eqProxy(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    inference(equality_proxy_replacement,[],[f24,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f24,plain,(
    k10_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k10_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k10_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k10_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f91,plain,
    ( ! [X10,X11] :
        ( sQ5_eqProxy(k10_relat_1(sK2,X10),X11)
        | ~ r2_hidden(sK3(sK2,X10,X11),X11)
        | ~ r2_hidden(sK3(sK2,X10,X11),k1_relat_1(sK2))
        | ~ r2_hidden(k1_funct_1(sK2,sK3(sK2,X10,X11)),X10) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f298,plain,
    ( ~ spl6_8
    | ~ spl6_1
    | ~ spl6_17
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f278,f126,f295,f66,f100])).

fof(f100,plain,
    ( spl6_8
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f66,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f278,plain,
    ( ~ r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_11 ),
    inference(resolution,[],[f186,f45])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).

fof(f15,plain,(
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

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

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
    inference(flattening,[],[f12])).

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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(f186,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ spl6_11 ),
    inference(resolution,[],[f128,f48])).

fof(f128,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k6_subset_1(sK0,sK1))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f293,plain,
    ( spl6_10
    | spl6_9
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f182,f82,f117,f121])).

fof(f82,plain,
    ( spl6_5
  <=> ! [X7,X6] :
        ( sQ5_eqProxy(k10_relat_1(sK2,X6),X7)
        | r2_hidden(sK3(sK2,X6,X7),X7)
        | r2_hidden(sK3(sK2,X6,X7),k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f182,plain,
    ( r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ spl6_5 ),
    inference(resolution,[],[f83,f51])).

fof(f83,plain,
    ( ! [X6,X7] :
        ( sQ5_eqProxy(k10_relat_1(sK2,X6),X7)
        | r2_hidden(sK3(sK2,X6,X7),X7)
        | r2_hidden(sK3(sK2,X6,X7),k1_relat_1(sK2)) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f292,plain,
    ( ~ spl6_8
    | ~ spl6_1
    | ~ spl6_10
    | spl6_16
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f267,f126,f289,f121,f66,f100])).

fof(f267,plain,
    ( r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_11 ),
    inference(resolution,[],[f185,f44])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f185,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl6_11 ),
    inference(resolution,[],[f128,f49])).

fof(f287,plain,
    ( ~ spl6_2
    | ~ spl6_9
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_9
    | spl6_10 ),
    inference(resolution,[],[f199,f178])).

fof(f178,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,X0))
    | ~ spl6_2
    | spl6_10 ),
    inference(resolution,[],[f122,f71])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k10_relat_1(sK2,X1)) )
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl6_2
  <=> ! [X1,X0] :
        ( r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k10_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f122,plain,
    ( ~ r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f199,plain,
    ( r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_9 ),
    inference(resolution,[],[f119,f49])).

fof(f129,plain,
    ( ~ spl6_8
    | ~ spl6_1
    | spl6_9
    | spl6_11 ),
    inference(avatar_split_clause,[],[f110,f126,f117,f66,f100])).

fof(f110,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k6_subset_1(sK0,sK1))
    | r2_hidden(sK3(sK2,k6_subset_1(sK0,sK1),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f51,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k10_relat_1(X0,X1),X2)
      | r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f29,f50])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f115,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl6_8 ),
    inference(resolution,[],[f102,f22])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f102,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f113,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl6_1 ),
    inference(resolution,[],[f68,f23])).

fof(f23,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f68,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f108,plain,
    ( ~ spl6_8
    | spl6_7 ),
    inference(avatar_split_clause,[],[f98,f90,f100])).

fof(f98,plain,(
    ! [X10,X11] :
      ( sQ5_eqProxy(k10_relat_1(sK2,X10),X11)
      | ~ r2_hidden(k1_funct_1(sK2,sK3(sK2,X10,X11)),X10)
      | ~ r2_hidden(sK3(sK2,X10,X11),k1_relat_1(sK2))
      | ~ r2_hidden(sK3(sK2,X10,X11),X11)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f23,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k10_relat_1(X0,X1),X2)
      | ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f30,f50])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f106,plain,
    ( ~ spl6_8
    | spl6_5 ),
    inference(avatar_split_clause,[],[f96,f82,f100])).

fof(f96,plain,(
    ! [X6,X7] :
      ( sQ5_eqProxy(k10_relat_1(sK2,X6),X7)
      | r2_hidden(sK3(sK2,X6,X7),k1_relat_1(sK2))
      | r2_hidden(sK3(sK2,X6,X7),X7)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f23,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k10_relat_1(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f28,f50])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f105,plain,
    ( ~ spl6_8
    | spl6_4 ),
    inference(avatar_split_clause,[],[f95,f78,f100])).

fof(f95,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,k10_relat_1(sK2,X5))
      | ~ r2_hidden(k1_funct_1(sK2,X4),X5)
      | ~ r2_hidden(X4,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f23,f44])).

fof(f104,plain,
    ( ~ spl6_8
    | spl6_3 ),
    inference(avatar_split_clause,[],[f94,f74,f100])).

fof(f94,plain,(
    ! [X2,X3] :
      ( r2_hidden(k1_funct_1(sK2,X2),X3)
      | ~ r2_hidden(X2,k10_relat_1(sK2,X3))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f23,f45])).

fof(f103,plain,
    ( ~ spl6_8
    | spl6_2 ),
    inference(avatar_split_clause,[],[f93,f70,f100])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(sK2))
      | ~ r2_hidden(X0,k10_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f23,f46])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
