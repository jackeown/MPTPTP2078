%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0510+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:34 EST 2020

% Result     : Theorem 41.40s
% Output     : Refutation 41.40s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 366 expanded)
%              Number of leaves         :   16 ( 107 expanded)
%              Depth                    :   16
%              Number of atoms          :  468 (1965 expanded)
%              Number of equality atoms :   36 ( 265 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23715,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f6490,f6516,f13095,f13137,f13176,f13204,f23223,f23647,f23671,f23710,f23714])).

fof(f23714,plain,
    ( ~ spl151_9
    | spl151_13 ),
    inference(avatar_contradiction_clause,[],[f23713])).

fof(f23713,plain,
    ( $false
    | ~ spl151_9
    | spl151_13 ),
    inference(unit_resulting_resolution,[],[f6489,f13094,f3007])).

fof(f3007,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f2558])).

fof(f2558,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1628])).

fof(f1628,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK123(X0,X1,X2),X1)
            | ~ r2_hidden(sK123(X0,X1,X2),X0)
            | ~ r2_hidden(sK123(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK123(X0,X1,X2),X1)
              & r2_hidden(sK123(X0,X1,X2),X0) )
            | r2_hidden(sK123(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK123])],[f1626,f1627])).

fof(f1627,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK123(X0,X1,X2),X1)
          | ~ r2_hidden(sK123(X0,X1,X2),X0)
          | ~ r2_hidden(sK123(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK123(X0,X1,X2),X1)
            & r2_hidden(sK123(X0,X1,X2),X0) )
          | r2_hidden(sK123(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1626,plain,(
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
    inference(rectify,[],[f1625])).

fof(f1625,plain,(
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
    inference(flattening,[],[f1624])).

fof(f1624,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f13094,plain,
    ( ~ r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK4)
    | spl151_13 ),
    inference(avatar_component_clause,[],[f13092])).

fof(f13092,plain,
    ( spl151_13
  <=> r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl151_13])])).

fof(f6489,plain,
    ( r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),k3_xboole_0(sK3,sK4))
    | ~ spl151_9 ),
    inference(avatar_component_clause,[],[f6487])).

fof(f6487,plain,
    ( spl151_9
  <=> r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),k3_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl151_9])])).

fof(f23710,plain,
    ( ~ spl151_7
    | spl151_8
    | ~ spl151_13
    | spl151_17 ),
    inference(avatar_contradiction_clause,[],[f23709])).

fof(f23709,plain,
    ( $false
    | ~ spl151_7
    | spl151_8
    | ~ spl151_13
    | spl151_17 ),
    inference(subsumption_resolution,[],[f23708,f1739])).

fof(f1739,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f1329])).

fof(f1329,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f770,f1328])).

fof(f1328,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f770,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f683])).

fof(f683,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f682])).

fof(f682,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).

fof(f23708,plain,
    ( ~ v1_relat_1(sK5)
    | ~ spl151_7
    | spl151_8
    | ~ spl151_13
    | spl151_17 ),
    inference(subsumption_resolution,[],[f23707,f13093])).

fof(f13093,plain,
    ( r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK4)
    | ~ spl151_13 ),
    inference(avatar_component_clause,[],[f13092])).

fof(f23707,plain,
    ( ~ r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK4)
    | ~ v1_relat_1(sK5)
    | ~ spl151_7
    | spl151_8
    | spl151_17 ),
    inference(subsumption_resolution,[],[f23704,f13251])).

fof(f13251,plain,
    ( r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),sK5)
    | ~ spl151_7
    | spl151_8 ),
    inference(subsumption_resolution,[],[f13207,f6484])).

fof(f6484,plain,
    ( ~ r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))
    | spl151_8 ),
    inference(avatar_component_clause,[],[f6483])).

fof(f6483,plain,
    ( spl151_8
  <=> r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl151_8])])).

fof(f13207,plain,
    ( r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),sK5)
    | r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))
    | ~ spl151_7 ),
    inference(subsumption_resolution,[],[f4027,f6480])).

fof(f6480,plain,
    ( v1_relat_1(k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))
    | ~ spl151_7 ),
    inference(avatar_component_clause,[],[f6479])).

fof(f6479,plain,
    ( spl151_7
  <=> v1_relat_1(k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl151_7])])).

fof(f4027,plain,
    ( r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),sK5)
    | r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))
    | ~ v1_relat_1(k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))) ),
    inference(subsumption_resolution,[],[f4026,f1739])).

fof(f4026,plain,
    ( r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),sK5)
    | r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))
    | ~ v1_relat_1(k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f3210,f3144])).

fof(f3144,plain,(
    ~ sQ150_eqProxy(k7_relat_1(sK5,k3_xboole_0(sK3,sK4)),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))) ),
    inference(equality_proxy_replacement,[],[f1740,f3126])).

fof(f3126,plain,(
    ! [X1,X0] :
      ( sQ150_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ150_eqProxy])])).

fof(f1740,plain,(
    k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)) ),
    inference(cnf_transformation,[],[f1329])).

fof(f3210,plain,(
    ! [X2,X0,X1] :
      ( sQ150_eqProxy(k7_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f1882,f3126])).

fof(f1882,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1363])).

fof(f1363,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK22(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X0)
                    & r2_hidden(sK22(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22,sK23])],[f1361,f1362])).

fof(f1362,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X0)
          | ~ r2_hidden(sK22(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X0)
            & r2_hidden(sK22(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1361,plain,(
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
    inference(rectify,[],[f1360])).

fof(f1360,plain,(
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
    inference(flattening,[],[f1359])).

fof(f1359,plain,(
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
    inference(nnf_transformation,[],[f841])).

fof(f841,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f641])).

fof(f641,axiom,(
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

fof(f23704,plain,
    ( ~ r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),sK5)
    | ~ r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK4)
    | ~ v1_relat_1(sK5)
    | spl151_17 ),
    inference(resolution,[],[f23646,f4018])).

fof(f4018,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f2930,f2025])).

fof(f2025,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f879])).

fof(f879,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f2930,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1880])).

fof(f1880,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1363])).

fof(f23646,plain,
    ( ~ r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k7_relat_1(sK5,sK4))
    | spl151_17 ),
    inference(avatar_component_clause,[],[f23644])).

fof(f23644,plain,
    ( spl151_17
  <=> r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k7_relat_1(sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl151_17])])).

fof(f23671,plain,
    ( ~ spl151_7
    | spl151_8
    | ~ spl151_12
    | spl151_16 ),
    inference(avatar_contradiction_clause,[],[f23670])).

fof(f23670,plain,
    ( $false
    | ~ spl151_7
    | spl151_8
    | ~ spl151_12
    | spl151_16 ),
    inference(subsumption_resolution,[],[f23669,f1739])).

fof(f23669,plain,
    ( ~ v1_relat_1(sK5)
    | ~ spl151_7
    | spl151_8
    | ~ spl151_12
    | spl151_16 ),
    inference(subsumption_resolution,[],[f23668,f13089])).

fof(f13089,plain,
    ( r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK3)
    | ~ spl151_12 ),
    inference(avatar_component_clause,[],[f13088])).

fof(f13088,plain,
    ( spl151_12
  <=> r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl151_12])])).

fof(f23668,plain,
    ( ~ r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK3)
    | ~ v1_relat_1(sK5)
    | ~ spl151_7
    | spl151_8
    | spl151_16 ),
    inference(subsumption_resolution,[],[f23665,f13251])).

fof(f23665,plain,
    ( ~ r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),sK5)
    | ~ r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK3)
    | ~ v1_relat_1(sK5)
    | spl151_16 ),
    inference(resolution,[],[f23642,f4018])).

fof(f23642,plain,
    ( ~ r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k7_relat_1(sK5,sK3))
    | spl151_16 ),
    inference(avatar_component_clause,[],[f23640])).

fof(f23640,plain,
    ( spl151_16
  <=> r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k7_relat_1(sK5,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl151_16])])).

fof(f23647,plain,
    ( ~ spl151_16
    | ~ spl151_17
    | spl151_8 ),
    inference(avatar_split_clause,[],[f13221,f6483,f23644,f23640])).

fof(f13221,plain,
    ( ~ r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k7_relat_1(sK5,sK4))
    | ~ r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k7_relat_1(sK5,sK3))
    | spl151_8 ),
    inference(resolution,[],[f6484,f3006])).

fof(f3006,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f2559])).

fof(f2559,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1628])).

fof(f23223,plain,
    ( ~ spl151_9
    | spl151_12 ),
    inference(avatar_contradiction_clause,[],[f23220])).

fof(f23220,plain,
    ( $false
    | ~ spl151_9
    | spl151_12 ),
    inference(unit_resulting_resolution,[],[f6489,f13090,f3008])).

fof(f3008,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f2557])).

fof(f2557,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1628])).

fof(f13090,plain,
    ( ~ r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK3)
    | spl151_12 ),
    inference(avatar_component_clause,[],[f13088])).

fof(f13204,plain,
    ( ~ spl151_7
    | ~ spl151_8
    | ~ spl151_9 ),
    inference(avatar_contradiction_clause,[],[f13203])).

fof(f13203,plain,
    ( $false
    | ~ spl151_7
    | ~ spl151_8
    | ~ spl151_9 ),
    inference(unit_resulting_resolution,[],[f1739,f6522,f13202,f4017])).

fof(f4017,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f2931,f2025])).

fof(f2931,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1879])).

fof(f1879,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1363])).

fof(f13202,plain,
    ( ~ r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),sK5)
    | ~ spl151_7
    | ~ spl151_8
    | ~ spl151_9 ),
    inference(subsumption_resolution,[],[f13178,f6489])).

fof(f13178,plain,
    ( ~ r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),sK5)
    | ~ r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),k3_xboole_0(sK3,sK4))
    | ~ spl151_7
    | ~ spl151_8 ),
    inference(subsumption_resolution,[],[f13177,f6480])).

fof(f13177,plain,
    ( ~ r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),sK5)
    | ~ r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),k3_xboole_0(sK3,sK4))
    | ~ v1_relat_1(k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))
    | ~ spl151_8 ),
    inference(subsumption_resolution,[],[f4029,f6485])).

fof(f6485,plain,
    ( r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))
    | ~ spl151_8 ),
    inference(avatar_component_clause,[],[f6483])).

fof(f4029,plain,
    ( ~ r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),sK5)
    | ~ r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),k3_xboole_0(sK3,sK4))
    | ~ r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))
    | ~ v1_relat_1(k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))) ),
    inference(subsumption_resolution,[],[f4028,f1739])).

fof(f4028,plain,
    ( ~ r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),sK5)
    | ~ r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),k3_xboole_0(sK3,sK4))
    | ~ r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))
    | ~ v1_relat_1(k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f3209,f3144])).

fof(f3209,plain,(
    ! [X2,X0,X1] :
      ( sQ150_eqProxy(k7_relat_1(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X0)
      | ~ r2_hidden(sK22(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f1883,f3126])).

fof(f1883,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X0)
      | ~ r2_hidden(sK22(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1363])).

fof(f6522,plain,
    ( r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k7_relat_1(sK5,sK3))
    | ~ spl151_8 ),
    inference(resolution,[],[f6485,f3008])).

fof(f13176,plain,
    ( ~ spl151_8
    | spl151_13 ),
    inference(avatar_contradiction_clause,[],[f13175])).

fof(f13175,plain,
    ( $false
    | ~ spl151_8
    | spl151_13 ),
    inference(subsumption_resolution,[],[f13174,f1739])).

fof(f13174,plain,
    ( ~ v1_relat_1(sK5)
    | ~ spl151_8
    | spl151_13 ),
    inference(subsumption_resolution,[],[f13162,f13094])).

fof(f13162,plain,
    ( r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK4)
    | ~ v1_relat_1(sK5)
    | ~ spl151_8 ),
    inference(resolution,[],[f6523,f4016])).

fof(f4016,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(X5,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f2932,f2025])).

fof(f2932,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1878])).

fof(f1878,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1363])).

fof(f6523,plain,
    ( r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k7_relat_1(sK5,sK4))
    | ~ spl151_8 ),
    inference(resolution,[],[f6485,f3007])).

fof(f13137,plain,
    ( ~ spl151_8
    | spl151_12 ),
    inference(avatar_contradiction_clause,[],[f13136])).

fof(f13136,plain,
    ( $false
    | ~ spl151_8
    | spl151_12 ),
    inference(subsumption_resolution,[],[f13135,f1739])).

fof(f13135,plain,
    ( ~ v1_relat_1(sK5)
    | ~ spl151_8
    | spl151_12 ),
    inference(subsumption_resolution,[],[f13123,f13090])).

fof(f13123,plain,
    ( r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK3)
    | ~ v1_relat_1(sK5)
    | ~ spl151_8 ),
    inference(resolution,[],[f6522,f4016])).

fof(f13095,plain,
    ( ~ spl151_12
    | ~ spl151_13
    | spl151_9 ),
    inference(avatar_split_clause,[],[f6518,f6487,f13092,f13088])).

fof(f6518,plain,
    ( ~ r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK4)
    | ~ r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK3)
    | spl151_9 ),
    inference(resolution,[],[f6488,f3006])).

fof(f6488,plain,
    ( ~ r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),k3_xboole_0(sK3,sK4))
    | spl151_9 ),
    inference(avatar_component_clause,[],[f6487])).

fof(f6516,plain,(
    spl151_7 ),
    inference(avatar_contradiction_clause,[],[f6515])).

fof(f6515,plain,
    ( $false
    | spl151_7 ),
    inference(subsumption_resolution,[],[f6509,f1739])).

fof(f6509,plain,
    ( ~ v1_relat_1(sK5)
    | spl151_7 ),
    inference(resolution,[],[f6503,f2025])).

fof(f6503,plain,
    ( ~ v1_relat_1(k7_relat_1(sK5,sK3))
    | spl151_7 ),
    inference(resolution,[],[f6481,f2027])).

fof(f2027,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f881])).

fof(f881,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f664])).

fof(f664,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f6481,plain,
    ( ~ v1_relat_1(k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))
    | spl151_7 ),
    inference(avatar_component_clause,[],[f6479])).

fof(f6490,plain,
    ( ~ spl151_7
    | spl151_8
    | spl151_9 ),
    inference(avatar_split_clause,[],[f4025,f6487,f6483,f6479])).

fof(f4025,plain,
    ( r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),k3_xboole_0(sK3,sK4))
    | r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))
    | ~ v1_relat_1(k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))) ),
    inference(subsumption_resolution,[],[f4024,f1739])).

fof(f4024,plain,
    ( r2_hidden(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),k3_xboole_0(sK3,sK4))
    | r2_hidden(k4_tarski(sK22(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4))),sK23(sK5,k3_xboole_0(sK3,sK4),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))),k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))
    | ~ v1_relat_1(k3_xboole_0(k7_relat_1(sK5,sK3),k7_relat_1(sK5,sK4)))
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f3211,f3144])).

fof(f3211,plain,(
    ! [X2,X0,X1] :
      ( sQ150_eqProxy(k7_relat_1(X0,X1),X2)
      | r2_hidden(sK22(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f1881,f3126])).

fof(f1881,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(sK22(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1363])).
%------------------------------------------------------------------------------
