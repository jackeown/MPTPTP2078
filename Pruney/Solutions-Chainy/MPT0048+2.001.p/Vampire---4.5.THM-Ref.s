%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 196 expanded)
%              Number of leaves         :   13 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  299 (1126 expanded)
%              Number of equality atoms :   35 ( 147 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f63,f91,f105,f120,f133,f149,f179,f180,f182,f185])).

fof(f185,plain,
    ( ~ spl6_3
    | spl6_5 ),
    inference(avatar_split_clause,[],[f174,f88,f59])).

fof(f59,plain,
    ( spl6_3
  <=> r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f88,plain,
    ( spl6_5
  <=> r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f174,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | spl6_5 ),
    inference(resolution,[],[f89,f31])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f89,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f182,plain,
    ( spl6_4
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f127,f50,f84])).

fof(f84,plain,
    ( spl6_4
  <=> r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f50,plain,
    ( spl6_1
  <=> r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f127,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f52,f36])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).

fof(f16,plain,(
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

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f52,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f180,plain,
    ( ~ spl6_4
    | spl6_6
    | spl6_2 ),
    inference(avatar_split_clause,[],[f157,f54,f117,f84])).

fof(f117,plain,
    ( spl6_6
  <=> r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f54,plain,
    ( spl6_2
  <=> r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f157,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | spl6_2 ),
    inference(resolution,[],[f55,f34])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f179,plain,
    ( ~ spl6_6
    | spl6_5 ),
    inference(avatar_split_clause,[],[f173,f88,f117])).

fof(f173,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | spl6_5 ),
    inference(resolution,[],[f89,f32])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f149,plain,
    ( ~ spl6_2
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(resolution,[],[f119,f71])).

fof(f71,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f56,f35])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f119,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f133,plain,
    ( ~ spl6_5
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f128,f50,f88])).

fof(f128,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl6_1 ),
    inference(resolution,[],[f52,f35])).

fof(f120,plain,
    ( spl6_6
    | spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f111,f88,f59,f117])).

fof(f111,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f90,f33])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f90,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f105,plain,
    ( ~ spl6_2
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | ~ spl6_2
    | spl6_4 ),
    inference(resolution,[],[f86,f70])).

fof(f70,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f56,f36])).

fof(f86,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f91,plain,
    ( ~ spl6_4
    | spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f78,f50,f88,f84])).

fof(f78,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | spl6_1 ),
    inference(resolution,[],[f51,f34])).

fof(f51,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f63,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f48,f59,f54,f50])).

fof(f48,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f38,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f30,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ~ sQ5_eqProxy(k4_xboole_0(k4_xboole_0(sK0,sK1),sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(equality_proxy_replacement,[],[f18,f37])).

fof(f18,plain,(
    k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) != k4_xboole_0(X0,k2_xboole_0(X1,X2))
   => k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) != k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f62,plain,
    ( spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f47,f59,f50])).

fof(f47,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f38,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k4_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f29,f37])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f46,f54,f50])).

fof(f46,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f38,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f28,f37])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:20:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (27046)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (27046)Refutation not found, incomplete strategy% (27046)------------------------------
% 0.21/0.47  % (27046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (27046)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (27046)Memory used [KB]: 10618
% 0.21/0.47  % (27046)Time elapsed: 0.007 s
% 0.21/0.47  % (27046)------------------------------
% 0.21/0.47  % (27046)------------------------------
% 0.21/0.47  % (27036)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (27045)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (27045)Refutation not found, incomplete strategy% (27045)------------------------------
% 0.21/0.49  % (27045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (27045)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (27045)Memory used [KB]: 1535
% 0.21/0.49  % (27045)Time elapsed: 0.069 s
% 0.21/0.49  % (27045)------------------------------
% 0.21/0.49  % (27045)------------------------------
% 0.21/0.51  % (27050)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.53  % (27047)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.53  % (27047)Refutation not found, incomplete strategy% (27047)------------------------------
% 0.21/0.53  % (27047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27047)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27047)Memory used [KB]: 6012
% 0.21/0.53  % (27047)Time elapsed: 0.083 s
% 0.21/0.53  % (27047)------------------------------
% 0.21/0.53  % (27047)------------------------------
% 0.21/0.54  % (27033)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (27033)Refutation not found, incomplete strategy% (27033)------------------------------
% 0.21/0.54  % (27033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27033)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27033)Memory used [KB]: 10490
% 0.21/0.54  % (27033)Time elapsed: 0.101 s
% 0.21/0.54  % (27033)------------------------------
% 0.21/0.54  % (27033)------------------------------
% 0.21/0.54  % (27034)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.54  % (27040)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.55  % (27037)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.55  % (27039)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.56  % (27048)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.56  % (27035)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.57  % (27035)Refutation not found, incomplete strategy% (27035)------------------------------
% 0.21/0.57  % (27035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (27035)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (27035)Memory used [KB]: 10490
% 0.21/0.57  % (27035)Time elapsed: 0.120 s
% 0.21/0.57  % (27035)------------------------------
% 0.21/0.57  % (27035)------------------------------
% 0.21/0.57  % (27032)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.57  % (27051)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.57  % (27042)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.57  % (27041)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.57  % (27044)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.58  % (27044)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f186,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f57,f62,f63,f91,f105,f120,f133,f149,f179,f180,f182,f185])).
% 0.21/0.58  fof(f185,plain,(
% 0.21/0.58    ~spl6_3 | spl6_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f174,f88,f59])).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    spl6_3 <=> r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.58  fof(f88,plain,(
% 0.21/0.58    spl6_5 <=> r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.58  fof(f174,plain,(
% 0.21/0.58    ~r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2) | spl6_5),
% 0.21/0.58    inference(resolution,[],[f89,f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.21/0.58    inference(equality_resolution,[],[f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.58    inference(cnf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).
% 0.21/0.58  fof(f11,plain,(
% 0.21/0.58    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f10,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.58    inference(rectify,[],[f9])).
% 0.21/0.58  fof(f9,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.58    inference(flattening,[],[f8])).
% 0.21/0.58  fof(f8,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.58    inference(nnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.58  fof(f89,plain,(
% 0.21/0.58    ~r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2)) | spl6_5),
% 0.21/0.58    inference(avatar_component_clause,[],[f88])).
% 0.21/0.58  fof(f182,plain,(
% 0.21/0.58    spl6_4 | ~spl6_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f127,f50,f84])).
% 0.21/0.58  fof(f84,plain,(
% 0.21/0.58    spl6_4 <=> r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    spl6_1 <=> r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.58  fof(f127,plain,(
% 0.21/0.58    r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) | ~spl6_1),
% 0.21/0.58    inference(resolution,[],[f52,f36])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(equality_resolution,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).
% 0.21/0.58  fof(f16,plain,(
% 0.21/0.58    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f15,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.58    inference(rectify,[],[f14])).
% 0.21/0.58  fof(f14,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.58    inference(flattening,[],[f13])).
% 0.21/0.58  fof(f13,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.58    inference(nnf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | ~spl6_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f50])).
% 0.21/0.58  fof(f180,plain,(
% 0.21/0.58    ~spl6_4 | spl6_6 | spl6_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f157,f54,f117,f84])).
% 0.21/0.58  fof(f117,plain,(
% 0.21/0.58    spl6_6 <=> r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    spl6_2 <=> r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.58  fof(f157,plain,(
% 0.21/0.58    r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) | ~r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) | spl6_2),
% 0.21/0.58    inference(resolution,[],[f55,f34])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.21/0.58    inference(equality_resolution,[],[f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    ~r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1)) | spl6_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f54])).
% 0.21/0.58  fof(f179,plain,(
% 0.21/0.58    ~spl6_6 | spl6_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f173,f88,f117])).
% 0.21/0.58  fof(f173,plain,(
% 0.21/0.58    ~r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) | spl6_5),
% 0.21/0.58    inference(resolution,[],[f89,f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.21/0.58    inference(equality_resolution,[],[f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.58    inference(cnf_transformation,[],[f12])).
% 0.21/0.58  fof(f149,plain,(
% 0.21/0.58    ~spl6_2 | ~spl6_6),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f144])).
% 0.21/0.58  fof(f144,plain,(
% 0.21/0.58    $false | (~spl6_2 | ~spl6_6)),
% 0.21/0.58    inference(resolution,[],[f119,f71])).
% 0.21/0.58  fof(f71,plain,(
% 0.21/0.58    ~r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) | ~spl6_2),
% 0.21/0.58    inference(resolution,[],[f56,f35])).
% 1.74/0.58  fof(f35,plain,(
% 1.74/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.74/0.58    inference(equality_resolution,[],[f26])).
% 1.74/0.58  fof(f26,plain,(
% 1.74/0.58    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.74/0.58    inference(cnf_transformation,[],[f17])).
% 1.74/0.58  fof(f56,plain,(
% 1.74/0.58    r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1)) | ~spl6_2),
% 1.74/0.58    inference(avatar_component_clause,[],[f54])).
% 1.74/0.58  fof(f119,plain,(
% 1.74/0.58    r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) | ~spl6_6),
% 1.74/0.58    inference(avatar_component_clause,[],[f117])).
% 1.74/0.58  fof(f133,plain,(
% 1.74/0.58    ~spl6_5 | ~spl6_1),
% 1.74/0.58    inference(avatar_split_clause,[],[f128,f50,f88])).
% 1.74/0.58  fof(f128,plain,(
% 1.74/0.58    ~r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2)) | ~spl6_1),
% 1.74/0.58    inference(resolution,[],[f52,f35])).
% 1.74/0.58  fof(f120,plain,(
% 1.74/0.58    spl6_6 | spl6_3 | ~spl6_5),
% 1.74/0.58    inference(avatar_split_clause,[],[f111,f88,f59,f117])).
% 1.74/0.58  fof(f111,plain,(
% 1.74/0.58    r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2) | r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) | ~spl6_5),
% 1.74/0.58    inference(resolution,[],[f90,f33])).
% 1.74/0.58  fof(f33,plain,(
% 1.74/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 1.74/0.58    inference(equality_resolution,[],[f19])).
% 1.74/0.58  fof(f19,plain,(
% 1.74/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.74/0.58    inference(cnf_transformation,[],[f12])).
% 1.74/0.58  fof(f90,plain,(
% 1.74/0.58    r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2)) | ~spl6_5),
% 1.74/0.58    inference(avatar_component_clause,[],[f88])).
% 1.74/0.58  fof(f105,plain,(
% 1.74/0.58    ~spl6_2 | spl6_4),
% 1.74/0.58    inference(avatar_contradiction_clause,[],[f100])).
% 1.74/0.58  fof(f100,plain,(
% 1.74/0.58    $false | (~spl6_2 | spl6_4)),
% 1.74/0.58    inference(resolution,[],[f86,f70])).
% 1.74/0.58  fof(f70,plain,(
% 1.74/0.58    r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) | ~spl6_2),
% 1.74/0.58    inference(resolution,[],[f56,f36])).
% 1.74/0.58  fof(f86,plain,(
% 1.74/0.58    ~r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) | spl6_4),
% 1.74/0.58    inference(avatar_component_clause,[],[f84])).
% 1.74/0.58  fof(f91,plain,(
% 1.74/0.58    ~spl6_4 | spl6_5 | spl6_1),
% 1.74/0.58    inference(avatar_split_clause,[],[f78,f50,f88,f84])).
% 1.74/0.58  fof(f78,plain,(
% 1.74/0.58    r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2)) | ~r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) | spl6_1),
% 1.74/0.58    inference(resolution,[],[f51,f34])).
% 1.74/0.58  fof(f51,plain,(
% 1.74/0.58    ~r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | spl6_1),
% 1.74/0.58    inference(avatar_component_clause,[],[f50])).
% 1.74/0.58  fof(f63,plain,(
% 1.74/0.58    ~spl6_1 | ~spl6_2 | spl6_3),
% 1.74/0.58    inference(avatar_split_clause,[],[f48,f59,f54,f50])).
% 1.74/0.58  fof(f48,plain,(
% 1.74/0.58    r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2) | ~r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 1.74/0.58    inference(resolution,[],[f38,f42])).
% 1.74/0.58  fof(f42,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (sQ5_eqProxy(k4_xboole_0(X0,X1),X2) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.74/0.58    inference(equality_proxy_replacement,[],[f30,f37])).
% 1.74/0.58  fof(f37,plain,(
% 1.74/0.58    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 1.74/0.58    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 1.74/0.58  fof(f30,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f17])).
% 1.74/0.58  fof(f38,plain,(
% 1.74/0.58    ~sQ5_eqProxy(k4_xboole_0(k4_xboole_0(sK0,sK1),sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 1.74/0.58    inference(equality_proxy_replacement,[],[f18,f37])).
% 1.74/0.58  fof(f18,plain,(
% 1.74/0.58    k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.74/0.58    inference(cnf_transformation,[],[f7])).
% 1.74/0.58  fof(f7,plain,(
% 1.74/0.58    k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.74/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).
% 1.74/0.58  fof(f6,plain,(
% 1.74/0.58    ? [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) != k4_xboole_0(X0,k2_xboole_0(X1,X2)) => k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.74/0.58    introduced(choice_axiom,[])).
% 1.74/0.58  fof(f5,plain,(
% 1.74/0.58    ? [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) != k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.74/0.58    inference(ennf_transformation,[],[f4])).
% 1.74/0.58  fof(f4,negated_conjecture,(
% 1.74/0.58    ~! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.74/0.58    inference(negated_conjecture,[],[f3])).
% 1.74/0.58  fof(f3,conjecture,(
% 1.74/0.58    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.74/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.74/0.58  fof(f62,plain,(
% 1.74/0.58    spl6_1 | ~spl6_3),
% 1.74/0.58    inference(avatar_split_clause,[],[f47,f59,f50])).
% 1.74/0.58  fof(f47,plain,(
% 1.74/0.58    ~r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2) | r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 1.74/0.58    inference(resolution,[],[f38,f43])).
% 1.74/0.58  fof(f43,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (sQ5_eqProxy(k4_xboole_0(X0,X1),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.74/0.58    inference(equality_proxy_replacement,[],[f29,f37])).
% 1.74/0.58  fof(f29,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f17])).
% 1.74/0.58  fof(f57,plain,(
% 1.74/0.58    spl6_1 | spl6_2),
% 1.74/0.58    inference(avatar_split_clause,[],[f46,f54,f50])).
% 1.74/0.58  fof(f46,plain,(
% 1.74/0.58    r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1)) | r2_hidden(sK4(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 1.74/0.58    inference(resolution,[],[f38,f44])).
% 1.74/0.58  fof(f44,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (sQ5_eqProxy(k4_xboole_0(X0,X1),X2) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.74/0.58    inference(equality_proxy_replacement,[],[f28,f37])).
% 1.74/0.58  fof(f28,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f17])).
% 1.74/0.58  % SZS output end Proof for theBenchmark
% 1.74/0.58  % (27044)------------------------------
% 1.74/0.58  % (27044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.58  % (27044)Termination reason: Refutation
% 1.74/0.58  
% 1.74/0.58  % (27044)Memory used [KB]: 6140
% 1.74/0.58  % (27044)Time elapsed: 0.136 s
% 1.74/0.58  % (27044)------------------------------
% 1.74/0.58  % (27044)------------------------------
% 1.74/0.58  % (27029)Success in time 0.215 s
%------------------------------------------------------------------------------
